#lang racket
(require (only-in eopl sllgen:make-string-parser))
(provide eval-program run)

(struct binding (loc mutable?) #:transparent)
(struct closure (params body env) #:transparent)
(struct obj (fields proto) #:transparent)

(define (make-empty-store) (values (make-hasheq) 0))

(define location-watchers (make-hasheq))

(define (store-alloc store next v)
  (define loc next)
  (hash-set! store loc v)
  (values loc (add1 next)))

(define (store-ref store loc)
  (hash-ref store loc (λ () (error 'store-ref "loc no asignada: ~a" loc))))

(define (store-set! store loc v)
  (hash-set! store loc v)
  (when (hash-has-key? location-watchers loc)
    ((hash-ref location-watchers loc) v)))

(define (attach-location-watcher! loc proc)
  (hash-set! location-watchers loc proc))

;; Ambiente
(define empty-env (hash))

(define (env-lookup env name)
  (hash-ref env name (λ () (error 'lookup "variable no definida: ~a" name))))

(define (env-extend env name bind)
  (hash-set env name bind))

;; Helpers de tipos
(define (scalar? v)
  (or (number? v) (boolean? v) (string? v) (eq? v 'null)))

(define (listV? v)
  (and (list? v) (not (obj? v))))

(define (dictV? v)

(hash? v))

(define (objV? v)
  (obj? v))

(define (compound? v)
  (or (listV? v) (dictV? v) (objV? v)))

(define (type-of* v)
  (cond [(number? v) 'number]
        [(boolean? v) 'bool]
        [(string? v) 'string]
        [(eq? v 'null) 'null]
        [(closure? v) 'function]
        [(obj? v) 'object]
        [(hash? v) 'dict]
        [(pair? v) 'list]
        [else 'unknown]))

(define (truthy? v)
  (cond
    [(eq? v #f) #f]
    [(eq? v 'null) #f]
    [(and (number? v) (zero? v)) #f]
    [(and (string? v) (string=? v "")) #f]
    [else #t]))

(define (result v env store next)
  (values v env store next))

(define primitive-symbols
  '(+ - * / < <= > >= not and or equal? list-push!
    vacio? crear-lista lista? cabeza cola append ref-list set-list
    crear-diccionario diccionario? ref-diccionario set-diccionario
    claves valores
    longitud concatenar
    % // add1 sub1))

(define (primitive-symbol? sym)
  (memq sym primitive-symbols))

(define return-no-expr-tag '#:return-none)
(struct return-signal (value) #:transparent)

(define (make-binding-entry id expr) (list id expr))
(define (binding-id entry) (car entry))
(define (binding-expr entry) (cadr entry))

(define (eval-var-bindings bindings env store next)
  (let loop ((bs bindings) (e env) (s store) (n next))
    (if (null? bs)
        (result 'ok e s n)
        (let* ([entry (car bs)]
               [x (binding-id entry)]
               [expr (binding-expr entry)])
          (define-values (loc n1) (store-alloc s n 'null))
          (define env-with-var (env-extend e x (binding loc #t)))
          (define-values (v env1 s1 n2) (eval* expr env-with-var s n1))
          (store-set! s1 loc v)
          (loop (cdr bs) env1 s1 n2)))))

(define (eval-program ast)
  (define-values (S N) (make-empty-store))
  (define-values (v _e _S _N) (eval* ast empty-env S N))
  (if (return-signal? v) (return-signal-value v) v))

(define (run ast)
  (eval-program ast))

(define (eval-list es env store next)
  (let loop ((es es) (e env) (s store) (n next) (acc '()))
    (if (null? es) (values (reverse acc) e s n)
        (let-values ([(v e1 s1 n1) (eval* (car es) e s n)])
          (loop (cdr es) e1 s1 n1 (cons v acc))))))

(define (eval-seq es env store next new-scope?)
  (let seq ((es es) (e env) (s store) (n next) (last 'null))
    (if (null? es) (values last e s n)
        (let-values ([(v1 e1 s1 n1) (eval* (car es) e s n)])
          (if (return-signal? v1)
              (values v1 e1 s1 n1)
              (seq (cdr es) e1 s1 n1 v1))))))

(define (eval-seq-flat es env store next)
  (let seq ((es es) (e env) (s store) (n next) (last 'null))
    (if (null? es) (values last e s n)
        (let-values ([(v1 e1 s1 n1) (eval* (car es) e s n)])
          (if (return-signal? v1)
              (values v1 e1 s1 n1)
              (seq (cdr es) e1 s1 n1 v1))))))

(define (eval* ast env store next)
  (match ast
    [(list 'program es ...) (eval-seq es env store next #t)]
    [(list 'block es ...)   (eval-seq es env store next #f)]
    [(list 'begin es ...)   (eval-seq-flat es env store next)]

    [(list 'var* bindings)
     (eval-var-bindings bindings env store next)]

    [(list 'var (? symbol? x) e)
     (eval-var-bindings (list (make-binding-entry x e)) env store next)]

    [(? (λ (x) (and (symbol? x) (not (eq? x 'null)))) x)
     (if (primitive-symbol? x)
         (result x env store next)
         (let ([b (env-lookup env x)])
           (result (store-ref store (binding-loc b)) env store next)))]

    [(or (? number?) (? boolean?) (? string?) 'null)
     (result ast env store next)]

    [else (error 'eval (format "AST no reconocido: ~a" ast))]))