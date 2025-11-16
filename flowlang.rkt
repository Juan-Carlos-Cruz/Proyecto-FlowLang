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
    
    [(list 'list es ...)
    (define-values (vals e1 s1 n1) (eval-list es env store next))
    (result vals e1 s1 n1)]

    [(list* 'call f args)
    (define-values (vf e1 s1 n1) (eval* f env store next))
    (apply-call vf args e1 s1 n1 #f)]
    [(list* 'dict pairs)
    (define h (make-hasheq))
    (define (add-pair p e s n)
    (match p
        [(list (? symbol? k) e1)
        (define-values (v e2 s2 n2) (eval* e1 e s n))
        (hash-set! h k v)
        (values 'ok e2 s2 n2)]
        [else (error 'dict (format "par mal formado: ~a" p))]))
    (define-values (_ e1 s1 n1)
    (let loop ((rest pairs) (e env) (s store) (n next))
        (if (null? rest)
            (values 'ok e s n)
            (call-with-values
                (λ () (add-pair (car rest) e s n))
            (λ (_ e2 s2 n2)
                (loop (cdr rest) e2 s2 n2))))))
    (result h e1 s1 n1)]

    [(list 'print es ...)
    (define-values (vals e1 s1 n1) (eval-list es env store next))
    (for ([v vals]) (displayln v))
    (result (if (null? vals) 'null (last vals)) e1 s1 n1)]

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

    (define (ensure-list who v)
  (unless (listV? v) (error who "no es lista")))

(define (valid-index? idx)
  (and (integer? idx) (>= idx 0)))

(define (list-ref-safely lst idx)
  (if (valid-index? idx)
      (let loop ((xs lst) (i idx))
        (cond
          [(null? xs) 'null]
          [(zero? i) (car xs)]
          [else (loop (cdr xs) (sub1 i))]))
      'null))

(define (list-replace lst idx val who)
  (unless (valid-index? idx) (error who "índice inválido: ~a" idx))
  (let loop ((xs lst) (i idx))
    (cond
      [(null? xs) (error who "índice fuera de rango: ~a" idx)]
      [(zero? i) (cons val (cdr xs))]
      [else (cons (car xs) (loop (cdr xs) (sub1 i)))])))

(define (update-symbol-binding! env store name value)
  (define b (env-lookup env name))
  (store-set! store (binding-loc b) value))

(define (maybe-update-symbol! env store expr value)
  (when (symbol? expr)
    (update-symbol-binding! env store expr value)))

(define (eval-prim-call f args env store next)
  (define (eval1 e env store next) (eval* e env store next))
  
  (match f
    ['vacio?
     (match args
       [(list L)
        (define-values (vL e1 s1 n1) (eval1 L env store next))
        (ensure-list 'vacio? vL)
        (values (null? vL) e1 s1 n1)]
       [else (error 'vacio? "uso: (call vacio? lista)")])]
    
    ['crear-lista
     (match args
       [(list elem lst-expr)
        (define-values (vE e1 s1 n1) (eval1 elem env store next))
        (define-values (vL e2 s2 n2) (eval1 lst-expr e1 s1 n1))
        (ensure-list 'crear-lista vL)
        (values (cons vE vL) e2 s2 n2)]
       [else (error 'crear-lista "uso: (call crear-lista elem lista)")])]
    
    ['lista?
     (match args
       [(list expr)
        (define-values (v e1 s1 n1) (eval1 expr env store next))
        (values (listV? v) e1 s1 n1)]
       [else (error 'lista? "uso: (call lista? valor)")])]
    
    ['cabeza
     (match args
       [(list lst-expr)
        (define-values (vL e1 s1 n1) (eval1 lst-expr env store next))
        (ensure-list 'cabeza vL)
        (values (if (null? vL) 'null (car vL)) e1 s1 n1)]
       [else (error 'cabeza "uso: (call cabeza lista)")])]
    
    ['cola
     (match args
       [(list lst-expr)
        (define-values (vL e1 s1 n1) (eval1 lst-expr env store next))
        (ensure-list 'cola vL)
        (values (if (null? vL) '() (cdr vL)) e1 s1 n1)]
       [else (error 'cola "uso: (call cola lista)")])]

    ['append
     (match args
       [(list a b)
        (define-values (vA e1 s1 n1) (eval1 a env store next))
        (define-values (vB e2 s2 n2) (eval1 b e1 s1 n1))
        (ensure-list 'append vA)
        (ensure-list 'append vB)
        (values (append vA vB) e2 s2 n2)]
       [else (error 'append "uso: (call append lista1 lista2)")])]

    ['ref-list
     (match args
       [(list lst-expr idx-expr)
        (define-values (vL e1 s1 n1) (eval1 lst-expr env store next))
        (ensure-list 'ref-list vL)
        (define-values (vIdx e2 s2 n2) (eval1 idx-expr e1 s1 n1))
        (values (list-ref-safely vL vIdx) e2 s2 n2)]
       [else (error 'ref-list "uso: (call ref-list lista indice)")])]

    ['set-list
     (match args
       [(list lst-expr idx-expr val-expr)
        (define-values (vL e1 s1 n1) (eval1 lst-expr env store next))
        (ensure-list 'set-list vL)
        (define-values (vIdx e2 s2 n2) (eval1 idx-expr e1 s1 n1))
        (define-values (vVal e3 s3 n3) (eval1 val-expr e2 s2 n2))
        (define newL (list-replace vL vIdx vVal 'set-list))
        (maybe-update-symbol! e3 s3 lst-expr newL)
        (values newL e3 s3 n3)]
       [else (error 'set-list "uso: (call set-list lista indice valor)")])]
    
    ['crear-diccionario
 (define h (make-hasheq))
 (define (loop rest e s n)
   (cond
     [(null? rest) (values h e s n)]
     [(null? (cdr rest)) (error 'crear-diccionario "se requieren pares clave/valor")]
     [else
      (define-values (k e1 s1 n1) (eval1 (car rest) e s n))
      (define-values (v e2 s2 n2) (eval1 (cadr rest) e1 s1 n1))
      (hash-set! h (dict-key 'crear-diccionario k) v)
      (loop (cddr rest) e2 s2 n2)]))
 (loop args env store next)]

    ['diccionario?
    (match args
    [(list expr)
        (define-values (v e1 s1 n1) (eval1 expr env store next))
        (values (dictV? v) e1 s1 n1)]
    [else (error 'diccionario? "uso: (call diccionario? valor)")])]

    ['ref-diccionario
    (match args
    [(list dic-expr key-expr)
        (define-values (vD e1 s1 n1) (eval1 dic-expr env store next))
        (ensure-dict 'ref-diccionario vD)
        (define-values (vK e2 s2 n2) (eval1 key-expr e1 s1 n1))
        (values (hash-ref vD (dict-key 'ref-diccionario vK) 'null) e2 s2 n2)]
    [else (error 'ref-diccionario "uso: (call ref-diccionario dic clave)")])]

    ['set-diccionario
    (match args
    [(list dic-expr key-expr val-expr)
        (define-values (vD e1 s1 n1) (eval1 dic-expr env store next))
        (ensure-dict 'set-diccionario vD)
        (define-values (vK e2 s2 n2) (eval1 key-expr e1 s1 n1))
        (define-values (vVal e3 s3 n3) (eval1 val-expr e2 s2 n2))
        (hash-set! vD (dict-key 'set-diccionario vK) vVal)
        (maybe-update-symbol! e3 s3 dic-expr vD)
        (values vD e3 s3 n3)]
    [else (error 'set-diccionario "uso: (call set-diccionario dic clave valor)")])]

    ['claves
    (match args
    [(list dic-expr)
        (define-values (vD e1 s1 n1) (eval1 dic-expr env store next))
        (ensure-dict 'claves vD)
        (values (hash-keys vD) e1 s1 n1)]
    [else (error 'claves "uso: (call claves diccionario)")])]

    ['valores
    (match args
    [(list dic-expr)
        (define-values (vD e1 s1 n1) (eval1 dic-expr env store next))
        (ensure-dict 'valores vD)
        (values (hash-values vD) e1 s1 n1)]
    [else (error 'valores "uso: (call valores diccionario)")])]

    ['longitud
    (match args
    [(list expr)
        (define-values (v e1 s1 n1) (eval1 expr env store next))
        (unless (string? v) (error 'longitud "esperaba cadena"))
        (values (string-length v) e1 s1 n1)]
    [else (error 'longitud "uso: (call longitud cadena)")])]

    ['concatenar
    (match args
    [(list a b)
        (define-values (va e1 s1 n1) (eval1 a env store next))
        (define-values (vb e2 s2 n2) (eval1 b e1 s1 n1))
        (unless (and (string? va) (string? vb)) (error 'concatenar "esperaba dos cadenas"))
        (values (string-append va vb) e2 s2 n2)]
    [else (error 'concatenar "uso: (call concatenar cad1 cad2)")])]

    ['print
    (define-values (vals e1 s1 n1)
    (let loop ((rest args) (acc '()) (e env) (s store) (n next))
        (if (null? rest)
            (values (reverse acc) e s n)
            (let-values ([(v e2 s2 n2) (eval1 (car rest) e s n)])
            (loop (cdr rest) (cons v acc) e2 s2 n2)))))
    (for ([v vals]) (displayln v))
    (values (if (null? vals) 'null (last vals)) e1 s1 n1)]
    
    [else (error 'call (format "función/primitiva desconocida: ~a" f))]))


    (define (apply-call vf args env store next maybe-this)
    (cond
        [(closure? vf)
        (error 'call "closures aún no implementadas")]
        [else (eval-prim-call vf args env store next)]))

    (define (ensure-dict who v)
    (unless (dictV? v) (error who "no es diccionario")))

    (define (dict-key who k)
    (cond
        [(symbol? k) k]
        [(string? k) (string->symbol k)]
        [else (error who (format "clave inválida: ~a" k))]))

