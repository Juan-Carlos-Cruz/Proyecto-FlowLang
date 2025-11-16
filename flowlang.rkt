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
