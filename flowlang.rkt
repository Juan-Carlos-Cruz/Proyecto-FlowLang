#lang racket
(require (only-in eopl sllgen:make-string-parser))
(provide eval-program run)
;; FlowLang – Intérprete combinado (v2 corregido)
;;  - var/const, asignación y secuenciación (store de referencias)
;;  - funciones/closures (lexical), recursión
;;  - paso de parámetros: por valor (escalares) y por referencia (listas, diccionarios, objetos)
;;  - listas, diccionarios, objetos prototipales (clone, lookup por proto)
;;  - if, while, for, switch
;;  - primitivas aritméticas y lógicas: + - * / < <= > >= equal? and or not
;;  - pruebas incluidas al final

(struct binding (loc mutable?) #:transparent)
(struct closure (params body env) #:transparent)
(struct obj (fields proto) #:transparent)   ; fields: (hash), proto: obj|#f

(define (make-empty-store) (values (make-hasheq) 0))
(define location-watchers (make-hasheq))  ; loc -> (λ (new-value) ...)

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
(define empty-env (hash))
(define (env-lookup env name) (hash-ref env name (λ () (error 'lookup "variable no definida: ~a" name))))
(define (env-extend env name bind) (hash-set env name bind))

(define (scalar? v) (or (number? v) (boolean? v) (string? v) (eq? v 'null)))
(define (listV? v) (and (list? v) (not (obj? v))))
(define (dictV? v) (hash? v))
(define (objV? v) (obj? v))
(define (compound? v) (or (listV? v) (dictV? v) (objV? v)))
(define (truthy? v)
  (cond
    [(eq? v #f) #f]
    [(eq? v 'null) #f]
    [(and (number? v) (zero? v)) #f]
    [(and (string? v) (string=? v "")) #f]
    [else #t]))
(define primitive-symbols
  '(+ - * / < <= > >= not and or equal? list-push!
    vacio? crear-lista lista? cabeza cola append ref-list set-list
    crear-diccionario diccionario? ref-diccionario set-diccionario
    claves valores
    longitud concatenar
    % // add1 sub1))
(define (primitive-symbol? sym) (memq sym primitive-symbols))
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

(define pure-imag-regex #px"^([0-9]+(?:\\.[0-9]+)?(?:[eE][+-]?[0-9]+)?)?[iI]$")
(define (parse-number-lexeme lex)
  (cond
    [(number? lex) lex]
    [(string? lex)
     (or (string->number lex)
         (let ([m (regexp-match pure-imag-regex lex)])
           (if m
               (let* ([mag-str (or (cadr m) "1")]
                      [mag (string->number mag-str)])
                 (if mag
                     (make-rectangular 0 mag)
                     (error 'number (format "lexema numérico inválido: ~a" lex))))
               (error 'number (format "lexema numérico inválido: ~a" lex)))))]
    [else lex]))

(define (ensure-list who v)
  (unless (listV? v) (error who "no es lista")))

(define (ensure-dict who v)
  (unless (dictV? v) (error who "no es diccionario")))

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

(define (dict-key who k)
  (cond
    [(symbol? k) k]
    [(string? k) (string->symbol k)]
    [else (error who (format "clave inválida: ~a" k))]))

(define (update-symbol-binding! env store name value)
  (define b (env-lookup env name))
  (store-set! store (binding-loc b) value))

(define (maybe-update-symbol! env store expr value)
  (when (symbol? expr)
    (update-symbol-binding! env store expr value)))

(define (iterable-values who v)
  (cond
    [(listV? v) v]
    [(dictV? v) (hash-values v)]
    [(string? v) (string->list v)]
    [else (error who "estructura no iterable: ~a" v)]))

(define (result v env store next) (values v env store next))
(define (eval-program ast)
  (define-values (S N) (make-empty-store))
  (define-values (v _e _S _N) (eval* ast empty-env S N))
  (if (return-signal? v) (return-signal-value v) v))

(define (run ast) (eval-program ast))

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

(define (eval-const-bindings bindings env store next)
  (let loop ((bs bindings) (e env) (s store) (n next))
    (if (null? bs)
        (result 'ok e s n)
        (let* ([entry (car bs)]
               [x (binding-id entry)]
               [expr (binding-expr entry)])
          (define-values (v env1 s1 n1) (eval* expr e s n))
          (define-values (loc n2) (store-alloc s1 n1 v))
          (loop (cdr bs) (env-extend env1 x (binding loc #f)) s1 n2)))))

;; -----------------------------------------------------------------------------
;; Parser (fase 2, parte 1)
;; -----------------------------------------------------------------------------

(define (make-program stmts) (list 'program (cons 'block stmts)))
(define (make-binop op lhs rhs) `(call ,op ,lhs ,rhs))
(define (make-neg expr) (make-binop '- 0 expr))
(define (fold-left base funcs)
  (foldl (λ (f acc) (f acc)) base funcs))
(define return-no-expr-tag '#:return-none)
(struct return-signal (value) #:transparent)

(define (make-binding-entry id expr) (list id expr))
(define (binding-tail-entry entry) entry)
(define (bindings->list first rest) (cons first rest))
(define (bindings->var-node bindings)
  (if (= (length bindings) 1)
      (let ([b (car bindings)])
        (list 'var (car b) (cadr b)))
      (list 'var* bindings)))
(define (bindings->const-node bindings)
  (if (= (length bindings) 1)
      (let ([b (car bindings)])
        (list 'const (car b) (cadr b)))
      (list 'const* bindings)))
(define (postfix-node base tails) (fold-left base tails))
(define (postfix-call-tail args) (lambda (left) (make-call-node left args)))
(define (make-call-node left args)
  (match left
    [(list 'get base (? symbol? field)) (apply list 'call-method base field args)]
    [else (apply list 'call left args)]))
(define (postfix-dot-tail id) (lambda (left) (list 'get left id)))
(define (assign-from-id-postfix lhs expr)
  (match lhs
    [(? symbol? x) (list 'set x expr)]
    [(list 'get base (? symbol? field)) (list 'set-field! base field expr)]
    [else (error 'assignment "lado izquierdo inválido: ~a" lhs)]))

(define (eval-arg expr env store next)
  (match expr
    [(? symbol? x)
     (define b (env-lookup env x))
     (define val (store-ref store (binding-loc b)))
     (values val env store next (list 'loc (binding-loc b)))]
    [(list 'get base (? symbol? field))
     (define-values (obj env1 store1 next1) (eval* base env store next))
     (unless (objV? obj) (error 'get "no es objeto"))
     (values (obj-get obj field) env1 store1 next1 (list 'field obj field))]
    [else
     (define-values (val env1 store1 next1) (eval* expr env store next))
     (values val env1 store1 next1 #f)]))

(define (ensure-param-location value ref store next)
  (define (alloc-new v s n)
    (store-alloc s n v))
  (cond
    [(and ref (compound? value))
     (match ref
       [(list 'loc locnum) (values locnum next)]
       [(list 'field obj field-id)
        (define-values (loc n2) (store-alloc store next value))
        (attach-location-watcher! loc (λ (nv) (hash-set! (obj-fields obj) field-id nv)))
        (values loc n2)]
       [else (alloc-new value store next)])]
    [else (alloc-new value store next)]))

(define (apply-call vf args env store next maybe-this)
  (cond
    [(closure? vf)
     (define c vf)
     (define argvals '()) (define argrefs '())
     (let loopA ((as args) (e env) (s store) (n next) (av '()) (ar '()))
       (if (null? as)
           (begin
             (set! argvals (reverse av))
             (set! argrefs (reverse ar))
             (values 'ok e s n))
           (let* ([a (car as)])
             (let-values ([(v e2 s2 n2 ref) (eval-arg a e s n)])
               (loopA (cdr as) e2 s2 n2 (cons v av) (cons ref ar))))))
     (define base-env (closure-env c))
     (define-values (env-with-this next-after-this)
       (if maybe-this
           (let-values ([(loc n2) (store-alloc store next maybe-this)])
             (values (env-extend base-env 'this (binding loc #f)) n2))
           (values base-env next)))
     (define argvals-vec (list->vector argvals))
     (define argrefs-vec (list->vector argrefs))
     (define-values (env-call next-after-params)
       (for/fold ([env0 env-with-this] [n0 next-after-this])
                 ([param (in-list (closure-params c))] [i (in-naturals)])
         (define v (vector-ref argvals-vec i))
         (define ref (vector-ref argrefs-vec i))
         (define-values (loc n1) (ensure-param-location v ref store n0))
         (values (env-extend env0 param (binding loc #t)) n1)))
     (let-values ([(body-result env2 s2 n2) (eval* (closure-body c) env-call store next-after-params)])
       (if (return-signal? body-result)
           (values (return-signal-value body-result) env2 s2 n2)
           (values body-result env2 s2 n2)))]
    [else (eval-prim-call vf args env store next)]))

(define (program-node stmts) (make-program stmts))
(define (statements-node stmts) stmts)
(define (stmt-var ast) ast)
(define (stmt-const ast) ast)
(define (stmt-assign ast) ast)
(define (stmt-print ast) ast)
(define (stmt-block ast) ast)
(define (stmt-if ast) ast)
(define (stmt-while ast) ast)
(define (stmt-for ast) ast)
(define (stmt-switch ast) ast)
(define (stmt-return ast) ast)
(define (var-decl-node first rest) (bindings->var-node (bindings->list first rest)))
(define (const-decl-node first rest) (bindings->const-node (bindings->list first rest)))
(define (assign-node id expr) (list 'set id expr))
(define (print-node expr) (list 'print expr))
(define (block-node stmts) (cons 'block stmts))
(define (if-node cond then-branch else-branch) (list 'if cond then-branch else-branch))
(define (while-node cond body) (list 'while cond body))
(define (for-node init cond step body) (list 'for (list init cond step) body))
(define (for-stmt-node tail) tail)
(define (for-in-node id iterable body) (list 'for-in id iterable body))
(define (for-init-stmt stmt) stmt)
(define (for-init-empty) '(block))
(define (switch-node expr cases) (cons 'switch (cons expr cases)))
(define (case-node value body) (list 'case value body))
(define (default-node body) (list 'default body))
(define (return-no-expr) return-no-expr-tag)
(define (return-node maybe-expr) (list 'return maybe-expr))
(define (expression-node value) value)
(define (or-node first tails) (fold-left first tails))
(define (or-tail-node expr) (lambda (left) `(call or ,left ,expr)))
(define (and-node first tails) (fold-left first tails))
(define (and-tail-node expr) (lambda (left) `(call and ,left ,expr)))
(define (equality-node first tails) (fold-left first tails))
(define (eq-equal-node expr) (lambda (left) `(call equal? ,left ,expr)))
(define (eq-not-equal-node expr)
  (lambda (left) `(call not (call equal? ,left ,expr))))
(define (relational-node first tails) (fold-left first tails))
(define (rel-lt-node expr) (lambda (left) (make-binop '< left expr)))
(define (rel-le-node expr) (lambda (left) (make-binop '<= left expr)))
(define (rel-gt-node expr) (lambda (left) (make-binop '> left expr)))
(define (rel-ge-node expr) (lambda (left) (make-binop '>= left expr)))
(define (add-node first tails) (fold-left first tails))
(define (add-plus-tail expr) (lambda (left) (make-binop '+ left expr)))
(define (add-minus-tail expr) (lambda (left) (make-binop '- left expr)))
(define (term-node first tails) (fold-left first tails))
(define (mul-times-tail expr) (lambda (left) (make-binop '* left expr)))
(define (mul-div-tail expr)   (lambda (left) (make-binop '/ left expr)))
(define (mul-mod-tail expr)   (lambda (left) (make-binop '% left expr)))
(define (unary-not-node expr) `(call not ,expr))
(define (unary-neg-node expr) (make-neg expr))
(define (unary-primary-node expr) expr)
(define (primary-number n) (parse-number-lexeme n))
(define (primary-string s) s)
(define (primary-true) #t)
(define (primary-false) #f)
(define (primary-null) 'null)
(define (primary-vacio) (list 'list))
(define (primary-id value) value)
(define (primary-paren expr) expr)
(define (primary-func params body) (list 'fun params body))
(define (primary-list items) (cons 'list items))
(define (primary-dict entries) (cons 'dict entries))
(define (list-empty) '())
(define (list-nonempty first rest) (cons first rest))
(define (list-tail-node expr) expr)
(define (dict-empty) '())
(define (dict-nonempty first rest) (cons first rest))
(define (dict-tail-node entry) entry)
(define (dict-entry-id key expr) (list key expr))
(define (dict-entry-str key expr) (list (string->symbol key) expr))
(define (arg-list-empty) '())
(define (arg-list-some first rest) (cons first rest))
(define (arg-more-node expr) expr)
(define (param-list-empty) '())
(define (param-list-some first rest) (cons first rest))
(define (param-more-node id) id)
(define (primary-begin stmts) (cons 'begin stmts))
(define (primary-obj specs) (cons 'obj specs))
(define (obj-specs-empty) '())
(define (obj-specs-some first rest) (cons first rest))
(define (obj-spec-tail-node entry) entry)
(define (obj-field-entry id expr) (list id expr))
(define (obj-proto-entry expr) (list 'proto expr))
(define (primary-clone expr) (list 'clone expr))

(define flowlang-parser
  (sllgen:make-string-parser
   '((whitespace (whitespace) skip)
     (comment ("//" (arbno (not #\newline))) skip)
     ;; Números complejos/imaginarios y flotantes
     (number (digit (arbno digit) "." digit (arbno digit) (or "i" "I")) string)
     (number (digit (arbno digit) (or "i" "I")) string)
     (number (digit (arbno digit) "." digit (arbno digit) (or "e" "E") "+" digit (arbno digit)) string)
     (number (digit (arbno digit) "." digit (arbno digit) (or "e" "E") "-" digit (arbno digit)) string)
     (number (digit (arbno digit) "." digit (arbno digit) (or "e" "E") digit (arbno digit)) string)
     (number (digit (arbno digit) (or "e" "E") "+" digit (arbno digit)) string)
     (number (digit (arbno digit) (or "e" "E") "-" digit (arbno digit)) string)
     (number (digit (arbno digit) (or "e" "E") digit (arbno digit)) string)
     (number (digit (arbno digit) "." digit (arbno digit)) string)
     (number (digit (arbno digit)) string)
     (string ("\"" (arbno (not #\")) "\"") string)
     (identifier ((or letter "_") (arbno (or letter digit "_" "-" "?" "!"))) symbol))
   '((program (statements) program-node)
     (statements ((arbno statement)) statements-node)

     (statement (var-decl) stmt-var)
     (statement (const-decl) stmt-const)
     (statement (assignment) stmt-assign)
     (statement (print-stmt) stmt-print)
     (statement (block) stmt-block)
     (statement (if-stmt) stmt-if)
     (statement (while-stmt) stmt-while)
     (statement (for-stmt) stmt-for)
     (statement (switch-stmt) stmt-switch)
     (statement (return-stmt) stmt-return)

     (var-decl ("var" var-binding (arbno var-binding-tail) ";") var-decl-node)
     (const-decl ("const" const-binding (arbno const-binding-tail) ";") const-decl-node)
     (assignment (id-postfix "=" expression ";") assign-from-id-postfix)
     (print-stmt ("print" "(" expression ")" ";") print-node)
     (block ("{" statements "}") block-node)
     (if-stmt ("if" "(" expression ")" statement "else" statement) if-node)
     (while-stmt ("while" "(" expression ")" statement) while-node)
     (for-stmt ("for" for-tail) for-stmt-node)
     (for-tail ("(" for-init ";" expression ";" for-step ")" statement) for-node)
     (for-tail (identifier "in" expression "do" statement "done") for-in-node)
     (switch-stmt ("switch" "(" expression ")" "{" case-list "}") switch-node)
     (return-stmt ("return" return-opt ";") return-node)
     (return-opt () return-no-expr)
     (return-opt (expression) identity)

     (for-init () for-init-empty)
     (for-init (var-decl-no-semi) for-init-stmt)
     (for-init (assignment-no-semi) for-init-stmt)
     (for-step (assignment-no-semi) for-init-stmt)
     (var-decl-no-semi ("var" var-binding (arbno var-binding-tail)) var-decl-node)
     (const-decl-no-semi ("const" const-binding (arbno const-binding-tail)) const-decl-node)
     (assignment-no-semi (id-postfix "=" expression) assign-from-id-postfix)
     (case-list ((arbno case-entry)) identity)
     (case-entry ("case" expression ":" statement) case-node)
     (case-entry ("default" ":" statement) default-node)

     (expression (or-expr) expression-node)
     (or-expr (and-expr (arbno or-tail)) or-node)
     (or-tail ("||" and-expr) or-tail-node)

     (and-expr (equality (arbno and-tail)) and-node)
     (and-tail ("&&" equality) and-tail-node)

     (equality (relational (arbno eq-tail)) equality-node)
     (eq-tail ("==" relational) eq-equal-node)
     (eq-tail ("!=" relational) eq-not-equal-node)

     (relational (add-expr (arbno rel-tail)) relational-node)
     (rel-tail ("<" add-expr) rel-lt-node)
     (rel-tail ("<=" add-expr) rel-le-node)
     (rel-tail (">" add-expr) rel-gt-node)
     (rel-tail (">=" add-expr) rel-ge-node)

     (add-expr (term (arbno add-tail)) add-node)
     (add-tail ("+" term) add-plus-tail)
     (add-tail ("-" term) add-minus-tail)

     (term (unary (arbno mul-tail)) term-node)
     (mul-tail ("*" unary) mul-times-tail)
     (mul-tail ("/" unary) mul-div-tail)
     (mul-tail ("%" unary) mul-mod-tail)

     (unary ("!" unary) unary-not-node)
     (unary ("-" unary) unary-neg-node)
     (unary (postfix) unary-primary-node)

     (postfix (primary (arbno postfix-tail)) postfix-node)
     (postfix-tail ("(" arg-list ")") postfix-call-tail)
     (postfix-tail ("." identifier) postfix-dot-tail)
     (id-postfix (identifier (arbno postfix-tail)) postfix-node)

     (primary (number) primary-number)
     (primary (string) primary-string)
     (primary ("true") primary-true)
     (primary ("false") primary-false)
     (primary ("null") primary-null)
     (primary ("vacio") primary-vacio)
     (primary (identifier) primary-id)
     (primary ("[" opt-list "]") primary-list)
     (primary ("{" opt-dict "}") primary-dict)
     (primary ("func" "(" param-list ")" statement) primary-func)
     (primary ("begin" statements "end") primary-begin)
     (primary ("obj" "{" obj-specs "}") primary-obj)
     (primary ("clone" "(" expression ")") primary-clone)
     (primary ("(" expression ")") primary-paren)

     (opt-list () list-empty)
     (opt-list (expression (arbno list-tail)) list-nonempty)
     (list-tail ("," expression) list-tail-node)

      (opt-dict () dict-empty)
      (opt-dict (dict-entry (arbno dict-tail)) dict-nonempty)
     (dict-tail ("," dict-entry) dict-tail-node)
     (dict-entry (identifier ":" expression) dict-entry-id)
     (dict-entry (string ":" expression) dict-entry-str)
     (var-binding (identifier "=" expression) make-binding-entry)
     (var-binding-tail ("," var-binding) binding-tail-entry)
     (const-binding (identifier "=" expression) make-binding-entry)
     (const-binding-tail ("," const-binding) binding-tail-entry)
     (obj-specs () obj-specs-empty)
     (obj-specs (obj-entry (arbno obj-spec-tail)) obj-specs-some)
     (obj-spec-tail ("," obj-entry) obj-spec-tail-node)
     (obj-entry (identifier ":" expression) obj-field-entry)
     (obj-entry ("proto" ":" expression) obj-proto-entry)

     (param-list () param-list-empty)
     (param-list (identifier (arbno param-more)) param-list-some)
     (param-more ("," identifier) param-more-node)

     (arg-list () arg-list-empty)
     (arg-list (expression (arbno arg-more)) arg-list-some)
     (arg-more ("," expression) arg-more-node))))

(define (parse-source src)
  (flowlang-parser src))

(define (run-source src)
  (run (parse-source src)))

(define (eval* ast env store next)
  (match ast
    [(list 'program es ...) (eval-seq es env store next #t)]
    [(list 'block es ...)   (eval-seq es env store next #f)]
    [(list 'begin es ...)   (eval-seq-flat es env store next)]

    [(list 'var* bindings)
     (eval-var-bindings bindings env store next)]

    [(list 'var (? symbol? x) e)
     (eval-var-bindings (list (make-binding-entry x e)) env store next)]

    [(list 'const* bindings)
     (eval-const-bindings bindings env store next)]

    [(list 'const (? symbol? x) e)
     (eval-const-bindings (list (make-binding-entry x e)) env store next)]

    [(list 'set (? symbol? x) e)
     (define b (env-lookup env x))
     (unless (binding-mutable? b) (error 'set "no se puede asignar a const ~a" x))
     (define-values (v1 env1 s1 n1) (eval* e env store next))
     (store-set! s1 (binding-loc b) v1)
     (result v1 env1 s1 n1)]

    [(list 'return expr)
     (if (eq? expr return-no-expr-tag)
         (values (return-signal 'null) env store next)
         (let-values ([(v env1 s1 n1) (eval* expr env store next)])
           (values (return-signal v) env1 s1 n1)))]

    [(? (λ (x) (and (symbol? x) (not (eq? x 'null)))) x)
     (if (primitive-symbol? x)
         (result x env store next)
         (let ([b (env-lookup env x)])
           (result (store-ref store (binding-loc b)) env store next)))]

    [(list 'if c t e)
     (define-values (vc e1 s1 n1) (eval* c env store next))
     (if (truthy? vc) (eval* t e1 s1 n1) (eval* e e1 s1 n1))]

    [(list 'while c body)
     (let loop ((e0 env) (s0 store) (n0 next) (last 'null))
       (let-values ([(vc e1 s1 n1) (eval* c e0 s0 n0)])
         (if (truthy? vc)
             (let-values ([(vb e2 s2 n2) (eval* body e1 s1 n1)])
               (loop e2 s2 n2 vb))
             (values last e1 s1 n1))))]

    [(list 'for (list init c step) body)
     (define-values (_vi e1 s1 n1) (eval* init env store next))
     (let loop ((e0 e1) (s0 s1) (n0 n1) (last 'null))
       (let-values ([(vc e2 s2 n2) (eval* c e0 s0 n0)])
         (if (truthy? vc)
             (let-values ([(vb e3 s3 n3) (eval* body e2 s2 n2)])
               (let-values ([(_vs e4 s4 n4) (eval* step e3 s3 n3)])
                 (loop e4 s4 n4 vb)))
             (values last e2 s2 n2))))]
    [(list 'for-in (? symbol? x) seq-expr body)
     (define-values (seq-val e1 s1 n1) (eval* seq-expr env store next))
     (define seq (iterable-values 'for-in seq-val))
     (define-values (loc n2) (store-alloc s1 n1 'null))
     (define env-with-iter (env-extend e1 x (binding loc #t)))
     (let loop ((vals seq) (e env-with-iter) (s s1) (n n2) (last 'null))
       (if (null? vals)
           (values last e s n)
           (begin
             (store-set! s loc (car vals))
             (let-values ([(vb e2 s2 n2) (eval* body e s n)])
               (if (return-signal? vb)
                   (values vb e2 s2 n2)
                   (loop (cdr vals) e2 s2 n2 vb))))))]

    [(list 'switch e cases ...)
     (define-values (v e1 s1 n1) (eval* e env store next))
     (define default-branch (for/or ([c cases]) (and (pair? c) (eq? (car c) 'default) c)))
     (define (run b) (eval* b e1 s1 n1))
     (let try ((cs cases))
       (cond [(null? cs) (if default-branch (run (cadr default-branch)) (values 'null e1 s1 n1))]
             [else (define c (car cs))
                   (match c
                     [(list 'case vcase body)
                      (if (equal? v (raw-value vcase)) (run body) (try (cdr cs)))]
                     [(list 'default body) (try (cdr cs))]
                     [else (error 'switch (format "caso mal formado: ~a" c))])]))]

    [(list 'fun (list params ...) body) (result (closure params body env) env store next)]

    [(list* 'call f args)
     (define-values (vf e1 s1 n1) (eval* f env store next))
     (apply-call vf args e1 s1 n1 #f)]
    [(list* 'call-method base field args)
     (define-values (vo e1 s1 n1) (eval* base env store next))
     (unless (objV? vo) (error 'call-method "receptor no es objeto"))
     (define method (obj-get vo field))
     (apply-call method args e1 s1 n1 vo)]

    [(list 'list es ...) (define-values (vals e1 s1 n1) (eval-list es env store next)) (result vals e1 s1 n1)]

    [(list* 'dict pairs)
     (define h (make-hasheq))
     (define (add-pair p e s n)
       (match p
         [(list (? symbol? k) e1) (define-values (v e2 s2 n2) (eval* e1 e s n)) (hash-set! h k v) (values 'ok e2 s2 n2)]
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

    [(list 'dict-get d (? symbol? k)) (define-values (vd e1 s1 n1) (eval* d env store next)) (unless (dictV? vd) (error 'dict-get "no es diccionario")) (result (hash-ref vd k 'null) e1 s1 n1)]
    [(list 'dict-set! d (? symbol? k) e)
     (define-values (vd e1 s1 n1) (eval* d env store next)) (unless (dictV? vd) (error 'dict-set! "no es diccionario"))
     (define-values (vv e2 s2 n2) (eval* e e1 s1 n1)) (hash-set! vd k vv) (result vv e2 s2 n2)]

    [(list* 'obj specs)
     (define h (make-hasheq)) (define proto #f)
     (define (handle-spec sp e s n)
       (match sp
         [(list 'proto e1) (define-values (vo e2 s2 n2) (eval* e1 e s n)) (unless (objV? vo) (error 'obj "proto debe ser objeto")) (set! proto vo) (values 'ok e2 s2 n2)]
         [(list (? symbol? k) e1) (define-values (v e2 s2 n2) (eval* e1 e s n)) (hash-set! h k v) (values 'ok e2 s2 n2)]
         [else (error 'obj (format "spec mal formada: ~a" sp))]))
     (define-values (_ e1 s1 n1)
       (let loop ((rest specs) (e env) (s store) (n next))
         (if (null? rest)
             (values 'ok e s n)
             (call-with-values
                 (λ () (handle-spec (car rest) e s n))
               (λ (_ e2 s2 n2)
                 (loop (cdr rest) e2 s2 n2))))))
     (result (obj h proto) e1 s1 n1)]

    [(list 'get o (? symbol? k)) (define-values (vo e1 s1 n1) (eval* o env store next)) (result (obj-get vo k) e1 s1 n1)]
    [(list 'set-field! o (? symbol? k) e) (define-values (vo e1 s1 n1) (eval* o env store next)) (unless (objV? vo) (error 'set-field! "no es objeto")) (define-values (vv e2 s2 n2) (eval* e e1 s1 n1)) (hash-set! (obj-fields vo) k vv) (result vv e2 s2 n2)]
    [(list 'clone o) (define-values (vo e1 s1 n1) (eval* o env store next)) (unless (objV? vo) (error 'clone "no es objeto")) (result (obj (make-hasheq) vo) e1 s1 n1)]

    [(list 'type-of e) (define-values (v1 e1 s1 n1) (eval* e env store next)) (result (type-of* v1) e1 s1 n1)]
    [(list 'len e) (define-values (v1 e1 s1 n1) (eval* e env store next)) (cond [(listV? v1) (result (length v1) e1 s1 n1)] [(dictV? v1) (result (hash-count v1) e1 s1 n1)] [(objV? v1) (result (hash-count (obj-fields v1)) e1 s1 n1)] [else (error 'len "tipo no soportado")])]
    [(list 'keys d) (define-values (vd e1 s1 n1) (eval* d env store next)) (unless (dictV? vd) (error 'keys "no es diccionario")) (result (hash-keys vd) e1 s1 n1)]
    [(list 'values d) (define-values (vd e1 s1 n1) (eval* d env store next)) (unless (dictV? vd) (error 'values "no es diccionario")) (result (hash-values vd) e1 s1 n1)]

    [(list 'print es ...) (define-values (vals e1 s1 n1) (eval-list es env store next)) (for ([v vals]) (displayln v)) (result (if (null? vals) 'null (last vals)) e1 s1 n1)]
    [(or (? number?) (? boolean?) (? string?) 'null) (result ast env store next)]
    [else (error 'eval (format "AST no reconocido: ~a" ast))]))

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

;; Primitivas (aritméticas/lógicas y utilitarias)
(define (eval-prim-call f args env store next)
  (define (eval1 e env store next) (eval* e env store next))
  (define (eval2 a b env store next op)
    (define-values (va e1 s1 n1) (eval1 a env store next))
    (define-values (vb e2 s2 n2) (eval1 b e1 s1 n1))
    (values (op va vb) e2 s2 n2))
  (match f
    ['+  (match args [(list a b) (eval2 a b env store next +)] [else (error '+ "uso: (call + a b)")])]
    ['-  (match args [(list a b) (eval2 a b env store next -)] [else (error '- "uso: (call - a b)")])]
    ['*  (match args [(list a b) (eval2 a b env store next *)] [else (error '* "uso: (call * a b)")])]
    ['/  (match args [(list a b) (eval2 a b env store next /)] [else (error '/ "uso: (call / a b)")])]
    ['<  (match args [(list a b) (eval2 a b env store next <)] [else (error '< "uso: (call < a b)")])]
    ['<= (match args [(list a b) (eval2 a b env store next <=)] [else (error '<= "uso: (call <= a b)")])]
    ['>  (match args [(list a b) (eval2 a b env store next >)] [else (error '> "uso: (call > a b)")])]
    ['>= (match args [(list a b) (eval2 a b env store next >=)] [else (error '>= "uso: (call >= a b)")])]
    ['not (match args [(list a) (define-values (va e1 s1 n1) (eval1 a env store next)) (values (not (truthy? va)) e1 s1 n1)] [else (error 'not "uso: (call not a)")])]
    ['and (match args [(list a b) (define-values (va e1 s1 n1) (eval1 a env store next)) (if (truthy? va) (eval1 b e1 s1 n1) (values #f e1 s1 n1))] [else (error 'and "uso: (call and a b)")])]
    ['or  (match args [(list a b) (define-values (va e1 s1 n1) (eval1 a env store next)) (if (truthy? va) (values va e1 s1 n1) (eval1 b e1 s1 n1))] [else (error 'or "uso: (call or a b)")])]
    ['equal? (match args [(list a b) (define-values (va e1 s1 n1) (eval1 a env store next)) (define-values (vb e2 s2 n2) (eval1 b e1 s1 n1)) (values (equal? va vb) e2 s2 n2)] [else (error 'equal? "uso: (call equal? a b)")])]
    ['list-push!
     (match args
       [(list L e)
        (define-values (vL e1 s1 n1) (eval1 L env store next))
        (define-values (vE e2 s2 n2) (eval1 e e1 s1 n1))
        (unless (listV? vL) (error 'list-push! "L no es lista"))
        (define newL (append vL (list vE)))
        (when (symbol? L) (define b (env-lookup e2 L)) (store-set! s2 (binding-loc b) newL))
        (values newL e2 s2 n2)]
       [else (error 'list-push! "uso: (call list-push! lista expr)")])]
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
    ['%
     (match args
       [(list a b)
        (define-values (va e1 s1 n1) (eval1 a env store next))
        (define-values (vb e2 s2 n2) (eval1 b e1 s1 n1))
        (unless (and (number? va) (number? vb))
          (error '% "esperaba números"))
        (define rem
          (if (and (integer? va) (integer? vb))
              (remainder va vb)
              (- va (* vb (truncate (/ va vb))))))
        (values rem e2 s2 n2)]
       [else (error '% "uso: (call % a b)")])]
    ['//
     (match args
       [(list a b)
        (define-values (va e1 s1 n1) (eval1 a env store next))
        (define-values (vb e2 s2 n2) (eval1 b e1 s1 n1))
        (values (quotient va vb) e2 s2 n2)]
       [else (error '// "uso: (call // a b)")])]
    ['add1
     (match args
       [(list a)
        (define-values (va e1 s1 n1) (eval1 a env store next))
        (values (add1 va) e1 s1 n1)]
       [else (error 'add1 "uso: (call add1 a)")])]
    ['sub1
     (match args
       [(list a)
        (define-values (va e1 s1 n1) (eval1 a env store next))
        (values (sub1 va) e1 s1 n1)]
       [else (error 'sub1 "uso: (call sub1 a)")])]
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

(define (obj-get o k)
  (unless (objV? o) (error 'get "no es objeto"))
  (define fields (obj-fields o))
  (cond [(hash-has-key? fields k) (hash-ref fields k)]
        [(obj-proto o) => (λ (p) (obj-get p k))]
        [else 'null]))

(define (raw-value x)
  (match x [(? symbol?) x] [(? number?) x] [(? string?) x] [(? boolean?) x] ['null 'null] [else x]))

(module+ test
  (define (run ast) (eval-program ast))

  (displayln "== Prueba 1: var/const y set ==")
  (run '(program (block (var x 10) (const y 20) (set x 15) (print x) (begin (print (type-of x)) (print (type-of y))) 999)))

  (displayln "== Prueba 2: if/while/for ==")
  (run '(program (block
                   (var s 0)
                   (for ((var i 0) (call < i 5) (set i (call + i 1)))
                        (begin (set s (call + s i))))
                   (print s) ; 10
                   (var c 0)
                   (while (call < c 3) (begin (set c (call + c 1))))
                   (print c) ; 3
                   999)))

  (displayln "== Prueba 3: listas y paso por referencia ==")
  (run '(program (block
                   (var L (list 1 2))
                   (call list-push! L 99)
                   (print L) ; => (1 2 99)
                   (var x 5)
                   (var inc (fun (y) (set y (call + y 1))))
                   (call inc x)
                   (print x) ; 5 (escalares por valor)
                   999)))

  (displayln "== Prueba 4: diccionarios ==")
  (run '(program (block
                   (var D (dict (a 1) (b 2)))
                   (print (dict-get D a)) ; 1
                   (dict-set! D b 42)
                   (print (dict-get D b)) ; 42
                   (print (keys D))
                   999)))

  (displayln "== Prueba 5: funciones/closures y recursión ==")
  (run '(program (block
                   (var fact (fun (n) (if (call equal? n 0) 1 (call * n (call fact (call - n 1))))))
                   (print (call fact 5)) ; 120
                   999)))

  (displayln "== Prueba 6: objetos prototipales y clone ==")
  (run '(program (block
                   (var base (obj (x 1) (y 2)))
                   (var o1 (clone base))
                   (set-field! o1 x 10)
                   (print (get o1 x)) ; 10 (propia)
                   (print (get o1 y)) ; 2  (heredada)
                   (var o2 (obj (z 7) (proto o1)))
                   (print (get o2 y)) ; 2 por la cadena
                   999)))

  (displayln "== Prueba 7: switch ==")
  (run '(program (block
                   (var k 2)
                   (switch k (case 1 (print "uno")) (case 2 (print "dos")) (default (print "otro")))
                   999)))

  (displayln "== Prueba 8: for-in ==")
  (run '(program (block
                   (var suma 0)
                   (var numeros (list 1 2 3 4))
                   (for-in n numeros
                           (set suma (call + suma n)))
                   (print suma) ; 10
                   999)))

  (displayln "== Prueba 9: var/const múltiples ==")
  (run '(program (block
                   (var* ((a 1) (b (call + a 2))))
                   (const* ((c b) (d (call + c 3))))
                   (print d) ; 6
                   999)))

  (displayln "== Prueba 10: cadenas ==")
  (run '(program (block
                   (var saludo (call concatenar "Hola, " "mundo"))
                   (print saludo)
                   (print (call longitud saludo))
                   999)))

  (displayln "== Prueba 11: notación punto ==")
  (run '(program (block
                   (var base (obj (x 1) (y 2)))
                   (var hijo (clone base))
                   (set-field! base y 10)
                   (print (get hijo y)) ; 10 via proto
                   (set-field! base inc (fun () (begin (set-field! this y (call + (get this y) 1)) (get this y))))
                   (print (call-method base inc)) ; 11 usando this
                   999)))

  (displayln "== Prueba 12: paso por referencia en campos ==")
  (run '(program (block
                   (var data (obj (nums (list 1 2))))
                   (var reemplazar (fun (lista) (set lista (list 9 9))))
                   (call reemplazar (get data nums))
                   (print (get data nums)) ; (9 9)
                   999)))

  (displayln "== Prueba 13: primitivas aritméticas adicionales ==")
  (run '(program (block
                   (print (call % 10 3))    ; 1
                   (print (call // 10 3))   ; 3
                   (print (call add1 5))    ; 6
                   (print (call sub1 5))    ; 4
                   999)))

  (displayln "== Parser parcial (fase 2/8) ==")
  (run (parse-source "var x = 10; print(x);"))
  (run (parse-source "{ var suma = 1 + 2 * 3; print(suma); }"))
  (run (parse-source "{ var flag = 1; if (flag > 0) { print(111); } else { print(0); } }"))
  (run (parse-source "{ var datos = [1, 2, 3]; print(datos); }"))
  (run (parse-source "{ var conf = {clave: 1, \"otra\": 2}; print(conf); }"))
  (run (parse-source "{ var c = 2; while (c > 0) { print(c); c = c - 1; } }"))
  (run (parse-source "{ for (var i = 0; i < 3; i = i + 1) { print(i); } }"))
  (run (parse-source "{ switch (2) { case 1: print(1); default: print(2); } }"))
  (run (parse-source "{ var inc = func(n) { n = n + 1; }; print(inc(5)); }"))
  (run (parse-source "{ var res = begin var value = 3; value = value + 2; end; print(res); }"))
  (run (parse-source "{ var f = func(x) { return x * 2; }; print(f(4)); }"))
  (run (parse-source "{ var g = func() { return; }; print(g()); }"))
  (run (parse-source "{ var base = obj { x: 1 }; var copy = clone(base); print(copy); }"))
  (run (parse-source "{ var L = crear-lista(3, crear-lista(2, crear-lista(1, vacio))); print(lista?(L)); print(vacio?(crear-lista(0, vacio))); L = set-list(L, 1, 99); print(ref-list(L, 1)); print(append(L, crear-lista(0, vacio))); var D = crear-diccionario(\"id\", 101, \"nombre\", \"Ana\"); print(ref-diccionario(D, \"id\")); D = set-diccionario(D, \"nombre\", \"Ana Maria\"); print(claves(D)); print(valores(D)); }"))
  (run (parse-source "{ var numeros = [1, 2, 3]; var total = 0; for n in numeros do { total = total + n; } done print(total); }"))
  (run (parse-source "{ var a = 1, b = a + 2; const c = b, d = c + 3; print(d); }"))
  (run (parse-source "{ var saludo = concatenar(\"Flow\", \"Lang\"); print(saludo); print(longitud(saludo)); }"))
  (run (parse-source "{ var item = obj { valor: 0, inc: func() { this.valor = this.valor + 1; return this.valor; } }; print(item.inc()); print(item.valor); }"))

  (displayln "== Prueba 14: verdad dinámica (0, \"\", null) ==")
  (run '(program (block
                   (if 0 (print "no") (print "cero es falso"))
                   (if "" (print "no") (print "cadena vacia es falsa"))
                   (if null (print "no") (print "null es falso"))
                   (if "algo" (print "cadena no vacia es verdadera") (print "no"))
                   999)))

  (displayln "== Prueba 15: literales flotantes y complejos ==")
  (run (parse-source "{ var pi = 3.1415; var expo = 1.2e3; var enteroExpo = 2e-2; var c = 2 + 3i; var imag = 10i; var fracImag = 0.25i; print(pi); print(expo); print(enteroExpo); print(c); print(imag); print(fracImag); }"))
)
