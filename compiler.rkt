#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1) (pe-neg (pe-exp e2)))]
    ))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (lookup x env))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define new-x (gensym x))
       (Let new-x
            ((uniquify-exp env) e)
            ((uniquify-exp (extend-env env x new-x)) body))
       ]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : Lvar -> Lvar
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))


;; rco-atom : exp -> (values atom bindings)
;; Convert e to an atom, returning the temporary bindings needed for the conversion.
(define (rco-atom e)
  (define (atom-exp? e)
    (or (Int? e) (Var? e)))
  (cond
    [(atom-exp? e)
     (values e '())]
    [else
     (define tmp (gensym 'tmp))
     (values (Var tmp)
             (list (cons tmp (rco-exp e))))]))

;; rco-exp : exp -> exp^mon
;; Remove complex operands from e by introducing temporary Let bindings.
(define (rco-exp e)
  (define (rco-args es)
    (match es
      ['() (values '() '())]
      [(cons e rest)
       (define-values (atom bindings) (rco-atom e))
       (define-values (atoms rest-bindings) (rco-args rest))
       (values (cons atom atoms)
               (append bindings rest-bindings))]))
  (define (wrap-rco-bindings bindings body)
    (foldl (lambda (binding body)
             (Let (car binding) (cdr binding) body))
           body
           (reverse bindings)))
  (match e
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es)
     (define-values (atoms bindings) (rco-args es))
     (wrap-rco-bindings bindings (Prim op atoms))]))

;; remove-complex-opera* : Lvar -> Lvar^mon
(define (remove-complex-opera* p)
  (match p
    [(Program info e)
     (Program info (rco-exp e))]))


;; explicate-assign
(define (explicate-assign e x cont)
  (match e
    [(Var y)
     (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n)
     (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body)
     (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es)
     (Seq (Assign (Var x) (Prim op es)) cont)]
    [_ (error "explicate_assign unhandled case" e)]))

;; explicate-tail
(define (explicate-tail e)
  (match e
    [(Int n)
     (Return (Int n))]
    [(Var x)
     (Return (Var x))]
    [(Let x rhs body)
     (explicate-assign rhs x (explicate-tail body))]
    [(Prim op es)
     (Return (Prim op es))]
    [_ (error "explicate_tail unhandled case" e)]))

;; explicate-control : Lvar^mon -> Cvar
(define (explicate-control p)
  (match p
    [(Program info e)
     (CProgram info
               (list (cons 'start (explicate-tail e))))]))

;; select-instructions : Cvar -> x86var
(define (select-instructions p)
  (define (atm e)
    (match e
      [(Var var)
       (Var var)]
      [(Int n)
       (Imm n)]
      [_ (error "atm unhandled case" e)]))
  (define (stmt s)
    (match s
      [(Assign (Var x) (Int n))
       (list (Instr 'movq (list (Imm n) (Var x))))]
      [(Assign (Var x) (Var y))
       (list (Instr 'movq (list (Var y) (Var x))))]
      [(Assign (Var x) (Prim 'read '()))
       (list (Callq 'read_int 0)
             (Instr 'movq (list (Reg 'rax) (Var x))))]
      [(Assign (Var x) (Prim '+ (list (Var y) e2)))
       #:when (eq? x y)
       (list (Instr 'addq (list (atm e2) (Var x))))]
      [(Assign (Var x) (Prim '+ (list e1 (Var y))))
       #:when (eq? x y)
       (list (Instr 'addq (list (atm e1) (Var x))))]
      [(Assign (Var x) (Prim '+ (list e1 e2)))
       (list (Instr 'movq (list (atm e1) (Var x)))
             (Instr 'addq (list (atm e2) (Var x))))]
      [(Assign (Var x) (Prim '- (list e)))
       (list (Instr 'movq (list (atm e) (Var x)))
             (Instr 'negq (list (Var x))))]
      [(Assign (Var x) (Prim '- (list e1 e2)))
       (list (Instr 'movq (list (atm e1) (Var x)))
             (Instr 'subq (list (atm e2) (Var x))))]
      [_ (error "stmt unhandled case" s)]))
  (define (tail e)
    (match e
      [(Seq s t)
       (append (stmt s) (tail t))]
      [(Return (Int n))
       (list (Instr 'movq (list (Imm n) (Reg 'rax)))
             (Jmp 'conclusion))]
      [(Return (Var x))
       (list (Instr 'movq (list (Var x) (Reg 'rax)))
             (Jmp 'conclusion))]
      [(Return (Prim 'read '()))
       (list (Callq 'read_int 0)
             (Jmp 'conclusion))]
      [(Return (Prim '+ (list e1 e2)))
       (list (Instr 'movq (list (atm e1) (Reg 'rax)))
             (Instr 'addq (list (atm e2) (Reg 'rax)))
             (Jmp 'conclusion))]
      [(Return (Prim '- (list e)))
       (list (Instr 'movq (list (atm e) (Reg 'rax)))
             (Instr 'negq (list (Reg 'rax)))
             (Jmp 'conclusion))]
      [(Return (Prim '- (list e1 e2)))
       (list (Instr 'movq (list (atm e1) (Reg 'rax)))
             (Instr 'subq (list (atm e2) (Reg 'rax)))
             (Jmp 'conclusion))]
      [_ (error "tail unhandled case" e)]))
  (match p
    [(CProgram info (list (cons 'start block-tail)))
     (X86Program
       info
       (list (cons 'start (Block '() (tail block-tail)))))]))

;; assign-homes : x86var -> x86var
(define (assign-homes p)
  (match p
    [(X86Program info (list (cons 'start (Block block-info instructions))))
     (define locals-types (dict-ref info 'locals-types))
     (define homes
       (for/hash ([local-type (in-list locals-types)]
                  [index (in-naturals 1)])
         (values (car local-type) (* -8 index))))
     (define stack-space (align (* 8 (length locals-types)) 16))
     (define (home arg)
       (match arg
         [(Var x) (Deref 'rbp (hash-ref homes x))]
         [_ arg]))
     (define new-instructions
       (for/list ([instruction (in-list instructions)])
         (match instruction
           [(Instr name args)
            (Instr name (map home args))]
           [_ instruction])))
     (X86Program (dict-set info 'stack-space stack-space)
                 (list (cons 'start (Block block-info new-instructions))))]
    [_ (error 'assign-homes "expected an X86Program, got ~a" p)]))

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (match p
    [(X86Program info (list (cons 'start (Block block-info instructions))))
     (define (patched instr)
       (match instr
         [(Instr 'movq (list (Deref 'rbp src) (Deref 'rbp dst)))
          (list (Instr 'movq (list (Deref 'rbp src) (Reg 'rax)))
                (Instr 'movq (list (Reg 'rax) (Deref 'rbp dst))))]
         [(Instr 'addq (list (Deref 'rbp src) (Deref 'rbp dst)))
          (list (Instr 'movq (list (Deref 'rbp dst) (Reg 'rax)))
                (Instr 'addq (list (Deref 'rbp src) (Reg 'rax)))
                (Instr 'movq (list (Reg 'rax) (Deref 'rbp dst))))]
         [(Instr 'subq (list (Deref 'rbp src) (Deref 'rbp dst)))
          (list (Instr 'movq (list (Deref 'rbp dst) (Reg 'rax)))
                (Instr 'subq (list (Deref 'rbp src) (Reg 'rax)))
                (Instr 'movq (list (Reg 'rax) (Deref 'rbp dst))))]
         [_ (list instr)]))
     (define patched-all
       (append-map patched instructions))
     (X86Program info (list (cons 'start (Block block-info patched-all))))]))

;; prelude-and-conclusion : x86int -> x86int
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ;; Uncomment the following passes as you finish them.
    ("uniquify" ,uniquify ,interp_Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp_Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
    ("assign homes" ,assign-homes ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ))
