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
(require "priority_queue.rkt")
(require graph)
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
(define (pe-residual-parts r)
  (match r
    [(Int n) (values n #f)]
    [(Prim '+ (list (Int n) inert)) (values n inert)]
    [_ (values 0 r)]))

(define (pe-inert-add r1 r2)
  (cond
    [(not r1) r2]
    [(not r2) r1]
    [else (Prim '+ (list r1 r2))]))

(define (pe-neg r)
  (match r
    [(Int n)
     (define negated (- n))
     (if (fixnum? negated)
         (Int negated)
         (Prim '- (list r)))]
    [(Prim '+ (list (Int n) inert))
     (pe-add (pe-neg (Int n)) (pe-neg inert))]
    [(Prim '+ (list inert1 inert2))
     (pe-add (pe-neg inert1) (pe-neg inert2))]
    [(Prim '- (list inert)) inert]
    [(Let x rhs body)
     (Let x rhs (pe-neg body))]
    [_ (Prim '- (list r))]))

(define (pe-add r1 r2)
  (define-values (n1 inert1) (pe-residual-parts r1))
  (define-values (n2 inert2) (pe-residual-parts r2))
  (define n (+ n1 n2))
  (cond
    [(not (fixnum? n)) (Prim '+ (list r1 r2))]
    [else
     (define inert (pe-inert-add inert1 inert2))
     (cond
       [(not inert) (Int n)]
       [(zero? n) inert]
       [else (Prim '+ (list (Int n) inert))])]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-add (pe-exp e1) (pe-neg (pe-exp e2)))]
    [(Let x rhs body) (Let x (pe-exp rhs) (pe-exp body))]
    ))

(define (pe-Lvar p)
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

;; Liveness Analysis
(define (uncover-live p)
  (match p
    [(X86Program info (list (cons 'start (Block block-info instructions))))
     (define reverse-instructions (reverse instructions))
     (define (locations arg)
       (match arg
         [(Var x) (set x)]
         [(Reg r) (set r)]
         [_ (set)]))
     (define (destination-locations arg)
       (match arg
         [(Var x) (set x)]
         [(Reg r) (set r)]
         [_ (set)]))
     (define (call-argument-locations arity)
       (for/set ([i (in-range arity)])
         (vector-ref arg-registers i)))
     (define (R instruction)
       (match instruction
         [(Instr 'movq (list src dst))
          (locations src)]
         [(Instr (or 'addq 'subq) (list src dst))
          (set-union (locations src) (locations dst))]
         [(Instr 'negq (list dst))
          (locations dst)]
         [(Callq _ arity)
          (call-argument-locations arity)]
         [(Jmp _)
          (set)]
         [_ (error 'R "unsupported instruction: ~a" instruction)]))
     (define (W instruction)
       (match instruction
         [(Instr 'movq (list _ dst))
          (destination-locations dst)]
         [(Instr (or 'addq 'subq) (list _ dst))
          (destination-locations dst)]
         [(Instr 'negq (list dst))
          (destination-locations dst)]
         [(Callq _ _)
          caller-save]
         [(Jmp _)
          (set)]
         [_ (error 'W "unsupported instruction: ~a" instruction)]))
     (define (live-before live-after instruction)
       (set-union (set-subtract live-after (W instruction)) (R instruction)))
     (define live-sets
       (for/fold ([live-sets (list (set))])
                 ([instruction (in-list reverse-instructions)])
         (cons (live-before (car live-sets) instruction)
               live-sets)))
     (define lives (cdr live-sets))
     (X86Program
       info
       (list (cons 'start
                   (Block (dict-set block-info 'lives lives)
                          instructions))))]))

;; build_interference
(define (build-interference p)
  (match p
    [(X86Program info (list (cons 'start (Block block-info instructions))))
     (define lives (dict-ref block-info 'lives))
     (define g (unweighted-graph/undirected '()))
     (unless (= (length instructions) (length lives))
       (error 'build-interference
              "expected one live-after set per instruction, got ~a instructions and ~a live sets"
              (length instructions)
              (length lives)))
     (define (locations arg)
       (match arg
         [(or (Var x) (Reg x)) (set x)]
         [_ (set)]))
     (define (writes instruction)
       (match instruction
         [(Instr (or 'movq 'addq 'subq) (list _ dst))
          (locations dst)]
         [(Instr 'negq (list dst))
          (locations dst)]
         [(Callq _ _) caller-save]
         [(Jmp _) (set)]
         [_ (error 'build-interference
                   "unsupported instruction: ~a"
                   instruction)]))
     (define (build-one-instruction instruction live-after)
       (define written-locations (writes instruction))
       (define (add-conflicts! destinations excluded-live)
         (for* ([d (in-set destinations)]
                [v (in-set live-after)]
                #:unless (or (equal? v d)
                             (set-member? excluded-live v)))
           (add-edge! g d v)))
       (match instruction
         [(Instr 'movq (list src dst))
          (add-conflicts! (locations dst) (locations src))]
         [_
          (add-conflicts! written-locations (set))]))
     (for ([local-type (in-list (dict-ref info 'locals-types))])
       (add-vertex! g (car local-type)))
     (for ([instruction (in-list instructions)]
           [live-after (in-list lives)])
       (build-one-instruction instruction live-after))
     (X86Program (dict-set info 'conflicts g)
                 (list (cons 'start (Block block-info instructions))))]
    [_ (error 'build-interference
              "expected an X86Program with a start block, got ~a"
              p)]))

;; Map graph-coloring colors to their corresponding registers.
(define (color->register-symbol color)
  (case color
    [(0) 'rcx]
    [(1) 'rdx]
    [(2) 'rsi]
    [(3) 'rdi]
    [(4) 'r8]
    [(5) 'r9]
    [(6) 'r10]
    [(7) 'rbx]
    [(8) 'r12]
    [(9) 'r13]
    [(10) 'r14]
    [(-1) 'rax]
    [(-2) 'rsp]
    [(-3) 'rbp]
    [(-4) 'r11]
    [(-5) 'r15]
    [else
     (error 'color->register-symbol "unsupported color: ~a" color)]))

;; Color variables using DSATUR, treating physical registers as precolored.
(define (color-graph graph variables)
  (define vars (remove-duplicates variables))
  (define vars-set (list->set vars))
  (define graph-vertices (list->set (get-vertices graph)))
  (define (neighbors vertex)
    (if (set-member? graph-vertices vertex)
        (get-neighbors graph vertex)
        '()))
  (define (precolored-color vertex)
    (for/first ([color (in-range -5 11)]
                #:when (eq? vertex (color->register-symbol color)))
      color))
  (define tie-breakers
    (for/hash ([vertex (in-list (shuffle vars))]
               [rank (in-naturals)])
      (values vertex rank)))
  (define (priority<=? a b)
    (or (< (vector-ref a 0) (vector-ref b 0))
        (and (= (vector-ref a 0) (vector-ref b 0))
             (<= (vector-ref a 1) (vector-ref b 1)))))
  (define queue (make-pqueue priority<=?))
  (define colors (make-hash))
  (define saturating-colors (make-hash))
  (define queue-nodes (make-hash))
  (for ([vertex (in-list vars)])
    (define initial-colors
      (for/fold ([seen (set)])
                ([neighbor (in-list (neighbors vertex))]
                 #:unless (set-member? vars-set neighbor))
        (define fixed-color (precolored-color neighbor))
        (if fixed-color (set-add seen fixed-color) seen)))
    (hash-set! saturating-colors vertex initial-colors)
    (hash-set! queue-nodes vertex
               (pqueue-push!
                 queue
                 (vector (- (set-count initial-colors))
                         (hash-ref tie-breakers vertex)
                         vertex))))
  (let color-next ()
    (unless (zero? (pqueue-count queue))
      (define entry (pqueue-pop! queue))
      (define vertex (vector-ref entry 2))
      (define used-colors (hash-ref saturating-colors vertex))
      (define color
        (let find-color ([candidate 0])
          (if (set-member? used-colors candidate)
              (find-color (add1 candidate))
              candidate)))
      (hash-set! colors vertex color)
      (for ([neighbor (in-list (neighbors vertex))]
            #:when (and (set-member? vars-set neighbor)
                        (not (hash-has-key? colors neighbor))))
        (define old-colors (hash-ref saturating-colors neighbor))
        (unless (set-member? old-colors color)
          (define new-colors (set-add old-colors color))
          (hash-set! saturating-colors neighbor new-colors)
          (define node (hash-ref queue-nodes neighbor))
          (set-node-key!
            node
            (vector (- (set-count new-colors))
                    (hash-ref tie-breakers neighbor)
                    neighbor))
          (pqueue-decrease-key! queue node)))
      (color-next)))
  (for/hash ([vertex (in-list vars)])
    (values vertex (hash-ref colors vertex))))

;; Allocate variables to registers or stack slots using DSATUR coloring.
(define (allocate-registers p)
  (match p
    [(X86Program info (list (cons 'start (Block block-info instructions))))
     (define live-program (uncover-live p))
     (define interference-program (build-interference live-program))
     (define locals-types (dict-ref info 'locals-types))
     (define variables (map car locals-types))
     (define conflicts (dict-ref (X86Program-info interference-program)
                                 'conflicts))
     (define colors (color-graph conflicts variables))
     (define allocatable-callee
       (callee-save-for-alloc))
     (define used-callee
       (for/fold ([used (set)])
                 ([variable (in-list variables)])
         (define color (hash-ref colors variable))
         (if (< color (vector-length general-registers))
             (let ([register (color->register-symbol color)])
               (if (set-member? allocatable-callee register)
                   (set-add used register)
                   used))
             used)))
     (define used-callee-count (set-count used-callee))
     (define max-spill-slot
       (for/fold ([max-slot 0])
                 ([variable (in-list variables)])
         (define color (hash-ref colors variable))
         (if (>= color (vector-length general-registers))
             (max max-slot (- color (sub1 (vector-length general-registers))))
             max-slot)))
     (define homes
       (for/hash ([variable (in-list variables)])
         (define color (hash-ref colors variable))
         (values variable
                 (if (<= color (sub1 (vector-length general-registers)))
                     (Reg (color->register-symbol color))
                     (Deref 'rbp
                            (* -8 (+ used-callee-count
                                     (- color
                                        (sub1 (vector-length general-registers))))))))))
     (define (home arg)
       (match arg
         [(Var variable) (hash-ref homes variable)]
         [_ arg]))
     (define new-instructions
       (for/list ([instruction (in-list instructions)])
         (match instruction
           [(Instr name args)
            (Instr name (map home args))]
           [_ instruction])))
     (define stack-space
       (- (align (* 8 (+ max-spill-slot used-callee-count)) 16)
          (* 8 used-callee-count)))
     (X86Program (dict-set (dict-set info 'stack-space stack-space)
                           'used-callee
                           used-callee)
                 (list (cons 'start
                             (Block block-info new-instructions))))]
    [_ (error 'allocate-registers
              "expected an X86Program with a start block, got ~a"
              p)]))

#| 
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
|#

;; patch-instructions : x86var -> x86int
(define (patch-instructions p)
  (match p
    [(X86Program info (list (cons 'start (Block block-info instructions))))
     (define (patched instr)
       (match instr
         [(Instr 'movq (list src dst))
          #:when (equal? src dst)
          '()]
         [(Instr name (list (Imm n) (Deref reg offset)))
          #:when (or (>= n (expt 2 31))
                     (< n (- (expt 2 31))))
          (list (Instr 'movq (list (Imm n) (Reg 'rax)))
                (Instr name (list (Reg 'rax) (Deref reg offset))))]
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
  (match p
    [(X86Program info (list (cons 'start start-block)))
     (define stack-space (dict-ref info 'stack-space))
     (define used-callee (dict-ref info 'used-callee (set)))
     (define ordered-callee
       (for/list ([register (in-vector general-registers)]
                  #:when (set-member? used-callee register))
         register))
     (define prelude
       (Block '()
              (append (list
                       (Instr 'pushq (list (Reg 'rbp)))
                       (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                      (for/list ([register (in-list ordered-callee)])
                        (Instr 'pushq (list (Reg register))))
                      (list
                       (Instr 'subq (list (Imm stack-space) (Reg 'rsp)))
                       (Jmp 'start)))))
     (define conclusion
       (Block '()
              (append (list
                       (Instr 'addq (list (Imm stack-space) (Reg 'rsp))))
                      (for/list ([register (in-list (reverse ordered-callee))])
                        (Instr 'popq (list (Reg register))))
                      (list
                       (Instr 'popq (list (Reg 'rbp)))
                       (Retq)))))
     (X86Program info (list (cons 'main prelude) (cons 'start start-block) (cons 'conclusion conclusion)))]
    [_ (error 'prelude-and-conclusion "expected an X86Program with a start block, got ~a" p)]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ;; Uncomment the following passes as you finish them.
    ("partial evaluator" ,pe-Lvar ,interp_Lvar ,type-check-Lvar)
    ("uniquify" ,uniquify ,interp_Lvar ,type-check-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp_Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-0)
    ("allocate registers" ,allocate-registers ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ))
