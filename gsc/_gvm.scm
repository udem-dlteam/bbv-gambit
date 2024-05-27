;;;============================================================================

;;; File: "_gvm.scm"

;;; Copyright (c) 1994-2022 by Marc Feeley, All Rights Reserved.

(include "fixnum.scm")

(include-adt "_envadt.scm")
(include     "_gvmadt.scm")
(include-adt "_ptreeadt.scm")
(include-adt "_sourceadt.scm")

(##include "../gsc/bfs.scm")

(define (pprint val)
  (##namespace ("" pp))
  (pp val))

;;;----------------------------------------------------------------------------
;;
;; Gambit virtual machine abstraction module:
;; -----------------------------------------

;; (See file 'doc/gvm' for details on the virtual machine)

(define return-addr-reg (make-reg 0)) ;; register used to pass return address

;; Utilities:
;; ---------

(define *opnd-table* #f)
(define *opnd-table-alloc* #f)

(define (extend-opnd-table!)
  (let* ((n (vector-length *opnd-table*))
         (new-table (make-vector (+ (quotient (* 3 n) 2) 1) #f)))
    (let loop ((i 0))
      (if (< i n)
        (begin
          (vector-set! new-table i (vector-ref *opnd-table* i))
          (loop (+ i 1)))
        (set! *opnd-table* new-table)))))

(define (enter-opnd arg1 arg2)
  (let loop ((i 0))
    (if (< i *opnd-table-alloc*)
      (let ((x (vector-ref *opnd-table* i)))
        (if (and (eqv? (car x) arg1) (eqv? (cdr x) arg2))
          i
          (loop (+ i 1))))
      (begin
        (set! *opnd-table-alloc* (+ *opnd-table-alloc* 1))
        (if (> *opnd-table-alloc* (vector-length *opnd-table*))
          (extend-opnd-table!))
        (vector-set! *opnd-table* i (cons arg1 arg2))
        i))))

(define (contains-opnd? opnd1 opnd2) ; does opnd2 contain opnd1?
  (cond ((eqv? opnd1 opnd2)
         #t)
        ((clo? opnd2)
         (contains-opnd? opnd1 (clo-base opnd2)))
        (else
         #f)))

(define (any-contains-opnd? opnd opnds)
  (if (null? opnds)
    #f
    (or (contains-opnd? opnd (car opnds))
        (any-contains-opnd? opnd (cdr opnds)))))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Processor context descriptions:
;; ------------------------------

(define (make-pcontext fs map)
  (vector fs map))

(define (pcontext-fs  x) (vector-ref x 0))
(define (pcontext-map x) (vector-ref x 1))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Frame description:
;; -----------------

(define (make-frame size slots regs closed live)
  (vector size slots regs closed live))

(define (frame-size x)   (vector-ref x 0))
(define (frame-slots x)  (vector-ref x 1))
(define (frame-regs x)   (vector-ref x 2))
(define (frame-closed x) (vector-ref x 3))
(define (frame-live x)   (vector-ref x 4))

(define (frame-eq? frame1 frame2)

  ; two frames are "equal" if they have the same number of slots and
  ; for all slots and registers in a frame the corresponding slot or
  ; register in the other frame has the same liveness and the return
  ; address is in the same place.

  (define (same-liveness? var1 var2)
    (eq? (varset-member? var1 (frame-live frame1))
         (varset-member? var2 (frame-live frame2))))

  (define (same-liveness-list? lst1 lst2)
    (if (pair? lst1)
      (let ((var1 (car lst1)))
        (if (pair? lst2)
          (let ((var2 (car lst2)))
            (and (eq? (eq? var1 ret-var) (eq? var2 ret-var))
                 (same-liveness? var1 var2)
                 (same-liveness-list? (cdr lst1) (cdr lst2))))
          (and (same-liveness? var1 empty-var)
               (same-liveness-list? (cdr lst1) lst2))))
      (if (pair? lst2)
        (let ((var2 (car lst2)))
          (and (same-liveness? empty-var var2)
               (same-liveness-list? lst1 (cdr lst2))))
        #t)))

  (and (= (frame-size frame1) (frame-size frame2))
       (let ((slots1 (frame-slots frame1))
             (slots2 (frame-slots frame2)))
         (same-liveness-list? slots1 slots2))
       (let ((regs1 (frame-regs frame1))
             (regs2 (frame-regs frame2)))
         (same-liveness-list? regs1 regs2))))

(define (frame-truncate frame nb-slots)
  (let ((fs (frame-size frame)))
    (make-frame nb-slots
                (drop (frame-slots frame) (- fs nb-slots))
                (frame-regs frame)
                (frame-closed frame)
                (frame-live frame))))

(define (types-truncate types frame)
  (and types
       (locenv-resize
        types
        (length (frame-regs frame))
        (length (frame-slots frame))
        (length (frame-closed frame))
        0
        #f)))

(define (types-keep-topmost-slots types topmost-slots)
  (locenv-keep-topmost-slots types topmost-slots #f))

(define (frame-live? var frame)
  (let ((live (frame-live frame)))
    (if (eq? var closure-env-var)
      (let ((closed (frame-closed frame)))
        (if (or (varset-member? var live)
                (varset-intersects? live (list->varset closed)))
          closed
          #f))
      (if (varset-member? var live)
        var
        #f))))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Procedure objects:
;; -----------------

(define (make-proc-obj
          name
          c-name
          primitive?
          code
          call-pat
          side-effects?
          strict-pat
          lift-pat
          type
          standard)
  (let ((proc-obj
          (vector
            proc-obj-tag
            name
            c-name
            primitive?
            code
            call-pat
            (lambda (env) #f) ;; testable?
            #f ;; test
            (lambda (env) #f) ;; expandable?
            #f ;; expand
            (lambda (env) #f) ;; inlinable?
            #f ;; inline
            (lambda (env) #f) ;; jump-inlinable?
            #f ;; jump-inline
            #f ;; specialize
            #f ;; simplify
            #f ;; type-infer
            #f ;; type-narrow
            side-effects?
            strict-pat
            lift-pat
            type
            standard
            #f))) ;; dead-end?
    (proc-obj-specialize-set! proc-obj (lambda (env call) call))
    proc-obj))

(define proc-obj-tag (list 'proc-obj))

(define (proc-obj? x)
  (and (vector? x)
       (> (vector-length x) 0)
       (eq? (vector-ref x 0) proc-obj-tag)))

(define (proc-obj-name obj)                   (vector-ref obj 1))
(define (proc-obj-c-name obj)                 (vector-ref obj 2))
(define (proc-obj-primitive? obj)             (vector-ref obj 3))
(define (proc-obj-code obj)                   (vector-ref obj 4))
(define (proc-obj-call-pat obj)               (vector-ref obj 5))
(define (proc-obj-testable? obj)              (vector-ref obj 6))
(define (proc-obj-test obj)                   (vector-ref obj 7))
(define (proc-obj-expandable? obj)            (vector-ref obj 8))
(define (proc-obj-expand obj)                 (vector-ref obj 9))
(define (proc-obj-inlinable? obj)             (vector-ref obj 10))
(define (proc-obj-inline obj)                 (vector-ref obj 11))
(define (proc-obj-jump-inlinable? obj)        (vector-ref obj 12))
(define (proc-obj-jump-inline obj)            (vector-ref obj 13))
(define (proc-obj-specialize obj)             (vector-ref obj 14))
(define (proc-obj-simplify obj)               (vector-ref obj 15))
(define (proc-obj-type-infer obj)             (vector-ref obj 16))
(define (proc-obj-type-narrow obj)            (vector-ref obj 17))

(define (proc-obj-side-effects? obj)          (vector-ref obj 18))
(define (proc-obj-strict-pat obj)             (vector-ref obj 19))
(define (proc-obj-lift-pat obj)               (vector-ref obj 20))
(define (proc-obj-type obj)                   (vector-ref obj 21))
(define (proc-obj-standard obj)               (vector-ref obj 22))
(define (proc-obj-dead-end? obj)              (vector-ref obj 23))
(define (proc-obj-name-set! obj x)            (vector-set! obj 1 x))
(define (proc-obj-c-name-set! obj x)          (vector-set! obj 2 x))
(define (proc-obj-primitive?-set! obj x)      (vector-set! obj 3 x))
(define (proc-obj-code-set! obj x)            (vector-set! obj 4 x))
(define (proc-obj-call-pat-set! obj x)        (vector-set! obj 5 x))
(define (proc-obj-testable?-set! obj x)       (vector-set! obj 6 x))
(define (proc-obj-test-set! obj x)            (vector-set! obj 7 x))
(define (proc-obj-expandable?-set! obj x)     (vector-set! obj 8 x))
(define (proc-obj-expand-set! obj x)          (vector-set! obj 9 x))
(define (proc-obj-inlinable?-set! obj x)      (vector-set! obj 10 x))
(define (proc-obj-inline-set! obj x)          (vector-set! obj 11 x))
(define (proc-obj-jump-inlinable?-set! obj x) (vector-set! obj 12 x))
(define (proc-obj-jump-inline-set! obj x)     (vector-set! obj 13 x))
(define (proc-obj-specialize-set! obj x)      (vector-set! obj 14 x))
(define (proc-obj-simplify-set! obj x)        (vector-set! obj 15 x))
(define (proc-obj-type-infer-set! obj x)      (vector-set! obj 16 x))
(define (proc-obj-type-narrow-set! obj x)     (vector-set! obj 17 x))
(define (proc-obj-side-effects?-set! obj x)   (vector-set! obj 18 x))
(define (proc-obj-strict-pat-set! obj x)      (vector-set! obj 19 x))
(define (proc-obj-lift-pat-set! obj x)        (vector-set! obj 20 x))
(define (proc-obj-type-set! obj x)            (vector-set! obj 21 x))
(define (proc-obj-standard-set! obj x)        (vector-set! obj 22 x))
(define (proc-obj-dead-end?-set! obj x)       (vector-set! obj 23 x))

(define (make-pattern nb-parms nb-opts nb-keys rest?)
  (let* ((max-pos-args (- nb-parms nb-keys (if rest? 1 0)))
         (min-args (- max-pos-args nb-opts)))
    (let loop ((i
                (- max-pos-args 1))
               (pattern
                (if (or (> nb-keys 0) rest?)
                  max-pos-args
                  (list max-pos-args))))
      (if (>= i min-args)
        (loop (- i 1) (cons i pattern))
        pattern))))

(define (pattern-member? n pat) ; tests if 'n' is a member of pattern 'pat'
  (cond ((pair? pat)
         (if (= (car pat) n) #t (pattern-member? n (cdr pat))))
        ((null? pat)
         #f)
        (else
         (<= pat n))))

(define (type-name type)
  (if (pair? type) (car type) type))

(define (type-pot-fut? type)
  (pair? type))

;; for representing procedure calls for specialization

(define (make-call proc args) (cons proc args))
(define (call-proc call) (car call))
(define (call-args call) (cdr call))

(define (make-call-arg val) (list val))
(define (call-arg-val x) (car x))

(define (fold-call-args old-args new-args init proc)

  (define (fold-args n-args o-args o-args-pos)
    (if (pair? n-args)
        (let ((n-arg (car n-args)))
          (proc n-arg
                (if (and (pair? o-args) (eq? (car o-args) n-arg))
                    o-args-pos ;; optimize common case
                    (pos-in-list n-arg old-args))
                (fold-args (cdr n-args)
                           (if (pair? o-args) (cdr o-args) o-args)
                           (+ o-args-pos 1))))
        init))

  (fold-args new-args old-args 0))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Label objects:
;; -------------

(define (make-lbl-obj lbl new-lbl kind types)
  (let ((lbl-obj
         (vector
          lbl-obj-tag
          lbl
          new-lbl
          kind
          types)))
    lbl-obj))

(define lbl-obj-tag (list 'lbl-obj))

(define (lbl-obj? x)
  (and (vector? x)
       (> (vector-length x) 0)
       (eq? (vector-ref x 0) lbl-obj-tag)))

(define (lbl-obj-lbl obj)     (vector-ref obj 1))
(define (lbl-obj-new-lbl obj) (vector-ref obj 2))
(define (lbl-obj-kind obj)    (vector-ref obj 3)) ;; TODO: store reference to bbs
(define (lbl-obj-types obj)   (vector-ref obj 4))

(define (lbl-obj-eqv? lbl-obj1 lbl-obj2)
  (eqv? (lbl-obj-new-lbl lbl-obj1)
        (lbl-obj-new-lbl lbl-obj2)))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Basic block set manipulation:
;; ----------------------------

;; Virtual instructions have a linear structure.  However, this is not
;; how they are put together to form a piece of code.  Rather, virtual
;; instructions are grouped into 'basic blocks' which are 'linked'
;; together.  A basic block is a 'label' instruction followed by a
;; sequence of non-branching instructions (i.e. 'apply', 'copy' or
;; 'close') terminated by a single branch instruction (i.e. 'ifjump',
;; 'jump' or 'switch').  Links between basic blocks are denoted using
;; label references.  When a basic block ends with an 'ifjump'
;; instruction, the block is linked to the two basic blocks
;; corresponding to the two possible control paths out of the 'ifjump'
;; instruction.  When a basic block ends with a 'switch' instruction, the
;; block is linked to as many basic blocks as there are cases and the
;; default.  When a basic block ends with a 'jump' instruction, there
;; is either zero or one link.
;;
;; Basic blocks naturally group together to form 'basic block sets'.  A
;; basic block set describes all the code of a procedure.

(define (make-bbs)
  (set! transform-to-case? #f) ;; TODO: remove
  (vector bbs-tag
          bbs-first-lbl                ;; 1 - next assignable label number
          (make-stretchable-vector #f) ;; 2 - vector of basic blocks
          #f))                         ;; 3 - entry label number

(define bbs-first-lbl 1)

(define bbs-tag (list 'bbs))

(define (bbs? x)
  (and (vector? x)
       (> (vector-length x) 0)
       (eq? (vector-ref x 0) bbs-tag)))

(define (bbs-next-lbl-num bbs)             (vector-ref bbs 1))
(define (bbs-next-lbl-num-set! bbs lbl)    (vector-set! bbs 1 lbl))
(define (bbs-basic-blocks bbs)             (vector-ref bbs 2))
(define (bbs-basic-blocks-set! bbs blocks) (vector-set! bbs 2 blocks))
(define (bbs-entry-lbl-num bbs)            (vector-ref bbs 3))
(define (bbs-entry-lbl-num-set! bbs lbl)   (vector-set! bbs 3 lbl))

(define (bbs-for-each-bb proc bbs)
  (stretchable-vector-for-each
    (lambda (bb i) (if bb (proc bb)))
    (bbs-basic-blocks bbs)))

(define (bbs-bb-remove! bbs lbl)
  (stretchable-vector-set! (bbs-basic-blocks bbs) lbl #f))

(define (bbs-new-lbl! bbs)
  ;; NOTE: its very important that lbl remain increasing, as this is used to
  ;; compare the age of blocks in merges
  (let ((n (bbs-next-lbl-num bbs)))
    (bbs-next-lbl-num-set! bbs (+ n 1))
    n))

(define (lbl-num->bb lbl bbs)
  (stretchable-vector-ref (bbs-basic-blocks bbs) lbl))

;; Basic block manipulation procedures:

(define (make-bb label-instr bbs)
  (let ((lbl (label-lbl-num label-instr))
        (bb (vector
              label-instr   ; 0 - 'label' instr
              (queue-empty) ; 1 - sequence of non-branching instrs
              '()           ; 2 - branch instruction
              '()           ; 3 - basic blocks referenced by this block
              '())))        ; 4 - basic blocks which jump to this block
                            ;     (both filled in by 'bbs-purify')
    (stretchable-vector-set!
      (bbs-basic-blocks bbs)
      lbl
      bb)
    bb))

(define (bb-lbl-num bb)                  (label-lbl-num (vector-ref bb 0)))
(define (bb-label-kind bb)               (label-kind (vector-ref bb 0)))
(define (bb-label-instr bb)              (vector-ref bb 0))
(define (bb-label-instr-set! bb l)       (vector-set! bb 0 l))
(define (bb-non-branch-instrs bb)        (queue->list (vector-ref bb 1)))
(define (bb-non-branch-instrs-set! bb l) (vector-set! bb 1 (list->queue l)))
(define (bb-branch-instr bb)             (vector-ref bb 2))
(define (bb-branch-instr-set! bb b)      (vector-set! bb 2 b))
(define (bb-references bb)               (vector-ref bb 3))
(define (bb-references-set! bb l)        (vector-set! bb 3 l))
(define (bb-precedents bb)               (vector-ref bb 4))
(define (bb-precedents-set! bb l)        (vector-set! bb 4 l))

(define (bb-entry-frame-size bb)
  (frame-size (gvm-instr-frame (bb-label-instr bb))))

(define (bb-entry-nb-params bb)
  (let ((lbl (bb-label-instr bb)))
    (if (eq? (label-kind lbl) 'entry)
      (label-entry-nb-parms lbl)
      #f)))

(define (bb-exit-frame-size bb)
  (frame-size (gvm-instr-frame (bb-branch-instr bb))))

(define (bb-slots-gained bb)
  (- (bb-exit-frame-size bb) (bb-entry-frame-size bb)))

(define (bb-put-non-branch! bb gvm-instr)
  (queue-put! (vector-ref bb 1) gvm-instr))

(define (bb-put-branch! bb gvm-instr)
  (vector-set! bb 2 gvm-instr))

(define (bb-add-reference! bb lbl)
  (if (not (memv lbl (vector-ref bb 3)))
      (vector-set! bb 3 (cons lbl (vector-ref bb 3))))
  lbl)

(define (bb-add-precedent! bb lbl)
  (if (not (memv lbl (vector-ref bb 4)))
      (vector-set! bb 4 (cons lbl (vector-ref bb 4))))
  lbl)

(define (bb-last-non-branch-instr bb)
  (let ((non-branch-instrs (bb-non-branch-instrs bb)))
    (if (null? non-branch-instrs)
        (bb-label-instr bb)
        (let loop ((lst non-branch-instrs))
          (if (pair? (cdr lst))
              (loop (cdr lst))
              (car lst))))))

;; Virtual machine instruction representation:

(define (gvm-instr-kind gvm-instr)    (vector-ref gvm-instr 0))
(define (gvm-instr-frame gvm-instr)   (vector-ref gvm-instr 1))
(define (gvm-instr-types gvm-instr)   (vector-ref gvm-instr 2))
(define (gvm-instr-types-set! gvm-instr x) (vector-set! gvm-instr 2 x))
(define (gvm-instr-comment gvm-instr) (vector-ref gvm-instr 3))
(define (gvm-instr-comment-set! gvm-instr x) (vector-set! gvm-instr 3 x))

(define (gvm-instr-types-set!-returning-instr gvm-instr x)
  (gvm-instr-types-set! gvm-instr x)
  gvm-instr)

(define (gvm-instr-copy-types! gvm-instr1 gvm-instr2)
  (gvm-instr-types-set!-returning-instr
   gvm-instr2
   (gvm-instr-types gvm-instr1)))

(define (make-label-simple lbl-num frame comment)
  (vector 'label frame #f comment lbl-num 'simple))

(define (make-label-entry lbl-num nb-parms opts keys rest? closed? frame comment)
  (vector 'label frame #f comment lbl-num 'entry nb-parms opts keys rest? closed?))

(define (make-label-return lbl-num frame comment)
  (vector 'label frame #f comment lbl-num 'return))

(define (make-label-task-entry lbl-num frame comment)
  (vector 'label frame #f comment lbl-num 'task-entry))

(define (make-label-task-return lbl-num frame comment)
  (vector 'label frame #f comment lbl-num 'task-return))

(define (label-lbl-num gvm-instr)        (vector-ref gvm-instr 4))
(define (label-lbl-num-set! gvm-instr n) (vector-set! gvm-instr 4 n))
(define (label-kind gvm-instr)           (vector-ref gvm-instr 5))

(define (label-entry-nb-parms gvm-instr) (vector-ref gvm-instr 6))
(define (label-entry-opts gvm-instr)     (vector-ref gvm-instr 7))
(define (label-entry-keys gvm-instr)     (vector-ref gvm-instr 8))
(define (label-entry-rest? gvm-instr)    (vector-ref gvm-instr 9))
(define (label-entry-closed? gvm-instr)  (vector-ref gvm-instr 10))

(define (make-apply prim opnds loc frame comment)
  (vector 'apply frame #f comment prim opnds loc))
(define (apply-prim gvm-instr)  (vector-ref gvm-instr 4))
(define (apply-opnds gvm-instr) (vector-ref gvm-instr 5))
(define (apply-loc gvm-instr)   (vector-ref gvm-instr 6))

(define (make-copy opnd loc frame comment)
  (vector 'copy frame #f comment opnd loc))

(define (copy-opnd gvm-instr) (vector-ref gvm-instr 4))
(define (copy-loc gvm-instr)  (vector-ref gvm-instr 5))

(define (make-close parms frame comment)
  (vector 'close frame #f comment parms))
(define (close-parms gvm-instr) (vector-ref gvm-instr 4))

(define (make-closure-parms loc lbl opnds)
  (vector loc lbl opnds))
(define (closure-parms-loc x)   (vector-ref x 0))
(define (closure-parms-lbl x)   (vector-ref x 1))
(define (closure-parms-opnds x) (vector-ref x 2))

(define (make-ifjump test opnds true false poll? frame comment)
  (vector 'ifjump frame #f comment test opnds true false poll?))
(define (ifjump-test gvm-instr)  (vector-ref gvm-instr 4))
(define (ifjump-opnds gvm-instr) (vector-ref gvm-instr 5))
(define (ifjump-true gvm-instr)  (vector-ref gvm-instr 6))
(define (ifjump-false gvm-instr) (vector-ref gvm-instr 7))
(define (ifjump-poll? gvm-instr) (vector-ref gvm-instr 8))

(define (make-switch opnd cases default poll? frame comment)
  (vector 'switch frame #f comment opnd cases default poll?))
(define (switch-opnd gvm-instr)    (vector-ref gvm-instr 4))
(define (switch-cases gvm-instr)   (vector-ref gvm-instr 5))
(define (switch-default gvm-instr) (vector-ref gvm-instr 6))
(define (switch-poll? gvm-instr)   (vector-ref gvm-instr 7))

(define (make-switch-case obj lbl) (cons obj lbl))
(define (switch-case-obj switch-case) (car switch-case))
(define (switch-case-lbl switch-case) (cdr switch-case))

(define (make-jump opnd ret nb-args poll? safe? frame comment)
  (vector 'jump frame #f comment opnd ret nb-args poll? safe?))
(define (jump-opnd gvm-instr)    (vector-ref gvm-instr 4))
(define (jump-ret gvm-instr)     (vector-ref gvm-instr 5))
(define (jump-nb-args gvm-instr) (vector-ref gvm-instr 6))
(define (jump-poll? gvm-instr)   (vector-ref gvm-instr 7))
(define (jump-safe? gvm-instr)   (vector-ref gvm-instr 8))
(define (first-class-jump? gvm-instr) (jump-nb-args gvm-instr))

(define (gvm-instr-branch? gvm-instr)
  (case (gvm-instr-kind gvm-instr)
    ((ifjump switch jump)
     #t)
    (else
     #f)))

(define (make-comment)
  (cons 'comment '()))

(define (comment-put! comment name value)
  (set-cdr! comment (cons (cons name value) (cdr comment))))

(define (comment-get comment name)
  (and comment
       (let ((x (assq name (cdr comment))))
         (if x (cdr x) #f))))

(define (instr-comment-add! gvm-instr name val)
  (gvm-instr-comment-set!
   gvm-instr
   (cons 'comment
         (cons (cons name val) (cdr (gvm-instr-comment gvm-instr))))))

(define (instr-comment-get gvm-instr name)
  (comment-get (gvm-instr-comment gvm-instr) name))

;; Cloning of basic blocks.

(define (bb-clone bb bbs)
  (let ((new-bb (make-bb (bb-label-instr bb) bbs)))
    (bb-non-branch-instrs-set! new-bb (bb-non-branch-instrs bb))
    (bb-branch-instr-set! new-bb (bb-branch-instr bb))
    new-bb))

(define (bb-clone-replacing-lbls bb bbs replacement-lbl-num update-label-instr?)

  (let ((new-bb
         (make-bb (if update-label-instr?
                      (gvm-instr-clone-replacing-lbls
                       (bb-label-instr bb)
                       replacement-lbl-num)
                      (bb-label-instr bb))
                  bbs)))

    (define (clone instr)
      (gvm-instr-clone-replacing-lbls instr replacement-lbl-num))

    (bb-non-branch-instrs-set! new-bb (map clone (bb-non-branch-instrs bb)))

    (bb-branch-instr-set! new-bb (clone (bb-branch-instr bb)))

    new-bb))

(define (gvm-instr-clone-replacing-lbls instr replacement-lbl-num)

  (define (clone-gvm-opnd opnd)
    (if opnd
        (cond ((lbl? opnd)
               (make-lbl (replacement-lbl-num (lbl-num opnd))))
              ((clo? opnd)
               (make-clo (clone-gvm-opnd (clo-base opnd)) (clo-index opnd)))
              (else
               opnd))
        opnd))

  (define (clone-closure-parms p)
    (make-closure-parms
     (clone-gvm-opnd (closure-parms-loc p))
     (replacement-lbl-num (closure-parms-lbl p))
     (map clone-gvm-opnd (closure-parms-opnds p))))

  (define (clone-instr instr)
    (case (gvm-instr-kind instr)

      ((label)
       (case (label-kind instr)

         ((simple)
          (make-label-simple
           (replacement-lbl-num (label-lbl-num instr))
           (gvm-instr-frame instr)
           (gvm-instr-comment instr)))

         ((entry)
          (make-label-entry
           (replacement-lbl-num (label-lbl-num instr))
           (label-entry-nb-parms instr)
           (label-entry-opts instr)
           (label-entry-keys instr)
           (label-entry-rest? instr)
           (label-entry-closed? instr)
           (gvm-instr-frame instr)
           (gvm-instr-comment instr)))

         ((return)
          (make-label-return
           (replacement-lbl-num (label-lbl-num instr))
           (gvm-instr-frame instr)
           (gvm-instr-comment instr)))

         ((task-entry)
          (make-label-task-entry
           (replacement-lbl-num (label-lbl-num instr))
           (gvm-instr-frame instr)
           (gvm-instr-comment instr)))

         ((task-return)
          (make-label-task-return
           (replacement-lbl-num (label-lbl-num instr))
           (gvm-instr-frame instr)
           (gvm-instr-comment instr)))

         (else
          (compiler-internal-error
           "gvm-instr-clone-replacing-lbls, unknown 'instr':" instr))))

      ((apply)
       (make-apply
        (apply-prim instr)
        (map clone-gvm-opnd (apply-opnds instr))
        (clone-gvm-opnd (apply-loc instr))
        (gvm-instr-frame instr)
        (gvm-instr-comment instr)))

      ((copy)
       (make-copy
        (clone-gvm-opnd (copy-opnd instr))
        (clone-gvm-opnd (copy-loc instr))
        (gvm-instr-frame instr)
        (gvm-instr-comment instr)))

      ((close)
       (make-close
        (map clone-closure-parms (close-parms instr))
        (gvm-instr-frame instr)
        (gvm-instr-comment instr)))

      ((ifjump)
       (make-ifjump
        (ifjump-test instr)
        (map clone-gvm-opnd (ifjump-opnds instr))
        (replacement-lbl-num (ifjump-true instr))
        (replacement-lbl-num (ifjump-false instr))
        (ifjump-poll? instr)
        (gvm-instr-frame instr)
        (gvm-instr-comment instr)))

      ((switch)
       (make-switch
        (clone-gvm-opnd (switch-opnd instr))
        (map (lambda (c)
               (make-switch-case
                (switch-case-obj c)
                (replacement-lbl-num (switch-case-lbl c))))
             (switch-cases instr))
        (replacement-lbl-num (switch-default instr))
        (switch-poll? instr)
        (gvm-instr-frame instr)
        (gvm-instr-comment instr)))

      ((jump)
       (make-jump
        (clone-gvm-opnd (jump-opnd instr))
        (and (jump-ret instr) (replacement-lbl-num (jump-ret instr)))
        (jump-nb-args instr)
        (jump-poll? instr)
        (jump-safe? instr)
        (gvm-instr-frame instr)
        (gvm-instr-comment instr)))

      (else
       (compiler-internal-error
        "gvm-instr-clone-replacing-lbls, unknown 'instr':" instr))))

  (gvm-instr-copy-types! instr (clone-instr instr)))

(define (gvm-instr-clone instr)
  (gvm-instr-clone-replacing-lbls instr (lambda (lbl) lbl)))

;; Determining basic block references and precedents.

(define (bbs-determine-refs! bbs)

  (define (get-bb lbl)
    (lbl-num->bb lbl bbs))

  (bbs-for-each-bb
   (lambda (bb)
     (bb-precedents-set! bb '()))
   bbs)

  (bbs-for-each-bb
   (lambda (bb)
     (bb-determine-refs! bb get-bb))
   bbs))

(define (bb-determine-refs! bb get-bb)

  (bb-references-set! bb '())

  (gvm-instr-determine-refs! (bb-label-instr bb) bb get-bb)
  (for-each (lambda (instr) (gvm-instr-determine-refs! instr bb get-bb))
            (bb-non-branch-instrs bb))
  (gvm-instr-determine-refs! (bb-branch-instr bb) bb get-bb))

(define (gvm-instr-determine-refs! instr bb get-bb)

  (define (reference lbl)
    (bb-add-reference! bb lbl))

  (define (direct-branch lbl)
    ;; while building the versionned CFG, some blocks may not exist yet/anymore
    (let* ((prec (get-bb (reference lbl))))
      (if prec (bb-add-precedent! prec (bb-lbl-num bb)))))

  (define (scan-opnd gvm-opnd)
    (cond ((not gvm-opnd))
          ((lbl? gvm-opnd)
           (reference (lbl-num gvm-opnd)))
          ((clo? gvm-opnd)
           (scan-opnd (clo-base gvm-opnd)))))

  (case (gvm-instr-kind instr)

    ((label)
     '())

    ((apply)
     (for-each scan-opnd (apply-opnds instr))
     (if (apply-loc instr)
         (scan-opnd (apply-loc instr))))

    ((copy)
     (scan-opnd (copy-opnd instr))
     (scan-opnd (copy-loc instr)))

    ((close)
     (for-each (lambda (parm)
                 (reference (closure-parms-lbl parm))
                 (scan-opnd (closure-parms-loc parm))
                 (for-each scan-opnd (closure-parms-opnds parm)))
               (close-parms instr)))

    ((ifjump)
     (for-each scan-opnd (ifjump-opnds instr))
     (direct-branch (ifjump-true instr))
     (direct-branch (ifjump-false instr)))

    ((switch)
     (scan-opnd (switch-opnd instr))
     (for-each (lambda (c)
                 (direct-branch (switch-case-lbl c)))
               (switch-cases instr))
     (direct-branch (switch-default instr)))

    ((jump)
     (let ((opnd (jump-opnd instr)))
       (if (lbl? opnd)
           (direct-branch (lbl-num opnd))
           (scan-opnd (jump-opnd instr))))
     (let ((ret (jump-ret instr)))
       (if ret
           (reference ret))))

    (else
     (compiler-internal-error
      "gvm-instr-determine-refs!, unknown GVM instruction kind"))))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; 'Purification' of basic block sets:
;; ----------------------------------

;; This step removes unreachable basic blocks (i.e. dead code), duplicate
;; basic blocks (i.e. common code), useless jumps and jump cascades from
;; a basic block set.  It also orders the basic blocks so that the destination
;; of a branch is put (if possible) right after the branch instruction.  The
;; 'references' and 'precedents' fields of each basic block are also filled in
;; through the process.  The first basic block of a 'purified' basic block set
;; is always the entry point.

(define (bbs-purify bbs)
  (define optim? #f)
  (define (purify-step bbs0)
    (let* ((bbs1 (bbs-remove-jump-cascades bbs0))
           (bbs2 (bbs-remove-dead-code bbs1))
           (bbs3 (bbs-remove-common-code bbs2))
           (bbs4 (bbs-remove-useless-jumps bbs3)))
      (cons bbs2 bbs4)))

  (let loop ((bbs0 (bbs-type-specialize (if (not optim?) bbs (cdr (purify-step bbs))))))
    (if (not optim?) (begin (bbs-determine-refs! bbs0) (bbs-order bbs0))
    (let* ((bbs1-bbs2 (purify-step bbs0))
           (bbs1 (car bbs1-bbs2))
           (bbs2 (cdr bbs1-bbs2)))
      (if (not (eq? bbs1 bbs2)) ;; iterate until code does not change
          (loop bbs2)
          (bbs-order bbs2))))))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

;; Step 1, Jump cascade removal:

(define (bbs-remove-jump-cascades bbs)

  (let ((new-bbs (make-bbs))
        (changed? #f)
        (lbl-changed? #f))

    (define (empty-bb? bb)
      (and (eq? (bb-label-kind bb) 'simple)     ;; simple label and
           (null? (bb-non-branch-instrs bb))))  ;; no non-branching instrs

    (define (jump-to-non-entry-lbl? branch)
      (and (eq? (gvm-instr-kind branch) 'jump)
           (not (first-class-jump? branch)) ;; not a jump to an entry label
           (jump-lbl? branch)))

    (define (jump-cascade-to dest-lbl first-jump thunk)
      (let loop ((lbl dest-lbl)
                 (last-jump/ret (and (jump-ret first-jump) first-jump))
                 (fs (frame-size (gvm-instr-frame first-jump)))
                 (poll? (jump-poll? first-jump))
                 (seen '()))
        (if (memv lbl seen) ;; infinite loop?
            (thunk lbl fs last-jump/ret poll?)
            (let ((bb (lbl-num->bb lbl bbs)))
              (if (and (empty-bb? bb) (<= (bb-slots-gained bb) 0))
                  (let* ((branch
                          (bb-branch-instr bb))
                         (jump-lbl
                          (jump-to-non-entry-lbl? branch)))
                    (if jump-lbl
                        (loop
                         jump-lbl
                         (if (jump-ret branch) branch last-jump/ret)
                         (+ fs (bb-slots-gained bb))
                         (or (jump-poll? branch)
                             poll?)
                         (cons lbl seen))
                        (thunk lbl fs last-jump/ret poll?)))
                  (thunk lbl fs last-jump/ret poll?))))))

    (define (find-equiv-lbl start-lbl poll?)
      (let loop ((lbl start-lbl) (seen '()))
        (if (memv lbl seen) ;; infinite loop?
            lbl
            (let ((bb (lbl-num->bb lbl bbs)))
              (if (empty-bb? bb)
                  (let* ((branch
                          (bb-branch-instr bb))
                         (jump-lbl
                          (jump-to-non-entry-lbl? branch)))
                    (if (and jump-lbl
                             (not (jump-ret branch))
                             (or poll?
                                 (not (jump-poll? branch)))
                             (= (bb-slots-gained bb) 0))
                        (loop jump-lbl (cons lbl seen))
                        lbl))
                  lbl)))))

    (define (equiv-lbl start-lbl poll?)
      (let ((lbl (find-equiv-lbl start-lbl poll?)))
        (if (not (eqv? lbl start-lbl))
            (set! lbl-changed? #t))
        lbl))

    (define (remove-cascade! bb)
      (let ((branch (bb-branch-instr bb)))

        (define (replace-branch-by last-jump/ret new-branch-instr)
          (set! changed? #t)
          (let ((new-bb (make-bb (bb-label-instr bb) new-bbs)))
            (bb-non-branch-instrs-set! new-bb (bb-non-branch-instrs bb))
            (if (not last-jump/ret)
                (bb-branch-instr-set! new-bb new-branch-instr)
                (let* ((lbl2
                        (bbs-new-lbl! new-bbs))
                       (new-bb2
                        (make-bb
                         (gvm-instr-copy-types!
                          last-jump/ret
                          (make-label-simple
                           lbl2
                           (gvm-instr-frame last-jump/ret)
                           (gvm-instr-comment
                              (bb-label-instr
                                (stretchable-vector-ref
                                  (bbs-basic-blocks bbs)
                                  (lbl-num (jump-opnd last-jump/ret)))))))
                         new-bbs)))
                  (bb-branch-instr-set!
                   new-bb
                   (gvm-instr-copy-types!
                    last-jump/ret
                    (make-jump
                     (make-lbl lbl2)
                     (jump-ret last-jump/ret)
                     #f
                     #f
                     #f
                     (gvm-instr-frame last-jump/ret)
                     (gvm-instr-comment last-jump/ret))))
                  (bb-branch-instr-set! new-bb2 new-branch-instr)))))

        (stretchable-vector-set!
         (bbs-basic-blocks new-bbs)
         (bb-lbl-num bb)
         bb)

        (case (gvm-instr-kind branch)

          ((ifjump) ;; branch is an 'ifjump'
           (set! lbl-changed? #f)
           (let* ((new-poll?
                   (ifjump-poll? branch))
                  (new-true
                   (equiv-lbl (ifjump-true branch)
                              new-poll?))
                  (new-false
                   (equiv-lbl (ifjump-false branch)
                              new-poll?)))
             (if lbl-changed?
                 (replace-branch-by
                  #f
                  (gvm-instr-copy-types!
                   branch
                   (make-ifjump
                    (ifjump-test branch)
                    (ifjump-opnds branch)
                    new-true
                    new-false
                    new-poll?
                    (gvm-instr-frame branch)
                    (gvm-instr-comment branch)))))))

          ((switch) ;; branch is a 'switch'
           (set! lbl-changed? #f)
           (let* ((new-poll?
                   (switch-poll? branch))
                  (new-cases
                   (map (lambda (c)
                          (make-switch-case
                           (switch-case-obj c)
                           (equiv-lbl (switch-case-lbl c)
                                      new-poll?)))
                        (switch-cases branch)))
                  (new-default
                   (equiv-lbl (switch-default branch)
                              new-poll?)))
             (if lbl-changed?
                 (replace-branch-by
                  #f
                  (gvm-instr-copy-types!
                   branch
                   (make-switch
                    (switch-opnd branch)
                    new-cases
                    new-default
                    new-poll?
                    (gvm-instr-frame branch)
                    (gvm-instr-comment branch)))))))

          ((jump) ;; branch is a 'jump'
           (let ((dest-lbl (jump-lbl? branch)))
             (if (and dest-lbl
                      (not (first-class-jump? branch))) ;; but not to an entry label
                 (jump-cascade-to
                  dest-lbl
                  branch
                  (lambda (lbl fs last-jump/ret poll?)
                    (let* ((dest-bb (lbl-num->bb lbl bbs))
                           (last-branch (bb-branch-instr dest-bb)))
                      (if (and (empty-bb? dest-bb)
                               (or (not poll?) ;;TODO: remove this part
                                   (case (gvm-instr-kind last-branch)
                                     ((ifjump)
                                      (ifjump-poll? last-branch))
                                     ((switch)
                                      (switch-poll? last-branch))
                                     ((jump)
                                      (jump-poll? last-branch))
                                     (else
                                      #f))))

                          (let* ((new-fs (+ fs (bb-slots-gained dest-bb)))
                                 (new-frame (frame-truncate ;; TODO: fix r0 missing from live vars
                                             (gvm-instr-frame branch)
                                             new-fs))
                                 (new-types (types-truncate
                                             (gvm-instr-types branch)
                                             new-frame)))

                            (define (adjust-opnd opnd)
                              (cond ((stk? opnd)
                                     (make-stk
                                      (+ (- fs (bb-entry-frame-size dest-bb))
                                         (stk-num opnd))))
                                    ((clo? opnd)
                                     (make-clo (adjust-opnd (clo-base opnd))
                                               (clo-index opnd)))
                                    (else
                                     opnd)))

                            (case (gvm-instr-kind last-branch)

                              ((ifjump)
                               (let* ((new-poll?
                                       (or (ifjump-poll? last-branch)
                                           poll?))
                                      (new-true
                                       (equiv-lbl (ifjump-true last-branch)
                                                  new-poll?))
                                      (new-false
                                       (equiv-lbl (ifjump-false last-branch)
                                                  new-poll?)))
                                 (replace-branch-by
                                  last-jump/ret
                                  (gvm-instr-types-set!-returning-instr
                                   (make-ifjump
                                    (ifjump-test last-branch)
                                    (map adjust-opnd
                                         (ifjump-opnds last-branch))
                                    new-true
                                    new-false
                                    new-poll?
                                    new-frame
                                    (gvm-instr-comment last-branch))
                                   new-types))))

                              ((switch)
                               (let* ((new-poll?
                                       (or (switch-poll? last-branch)
                                           poll?))
                                      (new-cases
                                       (map (lambda (c)
                                              (make-switch-case
                                               (switch-case-obj c)
                                               (equiv-lbl (switch-case-lbl c)
                                                          new-poll?)))
                                            (switch-cases last-branch)))
                                      (new-default
                                       (equiv-lbl (switch-default last-branch)
                                                  new-poll?)))
                                 (replace-branch-by
                                  last-jump/ret
                                  (gvm-instr-types-set!-returning-instr
                                   (make-switch
                                    (adjust-opnd (switch-opnd last-branch))
                                    new-cases
                                    new-default
                                    new-poll?
                                    new-frame
                                    (gvm-instr-comment last-branch))
                                   new-types))))

                              ((jump)
                               (let* ((ret
                                       (and last-jump/ret
                                            (jump-ret last-jump/ret)))
                                      (new-ret
                                       (or (jump-ret last-branch)
                                           ret))
                                      (new-poll?
                                       (or (jump-poll? last-branch)
                                           poll?))
                                      (opnd
                                       (jump-opnd last-branch))
                                      (dead-end?
                                       (and (obj? opnd)
                                            (let ((val (obj-val opnd)))
                                              (and (proc-obj? val)
                                                   (proc-obj-dead-end? val))))))
                                 (if (not dead-end?)
                                     (replace-branch-by
                                      #f
                                      (gvm-instr-types-set!-returning-instr
                                       (make-jump
                                        (if (and ret (eqv? opnd return-addr-reg))
                                            (make-lbl ret)
                                            (adjust-opnd opnd))
                                        new-ret
                                        (jump-nb-args last-branch)
                                        new-poll?
                                        (jump-safe? last-branch)
                                        new-frame
                                        (gvm-instr-comment last-branch))
                                       new-types)))))

                              (else
                               (compiler-internal-error
                                "bbs-remove-jump-cascades, unknown branch kind"))))

                          (let* ((ret
                                  (and last-jump/ret
                                       (jump-ret last-jump/ret)))
                                 (new-ret
                                  (or (jump-ret branch)
                                      ret))
                                 (new-poll?
                                  (or (jump-poll? branch)
                                      poll?)))
                            (if (or (not (eqv? new-ret ret))
                                    (not (eqv? new-poll? poll?))
                                    (not (= lbl dest-lbl)))
                                (let* ((new-frame
                                        (frame-truncate ;; TODO: fix r0 missing from live vars
                                         (gvm-instr-frame branch)
                                         fs))
                                       (new-types
                                        (types-truncate
                                         (gvm-instr-types branch)
                                         new-frame)))
                                  (replace-branch-by
                                   #f
                                   (gvm-instr-types-set!-returning-instr
                                    (make-jump
                                     (make-lbl lbl)
                                     new-ret
                                     (jump-nb-args branch)
                                     new-poll?
                                     (jump-safe? branch)
                                     new-frame
                                     (gvm-instr-comment branch))
                                    new-types))))))))))))

          (else
           (compiler-internal-error
            "bbs-remove-jump-cascades, unknown branch kind")))))

    (bbs-next-lbl-num-set! new-bbs (bbs-next-lbl-num bbs))
    (bbs-entry-lbl-num-set! new-bbs (bbs-entry-lbl-num bbs))

    (bbs-for-each-bb remove-cascade! bbs)

    (if changed? new-bbs bbs)))

(define (jump-lbl? branch)
  (let ((opnd (jump-opnd branch)))
    (if (lbl? opnd) (lbl-num opnd) #f)))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

;; Step 2, Dead code removal:

(define (bbs-remove-dead-code bbs)

  (let ((new-bbs (make-bbs))
        (work-list (queue-empty)))

    (define (get-bb lbl)
      (reachable lbl))

    (define (reachable lbl)
      (or (lbl-num->bb lbl new-bbs)
          (let ((new-bb (bb-clone (lbl-num->bb lbl bbs) new-bbs)))
            (queue-put! work-list new-bb)
            new-bb)))

    (bbs-next-lbl-num-set! new-bbs (bbs-next-lbl-num bbs))
    (bbs-entry-lbl-num-set! new-bbs (bbs-entry-lbl-num bbs))

    (reachable (bbs-entry-lbl-num bbs))

    (let loop ()
      (if (not (queue-empty? work-list))
          (let ((bb (queue-get! work-list)))
            (begin
              (bb-determine-refs! bb get-bb)
              (for-each reachable (bb-references bb))
              (loop)))))

    new-bbs))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

;; Step 3, Common code removal:

(define (bbs-remove-common-code bbs)
  (let ((n (bbs-next-lbl-num bbs)))
    (if (> n 300) ;; if code is too large, don't optimize
        bbs
        (bbs-remove-common-code-aux bbs))))

(define (bbs-remove-common-code-aux bbs)

  (define tctx (make-tctx))

  (let* ((n (bbs-next-lbl-num bbs))
         (hash-table-length (if (< n 50) 43 403))
         (hash-table (make-vector hash-table-length '()))
         (prim-table '())
         (lbl-map (make-stretchable-vector #f))
         (new-bbs (make-bbs))
         (changed? #f))

    (define (hash-prim prim)
      (let ((n (length prim-table))
            (i (pos-in-list prim prim-table)))
        (if i
            (- n i)
            (begin
              (set! prim-table (cons prim prim-table))
              (+ n 1)))))

    (define (hash-opnds l)
      ;; assumes that operands are encoded with numbers
      (let loop ((l l) (n 0))
        (if (pair? l)
            (loop (cdr l)
                  (let ((x (car l)))
                    (if (lbl? x)
                        n ;; labels must be ignored (they might end up equal)
                        (modulo (+ (* n 10000) x) hash-table-length))))
            n)))

    (define (hash-bb bb)
      ;; compute hash address for a basic block using the branch
      ;; instruction and ignoring labels
      (let ((branch (bb-branch-instr bb)))
        (modulo
         (case (gvm-instr-kind branch)
           ((ifjump)
            (+ (hash-opnds (ifjump-opnds branch))
               (* 10 (hash-prim (ifjump-test branch)))
               (* 100 (frame-size (gvm-instr-frame branch)))))
           ((switch)
            (+ (hash-opnds (list (switch-opnd branch)))
               (* 10 (length (switch-cases branch)))
               (* 100 (frame-size (gvm-instr-frame branch)))))
           ((jump)
            (+ (hash-opnds (list (jump-opnd branch)))
               (* 10 (or (jump-nb-args branch) -1))
               (* 100 (frame-size (gvm-instr-frame branch)))))
           (else
            0))
         hash-table-length)))

    (define (replacement-lbl-num lbl)
      (or (stretchable-vector-ref lbl-map lbl) lbl))

    (define (add-map! bb1 bb2) ;; bb1 should be replaced by bb2
      (stretchable-vector-set!
       lbl-map
       (bb-lbl-num bb1)
       (bb-lbl-num bb2)))

    (define (remove-map! bb)
      (stretchable-vector-set!
       lbl-map
       (bb-lbl-num bb)
       #f))

    (define (enter-bb! bb) ;; enter a basic block in the hash table

      (stretchable-vector-set!
       (bbs-basic-blocks new-bbs)
       (bb-lbl-num bb)
       bb)

      (let ((h (hash-bb bb)))
        (vector-set! hash-table
                     h
                     (add-bb bb (vector-ref hash-table h)))))

    (define (types-merge types1 types2)
      (and types1
           types2
           (locenv-merge types1
                         types2
                         0
                         (lambda (type1 type2)
                           (type-union tctx type1 type2 #f)))))

    (define (instr-merge instr1 instr2)
      (let ((new-instr (gvm-instr-clone instr1)))
        (gvm-instr-types-set!-returning-instr
         new-instr
         (types-merge (gvm-instr-types instr1)
                      (gvm-instr-types instr2)))))

    (define (add-bb bb lst) ;; add basic block 'bb' to list of basic blocks
      (if (pair? lst)
          (let ((bb2 (car lst))) ;; pick next basic block in list

            (add-map! bb bb2) ;; for now, assume that 'bb' = 'bb2'

            (if (eqv-bb? bb bb2) ;; are they the same?

                (begin
                  ;; merge types of bb to bb2
                  (bb-label-instr-set!
                   bb2
                   (instr-merge
                    (bb-label-instr bb2)
                    (bb-label-instr bb)))
                  (bb-non-branch-instrs-set!
                   bb2
                   (map instr-merge
                        (bb-non-branch-instrs bb2)
                        (bb-non-branch-instrs bb)))
                  (bb-branch-instr-set!
                   bb2
                   (instr-merge
                    (bb-branch-instr bb2)
                    (bb-branch-instr bb)))
                  (set! changed? #t)
                  lst)

                (begin
                  (remove-map! bb) ;; they are not the same!
                  (if (eqv-gvm-instr? (bb-branch-instr bb)
                                      (bb-branch-instr bb2))

                      (extract-common-tail ;; check if tail is the same
                       bb
                       bb2
                       (lambda (head1 head2 tail1 tail2)
                         (if (<= (length tail1) 10) ;; common tail long enough?

                             ;; no, so try rest of list
                             (cons bb2 (add-bb bb (cdr lst)))

                             ;; create bb for common tail
                             (let* ((lbl-common
                                     (bbs-new-lbl! new-bbs))
                                    (branch1
                                     (bb-branch-instr bb))
                                    (branch2
                                     (bb-branch-instr bb2))
                                    (fs-common
                                     (need-gvm-instrs tail1 branch1))
                                    (last1
                                     (if (pair? head1) (car head1) (bb-label-instr bb)))
                                    (last2
                                     (if (pair? head2) (car head2) (bb-label-instr bb2)))
                                    (frame-common
                                     (frame-truncate
                                      (gvm-instr-frame last1)
                                      fs-common))
                                    (types-join1
                                     (gvm-instr-types last1))
                                    (types-join2
                                     (gvm-instr-types last2))
                                    (types-common
                                     (types-truncate
                                      (types-merge types-join1 types-join2)
                                      frame-common))
                                    (comment-common
                                     (gvm-instr-comment (car tail1)))
                                    (bb-common
                                     (make-bb
                                      (gvm-instr-types-set!-returning-instr
                                       (make-label-simple
                                        lbl-common
                                        frame-common
                                        comment-common)
                                       types-common)
                                      new-bbs))
                                    (new-bb
                                     (make-bb (bb-label-instr bb) new-bbs))
                                    (new-bb2
                                     (make-bb (bb-label-instr bb2) new-bbs)))

                               ;; create bb for common part
                               (bb-non-branch-instrs-set!
                                bb-common
                                (map instr-merge tail1 tail2))
                               (bb-branch-instr-set!
                                bb-common
                                (instr-merge branch1 branch2))

                               ;; create trimmed bb2 jumping to common part
                               (bb-non-branch-instrs-set!
                                new-bb2
                                (reverse head2))
                               (bb-branch-instr-set!
                                new-bb2
                                (gvm-instr-copy-types!
                                 last2
                                 (make-jump
                                  (make-lbl lbl-common)
                                  #f
                                  #f
                                  #f
                                  #f
                                  frame-common
                                  comment-common)))

                               ;; create trimmed bb jumping to common part
                               (bb-non-branch-instrs-set!
                                new-bb
                                (reverse head1))
                               (bb-branch-instr-set!
                                new-bb
                                (gvm-instr-copy-types!
                                 last1
                                 (make-jump
                                  (make-lbl lbl-common)
                                  #f
                                  #f
                                  #f
                                  #f
                                  frame-common
                                  comment-common)))

                               (set! changed? #t)

                               (add-bb bb-common (cdr lst))))))

                      (cons bb2 (add-bb bb (cdr lst)))))))

          (list bb)))

    (define (extract-common-tail bb1 bb2 cont)
      (let loop ((lst1 (reverse (bb-non-branch-instrs bb1)))
                 (lst2 (reverse (bb-non-branch-instrs bb2)))
                 (tail1 '())
                 (tail2 '()))
        (if (and (pair? lst1) (pair? lst2))
            (let ((i1 (car lst1))
                  (i2 (car lst2)))
              (if (eqv-gvm-instr? i1 i2)
                  (loop (cdr lst1) (cdr lst2) (cons i1 tail1) (cons i2 tail2))
                  (cont lst1 lst2 tail1 tail2)))
            (cont lst1 lst2 tail1 tail2))))

    (define (eqv-bb? bb1 bb2)
      (let ((bb1-non-branch (bb-non-branch-instrs bb1))
            (bb2-non-branch (bb-non-branch-instrs bb2)))
        (and (= (length bb1-non-branch) (length bb2-non-branch))
             (eqv-gvm-instr? (bb-label-instr bb1) (bb-label-instr bb2))
             (eqv-gvm-instr? (bb-branch-instr bb1) (bb-branch-instr bb2))
             (eqv-list? eqv-gvm-instr? bb1-non-branch bb2-non-branch))))

    (define (eqv-list? pred? lst1 lst2)
      (if (pair? lst1)
          (and (pair? lst2)
               (pred? (car lst1) (car lst2))
               (eqv-list? pred? (cdr lst1) (cdr lst2)))
          (not (pair? lst2))))

    (define (eqv-lbl-num? lbl1 lbl2)
      (= (replacement-lbl-num lbl1)
         (replacement-lbl-num lbl2)))

    (define (eqv-gvm-opnd? opnd1 opnd2)
      (if (not opnd1)
          (not opnd2)
          (and opnd2
               (cond ((lbl? opnd1)
                      (and (lbl? opnd2)
                           (eqv-lbl-num? (lbl-num opnd1) (lbl-num opnd2))))
                     ((clo? opnd1)
                      (and (clo? opnd2)
                           (= (clo-index opnd1) (clo-index opnd2))
                           (eqv-gvm-opnd? (clo-base opnd1)
                                          (clo-base opnd2))))
                     (else
                      (eqv? opnd1 opnd2))))))

    (define (eqv-key-pair? key-pair1 key-pair2)
      (and (eq? (car key-pair1) (car key-pair2))
           (eqv-gvm-opnd? (cdr key-pair1) (cdr key-pair2))))

    (define (eqv-gvm-instr? instr1 instr2)

      (define (eqv-closure-parms? p1 p2)
        (and (eqv-gvm-opnd? (closure-parms-loc p1)
                            (closure-parms-loc p2))
             (eqv-lbl-num? (closure-parms-lbl p1)
                           (closure-parms-lbl p2))
             (eqv-list? eqv-gvm-opnd?
                        (closure-parms-opnds p1)
                        (closure-parms-opnds p2))))

      (define (has-debug-info? instr)
        (let ((node (instr-comment-get instr 'node)))
          (and node
               (let ((env (node-env node)))
                 (and (debug? env)
                      (or (debug-location? env)
                          (debug-source? env)
                          (debug-environments? env)))))))

      (let ((kind1 (gvm-instr-kind instr1))
            (kind2 (gvm-instr-kind instr2)))
        (and (eq? kind1 kind2)
             (frame-eq? (gvm-instr-frame instr1) (gvm-instr-frame instr2))
             (not (has-debug-info? instr1))
             (not (has-debug-info? instr2))
;;;;;;;;;;             (equal? (gvm-instr-types instr1) (gvm-instr-types instr2))
             (case kind1

               ((label)
                (let ((lkind1 (label-kind instr1))
                      (lkind2 (label-kind instr2)))
                  (and (eq? lkind1 lkind2)
                       (case lkind1
                         ((simple return task-entry task-return)
                          #t)
                         ((entry)
                          (and (= (label-entry-nb-parms instr1)
                                  (label-entry-nb-parms instr2))
                               (eqv-list? eqv-gvm-opnd?
                                          (label-entry-opts instr1)
                                          (label-entry-opts instr2))
                               (if (label-entry-keys instr1)
                                   (and (label-entry-keys instr2)
                                        (eqv-list? eqv-key-pair?
                                                   (label-entry-keys instr1)
                                                   (label-entry-keys instr2)))
                                   (not (label-entry-keys instr2)))
                               (eq? (label-entry-rest? instr1)
                                    (label-entry-rest? instr2))
                               (eq? (label-entry-closed? instr1)
                                    (label-entry-closed? instr2))))
                         (else
                          (compiler-internal-error
                           "eqv-gvm-instr?, unknown label kind"))))))

               ((apply)
                (and (eq? (apply-prim instr1) (apply-prim instr2))
                     (eqv-list? eqv-gvm-opnd?
                                (apply-opnds instr1)
                                (apply-opnds instr2))
                     (eqv-gvm-opnd? (apply-loc instr1)
                                    (apply-loc instr2))))

               ((copy)
                (and (eqv-gvm-opnd? (copy-opnd instr1)
                                    (copy-opnd instr2))
                     (eqv-gvm-opnd? (copy-loc instr1)
                                    (copy-loc instr2))))

               ((close)
                (eqv-list? eqv-closure-parms?
                           (close-parms instr1)
                           (close-parms instr2)))

               ((ifjump)
                (and (eq? (ifjump-test instr1)
                          (ifjump-test instr2))
                     (eqv-list? eqv-gvm-opnd?
                                (ifjump-opnds instr1)
                                (ifjump-opnds instr2))
                     (eqv-lbl-num? (ifjump-true instr1)
                                   (ifjump-true instr2))
                     (eqv-lbl-num? (ifjump-false instr1)
                                   (ifjump-false instr2))
                     (eq? (ifjump-poll? instr1)
                          (ifjump-poll? instr2))))

               ((switch)
                (and (eqv-gvm-opnd? (switch-opnd instr1)
                                    (switch-opnd instr2))
                     (every? (lambda (x)
                               (and (eqv? (switch-case-obj (car x))
                                          (switch-case-obj (cdr x)))
                                    (eqv-lbl-num? (switch-case-lbl (car x))
                                                  (switch-case-lbl (cdr x)))))
                             (map cons
                                  (switch-cases instr1)
                                  (switch-cases instr2)))
                     (eqv-lbl-num? (switch-default instr1)
                                   (switch-default instr2))
                     (eq? (switch-poll? instr1)
                          (switch-poll? instr2))))

               ((jump)
                (and (eqv-gvm-opnd? (jump-opnd instr1)
                                    (jump-opnd instr2))
                     (let ((ret1 (jump-ret instr1))
                           (ret2 (jump-ret instr2)))
                       (if ret1
                           (and ret2
                                (eqv-lbl-num? ret1 ret2))
                           (not ret2)))
                     (eqv? (jump-nb-args instr1)
                           (jump-nb-args instr2))
                     (eq? (jump-poll? instr1)
                          (jump-poll? instr2))
                     (eq? (jump-safe? instr1)
                          (jump-safe? instr2))))

               (else
                (compiler-internal-error
                 "eqv-gvm-instr?, unknown 'gvm-instr':" instr1))))))

    (bbs-next-lbl-num-set! new-bbs (bbs-next-lbl-num bbs))

    ;; Fill hash table, remove equivalent basic blocks and common tails

    (bbs-for-each-bb enter-bb! bbs)

    (if changed?

        (begin

          ;; Reconstruct bbs

          (bbs-entry-lbl-num-set!
           new-bbs
           (replacement-lbl-num (bbs-entry-lbl-num bbs)))

          (bbs-for-each-bb
           (lambda (bb)
             (bb-clone-replacing-lbls bb new-bbs replacement-lbl-num #f))
           new-bbs)

          (bbs-determine-refs! new-bbs)

          new-bbs)

        bbs)))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

;; Step 4, Useless jump removal:

(define (bbs-remove-useless-jumps bbs)

  (let ((new-bbs (make-bbs))
        (changed? #f))

    (define (remove-useless-jump bb)

      (stretchable-vector-set!
       (bbs-basic-blocks new-bbs)
       (bb-lbl-num bb)
       bb)

      (let loop ((bb bb))
        (let* ((branch (bb-branch-instr bb))
               (branch-kind (gvm-instr-kind branch)))
          (cond
            ;; is it an if which then and else jump to the same location?
            ((and (eq? branch-kind 'ifjump)
                  (not (proc-obj-side-effects? (ifjump-test branch)))
                  (= (ifjump-true branch) (ifjump-false branch)))
              (let* ((new-bb (make-bb (bb-label-instr bb) new-bbs)))
                (bb-non-branch-instrs-set!
                 new-bb
                 (bb-non-branch-instrs bb))
                (bb-branch-instr-set!
                 new-bb
                 (make-jump
                   (make-lbl (ifjump-true branch)) ;; opnd
                   #f ;; ret
                   #f ;; nb-args
                   (ifjump-poll? branch) ;; poll?
                   #f ;; safe?
                   (gvm-instr-frame branch) ;; frame
                   (gvm-instr-comment branch) ;; comment
                   ))
                (set! changed? #t)
                (loop new-bb)))
            ;; is it a non-polling 'jump' to a label without a return address?
            ((and (eq? branch-kind 'jump)
                  (not (first-class-jump? branch))
                  (not (jump-ret branch))
                  (not (jump-poll? branch))
                  (jump-lbl? branch))
              (let* ((dest-bb (lbl-num->bb (jump-lbl? branch) bbs))
                     (frame1 (gvm-instr-frame (bb-last-non-branch-instr bb)))
                     (frame2 (gvm-instr-frame (bb-label-instr dest-bb))))

                ;; is it a 'simple' label with the same frame as the last
                ;; non-branch instruction?

                (if (and (eq? (bb-label-kind dest-bb) 'simple)
;;                         (frame-eq? frame1 frame2) ;; too restrictive, just use frame-size equality
                         (= (frame-size frame1) (frame-size frame2))
                         (= (length (bb-precedents dest-bb)) 1))

                    (let* ((new-bb (make-bb (bb-label-instr bb) new-bbs)))
                      (bb-non-branch-instrs-set!
                       new-bb
                       (append (bb-non-branch-instrs bb)
                               (bb-non-branch-instrs dest-bb)
                               '()))
                      (bb-branch-instr-set!
                       new-bb
                       (bb-branch-instr dest-bb))
                      (set! changed? #t)
                      (loop new-bb)))))))))

    (bbs-next-lbl-num-set! new-bbs (bbs-next-lbl-num bbs))
    (bbs-entry-lbl-num-set! new-bbs (bbs-entry-lbl-num bbs))

    (bbs-for-each-bb remove-useless-jump bbs)

    (if changed? new-bbs bbs)))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

;; Step 5, Basic block set ordering:

(define (bbs-order bbs)

  (let ((ordered-blocks (queue-empty))
        (left-to-schedule (stretchable-vector-copy (bbs-basic-blocks bbs))))

    ;; test if a basic block is in 'left-to-schedule' and return the
    ;; basic block if it is

    (define (left-to-schedule? bb)
      (stretchable-vector-ref left-to-schedule (bb-lbl-num bb)))

    ;; remove basic block from 'left-to-schedule'

    (define (remove-bb! bb)
      (stretchable-vector-set! left-to-schedule (bb-lbl-num bb) #f)
      bb)

    ;; return a basic block which ends with a branch to 'bb' (and that is
    ;; still in 'left-to-schedule') or #f if there aren't any

    (define (prec-bb bb)
      (let loop ((lst (bb-precedents bb)) (best #f) (best-fs #f))
        (if (null? lst)
          best
          (let* ((lbl (car lst))
                 (x (lbl-num->bb lbl bbs))
                 (x-fs (bb-exit-frame-size x)))
            (if (and (left-to-schedule? x)
                     (or (not best) (< x-fs best-fs)))
              (loop (cdr lst) x x-fs)
              (loop (cdr lst) best best-fs))))))

    ;; return the basic block which 'bb' jumps to (and that is still in
    ;; bbs) or #f if there aren't any

    (define (succ-bb bb)

      (define (branches-to-lbl? bb)
        (let ((branch (bb-branch-instr bb)))
          (case (gvm-instr-kind branch)
            ((ifjump) #t)
            ((switch) #t)
            ((jump) (lbl? (jump-opnd branch)))
            (else
             (compiler-internal-error
              "bbs-order, unknown branch kind")))))

      (define (best-succ bb1 bb2)   ;; heuristic that determines which
        (if (branches-to-lbl? bb1)  ;; bb is most frequently executed
           bb1
           (if (branches-to-lbl? bb2)
             bb2
             (if (< (bb-exit-frame-size bb1)
                    (bb-exit-frame-size bb2))
               bb2
               bb1))))

      (let ((branch (bb-branch-instr bb)))
        (case (gvm-instr-kind branch)

          ((ifjump)
           (let* ((true-bb
                   (left-to-schedule?
                     (lbl-num->bb (ifjump-true branch) bbs)))
                  (false-bb
                   (left-to-schedule?
                     (lbl-num->bb (ifjump-false branch) bbs))))
             (if (and true-bb false-bb)
               (best-succ true-bb false-bb)
               (or true-bb false-bb))))

          ((switch)
           (left-to-schedule?
            (lbl-num->bb (switch-default branch) bbs)))

          ((jump)
           (let ((opnd (jump-opnd branch)))
             (and (lbl? opnd)
                  (left-to-schedule?
                    (lbl-num->bb (lbl-num opnd) bbs)))))

          (else
           (compiler-internal-error
             "bbs-order, unknown branch kind")))))

    ;; schedule a given basic block 'bb' with it's predecessors and
    ;; successors.

    (define (schedule-from bb)
      (queue-put! ordered-blocks bb)
      (let ((x (succ-bb bb)))
        (if x
          (begin
            (schedule-around (remove-bb! x))
            (let ((y (succ-bb bb)))
              (if y
                (schedule-around (remove-bb! y)))))))
      (schedule-refs bb))

    (define (schedule-around bb)
      (let ((x (prec-bb bb)))
        (if x
          (let ((bb-list (schedule-back (remove-bb! x) '())))
            (queue-put! ordered-blocks x)
            (schedule-forw bb)
            (for-each schedule-refs bb-list))
          (schedule-from bb))))

    (define (schedule-back bb bb-list)
      (let ((bb-list* (cons bb bb-list))
            (x (prec-bb bb)))
        (if x
          (let ((bb-list (schedule-back (remove-bb! x) bb-list*)))
            (queue-put! ordered-blocks x)
            bb-list)
          bb-list*)))

    (define (schedule-forw bb)
      (queue-put! ordered-blocks bb)
      (let ((x (succ-bb bb)))
        (if x
          (begin
            (schedule-forw (remove-bb! x))
            (let ((y (succ-bb bb)))
              (if y
                (schedule-around (remove-bb! y)))))))
      (schedule-refs bb))

    (define (schedule-refs bb)
      (for-each
        (lambda (lbl)
          (let ((x (lbl-num->bb lbl bbs)))
            (if (left-to-schedule? x)
                (schedule-around (remove-bb! x)))))
        (bb-references bb)))

    (schedule-from (remove-bb! (lbl-num->bb (bbs-entry-lbl-num bbs) bbs)))

    (let ((new-bbs (make-bbs))
          (basic-blocks (make-stretchable-vector #f))
          (lbl-map (make-stretchable-vector #f)))

      (define (replacement-lbl-num lbl)
        (or (stretchable-vector-ref lbl-map lbl) lbl))

      (for-each
       (lambda (bb)
         (let* ((old-num (label-lbl-num (bb-label-instr bb)))
                (new-num (bbs-new-lbl! new-bbs)))
           (stretchable-vector-set! basic-blocks new-num bb)
           (stretchable-vector-set! lbl-map old-num new-num)))
       (queue->list ordered-blocks))

      (let loop ((i bbs-first-lbl))
        (if (< i (bbs-next-lbl-num new-bbs))
            (begin
              (bb-clone-replacing-lbls
               (stretchable-vector-ref basic-blocks i)
               new-bbs
               replacement-lbl-num
               #t)
              (loop (+ i 1)))))

      (bbs-entry-lbl-num-set!
       new-bbs
       (replacement-lbl-num (bbs-entry-lbl-num bbs)))

      (bbs-determine-refs! new-bbs)

;;      (set! new-bbs (bbs-type-analysis! new-bbs))

;;      (bbs-determine-refs! new-bbs)

;;      (bbs-dominators! new-bbs)

      new-bbs)))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Sequentialization of a basic block set:
;; --------------------------------------

;; The procedure 'bbs->code-list' transforms a 'purified' basic block set
;; into a sequence of virtual machine instructions.  Each element of the
;; resulting list is a 'code' object that contains a GVM instruction,
;; a pointer to the basic block it came from and a `slots needed' index
;; that specifies the minimum number of slots that have to be kept (relative
;; to the start of the frame) after the instruction is executed.
;; The first element of the code list is the entry label for the piece of code.

(define (make-code bb gvm-instr sn)     (vector bb gvm-instr sn))
(define (code-bb code)                  (vector-ref code 0))
(define (code-gvm-instr code)           (vector-ref code 1))
(define (code-slots-needed code)        (vector-ref code 2))
(define (code-slots-needed-set! code n) (vector-set! code 2 n))

(define (bbs->code-list bbs)
  (let ((code-list (linearize bbs)))
    (setup-slots-needed! code-list)
    code-list))

(define (linearize bbs) ; convert bbs into list of GVM instructions
  (let ((code-queue (queue-empty)))

    (define (put-bb bb)

      (define (put-instr gvm-instr)
        (queue-put! code-queue (make-code bb gvm-instr #f)))

      (put-instr (bb-label-instr bb))
      (for-each put-instr (bb-non-branch-instrs bb))
      (put-instr (bb-branch-instr bb)))

    (bbs-for-each-bb put-bb bbs)
    (queue->list code-queue)))

(define (setup-slots-needed! code-list) ; setup slots-needed field

  ; Backward pass to set slots-needed field

  (let loop1 ((lst (reverse code-list)) (sn-rest #f))
    (if (pair? lst)
      (let* ((code (car lst))
             (gvm-instr (code-gvm-instr code)))
        (loop1
         (cdr lst)
         (case (gvm-instr-kind gvm-instr)

           ((label)
            (if (> sn-rest (frame-size (gvm-instr-frame gvm-instr)))
              (compiler-internal-error
                "setup-slots-needed!, incoherent slots needed for label"))
            (code-slots-needed-set! code sn-rest)
            #f)

           ((ifjump switch jump)
            (let ((sn (frame-size (gvm-instr-frame gvm-instr))))
              (code-slots-needed-set! code sn)
              (need-gvm-instr gvm-instr sn)))

           (else
            (code-slots-needed-set! code sn-rest)
            (need-gvm-instr gvm-instr sn-rest))))))))

(define (need-gvm-instrs non-branch branch)
  (if (pair? non-branch)
    (need-gvm-instr (car non-branch)
                    (need-gvm-instrs (cdr non-branch) branch))
    (need-gvm-instr branch
                    (frame-size (gvm-instr-frame branch)))))

(define (need-gvm-instr gvm-instr sn-rest)
  (case (gvm-instr-kind gvm-instr)

    ((label)
     sn-rest)

    ((apply)
     (let ((loc (apply-loc gvm-instr)))
       (need-gvm-opnds (apply-opnds gvm-instr)
         (need-gvm-loc-opnd loc
           (need-gvm-loc loc sn-rest)))))

    ((copy)
     (let ((loc (copy-loc gvm-instr)))
       (need-gvm-opnd (copy-opnd gvm-instr)
         (need-gvm-loc-opnd loc
           (need-gvm-loc loc sn-rest)))))

    ((close)
     (let ((parms (close-parms gvm-instr)))

       (define (need-parms-opnds p)
         (if (null? p)
           sn-rest
           (need-gvm-opnds (closure-parms-opnds (car p))
             (need-parms-opnds (cdr p)))))

       (define (need-parms-loc p)
         (if (null? p)
           (need-parms-opnds parms)
           (let ((loc (closure-parms-loc (car p))))
             (need-gvm-loc-opnd loc
               (need-gvm-loc loc (need-parms-loc (cdr p)))))))

       (need-parms-loc parms)))

    ((ifjump)
     (need-gvm-opnds (ifjump-opnds gvm-instr) sn-rest))

    ((switch)
     (need-gvm-opnd (switch-opnd gvm-instr) sn-rest))

    ((jump)
     (need-gvm-opnd (jump-opnd gvm-instr) sn-rest))

    (else
     (compiler-internal-error
       "need-gvm-instr, unknown 'gvm-instr':" gvm-instr))))

(define (need-gvm-loc loc sn-rest)
  (if (and loc (stk? loc) (>= (stk-num loc) sn-rest))
    (- (stk-num loc) 1)
    sn-rest))

(define (need-gvm-loc-opnd gvm-loc slots-needed)
  (if (and gvm-loc (clo? gvm-loc))
    (need-gvm-opnd (clo-base gvm-loc) slots-needed)
    slots-needed))

(define (need-gvm-opnd gvm-opnd slots-needed)
  (if gvm-opnd
    (cond ((stk? gvm-opnd)
           (max (stk-num gvm-opnd) slots-needed))
          ((clo? gvm-opnd)
           (need-gvm-opnd (clo-base gvm-opnd) slots-needed))
          (else
           slots-needed))
    slots-needed))

(define (need-gvm-opnds gvm-opnds slots-needed)
  (if (null? gvm-opnds)
    slots-needed
    (need-gvm-opnd (car gvm-opnds)
                   (need-gvm-opnds (cdr gvm-opnds) slots-needed))))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Dominators:
;; ----------

(define (bbs-dominators! bbs)

  (define all-lbls '())

  (define (intersect lbl a b)
    (keep (lambda (x) (or (= x lbl) (memv x b))) a))

  (define (intersect-multi lbl lst)
    (let loop ((lst lst) (result all-lbls))
      (if (pair? lst)
          (loop (cdr lst) (intersect lbl result (car lst)))
          result)))

  (bbs-for-each-bb
   (lambda (bb)
     (set! all-lbls (cons (bb-lbl-num bb) all-lbls)))
   bbs)

  (set! all-lbls (reverse all-lbls))

  (bbs-for-each-bb
   (lambda (bb)
     (let ((label (bb-label-instr bb)))
       (instr-comment-add! label 'doms all-lbls)))
   bbs)

  (let* ((entry-lbl (bbs-entry-lbl-num bbs))
         (bb (lbl-num->bb entry-lbl bbs))
         (label (bb-label-instr bb)))
    (instr-comment-add! label 'doms (list entry-lbl)))

  (let loop ()
    (define changed? #f)
    (bbs-for-each-bb
     (lambda (bb)
       (if (not (= (bbs-entry-lbl-num bbs) (bb-lbl-num bb)))
           (let* ((label
                   (bb-label-instr bb))
                  (precedents
                   (bb-precedents bb))
                  (old
                   (instr-comment-get (gvm-instr-comment label)
                                'doms))
                  (new
                   (intersect-multi (bb-lbl-num bb)
                                    (map (lambda (p)
                                           (instr-comment-get
                                            (bb-label-instr (lbl-num->bb p bbs))
                                            'doms))
                                         precedents))))
             (if (not (equal? old new))
                 (begin
                   (instr-comment-add! label 'doms new)
                   (set! changed? #t))))))
     bbs)
    (if changed? (loop)))

  (bbs-for-each-bb
   (lambda (bb)
     (let* ((label (bb-label-instr bb))
            (doms
             (map (lambda (lbl)
                    (string-append " " (format-gvm-lbl lbl '())))
                  (instr-comment-get label 'doms))))
       (if (pair? doms)
           (instr-comment-add!
            label
            'cfg-bb-info
            (list (cons 'info (string-concatenate doms)))))))
   bbs))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Type analysis:
;; -------------

(define debug-bbv? #f)
(define track-version-history? #f)

(define instr-cost 1)
(define call-cost 100)

(define (bbs-type-specialize bbs)

  (define (any-bb-has-version-limit-above-0?)
    (let ((has-version-limit-above-0? #f))

      (bbs-for-each-bb
       (lambda (bb)
         (if (> (bb-version-limit bb) 0)
             (set! has-version-limit-above-0? #t)))
       bbs)

      has-version-limit-above-0?))

  (if (any-bb-has-version-limit-above-0?)
      (bbs-type-specialize* bbs) ;; create a specialized bbs
      bbs)) ;; leave bbs intact

(define (bb-version-limit bb)
  (let* ((node (instr-comment-get (bb-label-instr bb) 'node))
         (env (node-env node)))
    (if env (version-limit env) 0)))

(define (show-version-history-of-lbl lbl)
  #t #;
  (and (>= lbl 52) (<= lbl 52))) ;; filter these labels

(define (bbs-type-specialize* bbs)

  (define-macro (reachability-debug lbl . rest)
    #f)
  (define reachability-debug-lbl 1)
  (define (reachability-debug* lbl . rest)
    (let ((result (and reachability-debug-lbl (= lbl reachability-debug-lbl))))
      (if result (pp (append rest (list lbl))))
      result))

;;  (define column-sep "\x23b9;") ;; for display of history of versions
  (define column-sep ":") ;; for display of history of versions

  (define details-sep #\_) ;; for separating details in history of versions

  (define tctx (make-tctx))

  (define new-bbs (make-bbs))

  (define versions (make-table))
  (define lbl-mapping (make-table))

  (define (replacement-lbl-num lbl)
    (let ((x (table-ref lbl-mapping lbl #f)))
      (if (or (not x) (= x lbl))
          lbl
          (replacement-lbl-num x))))

  (define (type-singleton->opnd type)
    (let ((val (type-singleton-val type)))
      (if (lbl-obj? val)
          (make-lbl (lbl-obj-lbl val))
          (make-obj val))))

  (define (type-singleton->new-opnd type)
    (let ((val (type-singleton-val type)))
      (if (lbl-obj? val)
          (make-lbl (lbl-obj-new-lbl val))
          (make-obj val))))

  (define (generic-entry-frame-types frame)
    (let* ((nb-regs (length (frame-regs frame)))
           (nb-slots (length (frame-slots frame)))
           (nb-closed (length (frame-closed frame)))
           (types (make-locenv nb-regs nb-slots nb-closed #f)))
      (locenv-set
       types
       (gvm-loc->locenv-index types return-addr-reg)
       (make-type-motley-non-fixnum type-return-bit))))

  (define (resized-frame-types-remove-dead frame types)
    (let* ((regs (frame-regs frame))
           (nb-regs (length regs))
           (slots (frame-slots frame))
           (nb-slots (length slots))
           (nb-closed
            (if (frame-live? closure-env-var frame)
                (length (frame-closed frame))
                0))
           (new-types
            (locenv-resize-from-lengths
             types
             (vector nb-regs nb-slots nb-closed)
             0
             #f)))

      (define (remove-if-not-live! var gvm-loc)
        (if (not (frame-live? var frame))
            (let ((dst-loc (gvm-loc->locenv-index new-types gvm-loc)))
              ;; once dead, a slot count contain anything for all we care
              (locenv-set! new-types dst-loc type-top))))

      (let loop1 ((i 1) (slots slots))
        (if (pair? slots)
            (begin
              (remove-if-not-live! (car slots) (make-stk (+ (- nb-slots i) 1)))
              (loop1 (+ i 1) (cdr slots)))))

      (let loop2 ((i 0) (regs regs))
        (if (pair? regs)
            (begin
              (remove-if-not-live! (car regs) (make-reg i))
              (loop2 (+ i 1) (cdr regs)))))

      new-types))

  (define (resized-frame-types frame types)
    (locenv-resize
     types
     (length (frame-regs frame))
     (length (frame-slots frame))
     (length (frame-closed frame))
     0
     #f))

  (define (types-merge2 types1 types2 widen?)
    (locenv-merge types1
                  types2
                  0
                  (lambda (type1 type2)
                    (type-union tctx type1 type2 widen?))))

  (define (types-merge-multi types-list widen?)
    (let loop ((types (car types-list)) (lst (cdr types-list)))
      (if (pair? lst)
          (loop (types-merge2 types (car lst) widen?)
                (cdr lst))
          types)))

  (define nb-versions (make-table))

  (define (make-bbvctx types) (vector types 0 '())) ;; TODO: cost and path deprecated?
  (define (bbvctx-types bbvctx) (vector-ref bbvctx 0))
  (define (bbvctx-cost bbvctx) (vector-ref bbvctx 1))
  (define (bbvctx-path bbvctx) (vector-ref bbvctx 2))

  (define (walk-bbs bbs)

    (define work-queue (queue-empty))

    (define-type queue-task bb version-lbl)

    (define orig-lbl-mapping (make-table))
    (define (orig-lbl-mapping-set! lbl orig-lbl) (table-set! orig-lbl-mapping lbl orig-lbl))
    (define (orig-lbl-mapping-ref lbl) (table-ref orig-lbl-mapping lbl))
    (define (new-lbl! orig-lbl)
      (let ((new-lbl (bbs-new-lbl! new-bbs)))
        (orig-lbl-mapping-set! new-lbl orig-lbl)
        new-lbl))
    (define (new-lbl? lbl bbs) (not (lbl-num->bb lbl bbs)))

    (define (reachable? lbl) (connected? BFSTree lbl)) 

    (define (bbs-cleanup) 
      ;; remove unreachable bb
      ;; required to avoid having uninitialized bb in the bbs
      (bbs-for-each-bb
        (lambda (bb)
          (let ((lbl (bb-lbl-num bb)))
            (when (not (reachable? lbl))
                (bbs-bb-remove! new-bbs lbl))))
        new-bbs))

    (define version-types-table (make-table))

    (define (get-version-types lbl)
      (table-ref version-types-table lbl))

    (define (set-version-types! lbl types)
      (table-set! version-types-table lbl types))

    (define (track-version-history lbl operation) ;; track history of versions
      (if (and track-version-history? (show-version-history-of-lbl lbl))
          (let* ((bb (lbl-num->bb lbl bbs))
                  (label (bb-label-instr bb))
                  (frame (gvm-instr-frame label))
                  (bb-versions (table-ref versions lbl))
                  (types-lbl-alist (bb-versions-active-lbl->list bb-versions sort?: #t))
                  (text-grid (bb-versions-text-grid bb-versions))
                  (version-index-tbl (bb-versions-index-table bb-versions))
                  (options '(brief new))
                  (col (max 1 (text-grid-cols text-grid)))
                  (op (car operation))
                  (from-lbl (cadr operation)))

            (if (and (pair? types-lbl-alist) (memq op '(add merge)))
                (let* ((newest-types-lbl (last types-lbl-alist))
                        (types (car newest-types-lbl))
                        (new-lbl (cdr newest-types-lbl)))
                  (or (table-ref version-index-tbl new-lbl #f)
                      (let ((index (table-length version-index-tbl)))
                        (table-set! version-index-tbl new-lbl index)
                        (text-grid-set! text-grid
                          (+ index 2)
                          0
                          (string-append
                          (format-gvm-lbl new-lbl '(new))
                          (if from-lbl
                              (string-append
                                "<-"
                                (format-gvm-lbl from-lbl '(new)))
                              "")))
                        index))))

            (let ((header (format-frame frame #f 'header options))
                  (info
                    (if from-lbl
                        (string-append
                        (if (memq op '(add merge))
                            " <-"
                            " ")
                        (format-gvm-lbl from-lbl '(new)))
                        "")))

              (text-grid-set!
                text-grid
                0
                col
                column-sep)

              (case op
                ((add)
                  (text-grid-set!
                  text-grid
                  0
                  (+ col 1)
                  (list 'span
                        (length header)
                        (string-append "ADD" info))))
                ((merge)
                  (text-grid-set!
                  text-grid
                  0
                  (+ col 1)
                  (list 'span
                        (length header)
                        (string-append "MERGE" info))))
                ((gc)
                  (text-grid-set!
                  text-grid
                  0
                  (+ col 1)
                  (list 'span
                        (length header)
                        (string-append "GC" info)))))

              (text-grid-set!
                text-grid
                1
                col
                column-sep)

              (text-grid-line-set!
                text-grid
                1
                (+ col 1)
                header)

              (if (pair? (cddr operation))
                  (let* ((details
                          (caddr operation))
                          (index
                          (table-length version-index-tbl))
                          (width
                          (apply max (map string-length details)))
                          (c
                          col))
                    (for-each
                      (lambda (h)
                        (text-grid-set!
                        text-grid
                        (+ index 2)
                        (+ c 1)
                        details-sep)
                        (set! c (+ c 1)))
                      header)
                    (for-each
                      (lambda (line)
                        (text-grid-set!
                        text-grid
                        (+ index 3)
                        (+ col 1)
                        (list 'span
                              (length header)
                              line))
                        (set! index (+ index 1)))
                      details))))

            (for-each
              (lambda (types-lbl)
                (let* ((types (car types-lbl))
                      (version-lbl (cdr types-lbl))
                      (i (table-ref version-index-tbl version-lbl))
                      (typs (format-frame frame types 'types options)))
                  (text-grid-line-set! text-grid (+ i 2) (+ col 1) typs)))
              types-lbl-alist))))

    (define (reach lbl from-lbl bbvctx)
      (let* ((types-before (bbvctx-types bbvctx))
              (bb (lbl-num->bb lbl bbs))
              (label (bb-label-instr bb))
              (frame (gvm-instr-frame label))
              (types-before
              (if (and (eq? (label-kind label) 'entry)
                        (or (pair? (label-entry-keys label)) ;; label with "complex" parameter handling?
                            (pair? (label-entry-opts label))
                            (label-entry-rest? label)))
                  (generic-entry-frame-types frame)
                  (resized-frame-types-remove-dead frame types-before)))
              (bb-versions (get-bb-versions bb))
              (old-version (bb-versions-all-lbl-get bb-versions types-before))
              (most-recent-version
                (and old-version (replacement-lbl-num old-version)))
              (version-types
                (if most-recent-version
                    (get-version-types most-recent-version)
                    types-before))
              (version-is-live?
                (and most-recent-version
                    (bb-versions-active-lbl-get bb-versions version-types))))
        (if version-is-live?
            (begin
              (reachability-debug most-recent-version 'reaching 'live)
              (if from-lbl (add-edge! BFSTree from-lbl most-recent-version onrevive))
              most-recent-version)
            (let* ((new-lbl (or most-recent-version (new-lbl! lbl))))
              (bb-versions-active-lbl-add! bb-versions version-types new-lbl)
              (track-version-history lbl (list 'add from-lbl)) ;; track history of versions
              (queue-put! work-queue (make-queue-task bb new-lbl))
              (reachability-debug new-lbl 'reaching 'anew)
              (if from-lbl (add-edge! BFSTree from-lbl new-lbl onrevive))
              new-lbl))))

    (define (walk-bb bb types-before new-lbl)
      (let ((orig-lbl (bb-lbl-num bb))
            (new-bb #f))

        (define show #t)
        (define (reach* lbl types-after)
          (if (and debug-bbv? show)
              (begin
                (write-bb new-bb '(new) (current-output-port))
                (print "...\n")
                (set! show #f)))
          (reach lbl
                  new-lbl
                  (make-bbvctx
                  (let ((dest-fs (bb-entry-frame-size (lbl-num->bb lbl bbs))))
                    (types-keep-topmost-slots types-after dest-fs)))))

      (define (reach-ret* lbl from-lbl types-after)
          (if (and debug-bbv? show)
              (begin
                (write-bb new-bb '(new) (current-output-port))
                (print "...\n")
                (set! show #f)))
          (reach lbl
                  from-lbl
                  (make-bbvctx
                  (let* ((bb (lbl-num->bb lbl bbs))
                          (label (bb-label-instr bb))
                          (frame (gvm-instr-frame label)))
                    (types-truncate types-after frame)))))

      (define (walk-opnd gvm-opnd)
        (and gvm-opnd
              (if (lbl? gvm-opnd)
                  (let* ((lbl
                          (lbl-num gvm-opnd))
                        (bb
                          (lbl-num->bb lbl bbs))
                        (label
                          (bb-label-instr bb))
                        (types-bef
                          (generic-entry-frame-types (gvm-instr-frame label))))
                    (make-lbl (reach* lbl types-bef)))
                  gvm-opnd)))

      (define (walk-loc gvm-opnd)
        (walk-opnd gvm-opnd))

      (define (walk-instr gvm-instr types-before)

        (define (opnd-type opnd new-opnd types)
          (cond ((not new-opnd)
                  type-bot)
                ((locenv-loc? new-opnd)
                  (locenv-ref types
                              (gvm-loc->locenv-index types new-opnd)))
                ((obj? new-opnd)
                  (make-type-singleton (obj-val new-opnd)))
                ((lbl? new-opnd)
                  (let* ((new-lbl (lbl-num new-opnd))
                        (orig-lbl (orig-lbl-mapping-ref new-lbl))
                        (kind (bb-label-kind (lbl-num->bb orig-lbl bbs)))
                        (lbl-obj (make-lbl-obj orig-lbl new-lbl kind #f)))
                    (make-type-from-lbl-obj lbl-obj)))
                (else
                  ;; global variable
                  (make-type-top-with-new-length-bound bb))))

        (define (opnd-constantify opnd new-opnd types-before)
          (if (locenv-loc? opnd)
              (let ((type (opnd-type opnd new-opnd types-before)))
                (if (type-singleton? type)
                    (type-singleton->new-opnd type)
                    new-opnd))
              new-opnd))

        (let ((types-after
                (resized-frame-types-remove-dead
                (gvm-instr-frame gvm-instr)
                types-before)))


          (case (gvm-instr-kind gvm-instr)

            ((label)
;;               (pprint '****label)
              (let ((new-instr
                    (case (label-kind gvm-instr)

                      ((simple)
                        (make-label-simple
                        new-lbl
                        (gvm-instr-frame gvm-instr)
                        (gvm-instr-comment gvm-instr)))

                      ((entry)
                        (make-label-entry
                        new-lbl
                        (label-entry-nb-parms gvm-instr)
                        (label-entry-opts gvm-instr)
                        (label-entry-keys gvm-instr)
                        (label-entry-rest? gvm-instr)
                        (label-entry-closed? gvm-instr)
                        (gvm-instr-frame gvm-instr)
                        (gvm-instr-comment gvm-instr)))

                      ((return)
                        (make-label-return
                        new-lbl
                        (gvm-instr-frame gvm-instr)
                        (gvm-instr-comment gvm-instr)))

                      ((task-entry)
                        (make-label-task-entry
                        new-lbl
                        (gvm-instr-frame gvm-instr)
                        (gvm-instr-comment gvm-instr)))

                      ((task-return)
                        (make-label-task-return
                        new-lbl
                        (gvm-instr-frame gvm-instr)
                        (gvm-instr-comment gvm-instr)))

                      (else
                        (compiler-internal-error
                        "walk-instr, unknown 'gvm-instr':" gvm-instr)))))
                (gvm-instr-types-set! new-instr types-after)
                (instr-comment-add! new-instr 'orig-lbl orig-lbl)
                new-instr))

            ((apply)
;;               (pprint '****apply)
              (let* ((prim
                      (apply-prim gvm-instr))
                    (opnds
                      (apply-opnds gvm-instr))
                    (new-opnds
                      (map walk-opnd opnds))
                    (type-opnds
                      (map (lambda (opnd new-opnd)
                            (opnd-type opnd new-opnd types-before))
                          opnds
                          new-opnds))
                    (args
                      (map make-call-arg type-opnds))
                    (call
                      (make-call prim args))
                    (spec-call
                      (let* ((node (instr-comment-get gvm-instr 'node))
                            (env (node-env node)))
                        (if env
                            (specialize-call call env)
                            call)))
                    (prim2
                      (call-proc spec-call))
                    (args2
                      (call-args spec-call))
                    (loc
                      (walk-loc (apply-loc gvm-instr)))
                    (type-infer
                      (proc-obj-type-infer prim2))
                    (dst-type
                      (if type-infer
                          (type-infer tctx type-opnds)
                          (make-type-top-with-new-length-bound bb)))
                    (types-after
                      (if (locenv-loc? loc)
                          (let ((dst-loc
                                (gvm-loc->locenv-index types-after loc)))
                            (locenv-set types-after ;; change type of dst-loc
                                        dst-loc
                                        dst-type))
                          types-after)) ;; no change
                    (new-instr
                      (if (and (not (proc-obj-side-effects? prim2))
                              (type-singleton? dst-type))
                          (make-copy
                          (type-singleton->new-opnd dst-type)
                          loc
                          (gvm-instr-frame gvm-instr)
                          (gvm-instr-comment gvm-instr))
                          (let ((new-opnds2
                                (map (lambda (arg)
                                        (let ((arg-type (call-arg-val arg)))
                                          (if (type-singleton? arg-type)
                                              (type-singleton->new-opnd arg-type)
                                              (let ((i (pos-in-list arg args)))
                                                (if i
                                                    (list-ref new-opnds i)
                                                    (compiler-internal-error
                                                    "bbs-type-specialize*, can't find operand"))))))
                                      args2)))
                            (make-apply
                            prim2
                            new-opnds2
                            loc
                            (gvm-instr-frame gvm-instr)
                            (gvm-instr-comment gvm-instr))))))
                (gvm-instr-types-set! new-instr types-after)
                new-instr))

            ((copy)
;;               (pprint '****copy)
              (let* ((opnd
                      (copy-opnd gvm-instr))
                    (new-opnd
                      (walk-opnd opnd))
                    (loc
                      (walk-loc (copy-loc gvm-instr)))
                    (types-before
                      (resized-frame-types (gvm-instr-frame gvm-instr) types-before))
                    (types-after
                      (resized-frame-types-remove-dead
                        (gvm-instr-frame gvm-instr)
                        (if (locenv-loc? loc)
                            (let ((dst-loc
                                    (gvm-loc->locenv-index types-before loc)))
                              (if (locenv-loc? new-opnd)
                                  (let ((src-loc
                                          (gvm-loc->locenv-index types-before new-opnd)))
                                    (locenv-copy types-before dst-loc src-loc))
                                  (locenv-set types-before
                                              dst-loc
                                              (opnd-type opnd new-opnd types-before))))
                            types-before))) ;; no change
                    (new-instr
                      (make-copy
                      (opnd-constantify opnd new-opnd types-before)
                      loc
                      (gvm-instr-frame gvm-instr)
                      (gvm-instr-comment gvm-instr))))
                (gvm-instr-types-set! new-instr types-after)
                new-instr))

            ((close)
;;               (pprint '****close) (exit 1)
              (let loop1 ((lst (close-parms gvm-instr))
                          (types-after (resized-frame-types
                                        (gvm-instr-frame gvm-instr)
                                        types-before)))
                (if (pair? lst)
                    (loop1
                    (cdr lst)
                    (let* ((parms (car lst))
                            (loc (walk-loc (closure-parms-loc parms))))
                      (if (locenv-loc? loc)
                          (let ((dst-loc
                                  (gvm-loc->locenv-index types-after loc)))
                            (locenv-set types-after
                                        dst-loc
                                        type-procedure))
                          types-after)))
                    (let loop2 ((lst (close-parms gvm-instr))
                                (rev-parms '()))
                      (if (pair? lst)
                          (loop2
                          (cdr lst)
                          (cons
                            (let* ((parms
                                    (car lst))
                                  (lbl
                                    (closure-parms-lbl parms))
                                  (entry-bb
                                    (lbl-num->bb lbl bbs))
                                  (entry-label
                                    (bb-label-instr entry-bb))
                                  (opnds
                                    (closure-parms-opnds parms))
                                  (new-opnds
                                    (map walk-opnd opnds))
                                  (types-entry
                                    (let loop ((opnds opnds)
                                              (new-opnds new-opnds)
                                              (i 1)
                                              (types-entry
                                                (generic-entry-frame-types
                                                (gvm-instr-frame entry-label))))
                                      (if (pair? new-opnds)
                                          (loop
                                          (cdr opnds)
                                          (cdr new-opnds)
                                          (+ i 1)
                                          (let* ((opnd
                                                  (car opnds))
                                                  (new-opnd
                                                  (car new-opnds))
                                                  (dst-loc
                                                  (gvm-loc->locenv-index
                                                    types-entry
                                                    (make-clo #f i)))
                                                  (type
                                                  (opnd-type opnd
                                                              new-opnd
                                                              types-after)))
                                            (locenv-set types-entry
                                                        dst-loc
                                                        type)))
                                          types-entry))))
                              (make-closure-parms
                              (closure-parms-loc parms)
                              (reach* lbl types-entry)
                              new-opnds))
                            rev-parms))
                          (let ((new-instr
                                (make-close
                                  (reverse rev-parms)
                                  (gvm-instr-frame gvm-instr)
                                  (gvm-instr-comment gvm-instr))))
                            (gvm-instr-types-set! new-instr
                                                  (resized-frame-types-remove-dead
                                                    (gvm-instr-frame gvm-instr)
                                                    types-after))
                            new-instr))))))

            ((ifjump)
;;               (pprint '****ifjump)
              (let* ((test
                      (ifjump-test gvm-instr))
                    (opnds
                      (ifjump-opnds gvm-instr))
                    (new-opnds
                      (map walk-opnd opnds))
                    (type-narrow
                      (proc-obj-type-narrow test))
                    (result-types
                      (and type-narrow
                          (type-narrow
                            tctx
                            (map (lambda (opnd new-opnd)
                                  (opnd-type opnd new-opnd types-before))
                                opnds
                                new-opnds))))
                    (new-instr
                      (if (pair? result-types)

                          (let ()

                            (define (narrow opnd-types)
                              (and opnd-types
                                  (locenv-update types-after new-opnds opnd-types)))

                            (let* ((true-types
                                    (narrow (car result-types)))
                                  (true-lbl
                                    (and true-types
                                        (reach* (ifjump-true gvm-instr)
                                                true-types)))
                                  (false-types
                                    (narrow (cdr result-types)))
                                  (false-lbl
                                    (and false-types
                                        (reach* (ifjump-false gvm-instr)
                                                false-types))))
                              (if true-lbl
                                  (if false-lbl
                                      (make-ifjump
                                      test
                                      new-opnds
                                      true-lbl
                                      false-lbl
                                      (ifjump-poll? gvm-instr)
                                      (gvm-instr-frame gvm-instr)
                                      (gvm-instr-comment gvm-instr))
                                      (make-jump
                                      (make-lbl true-lbl)
                                      #f
                                      #f
                                      (ifjump-poll? gvm-instr)
                                      #f
                                      (gvm-instr-frame gvm-instr)
                                      (gvm-instr-comment gvm-instr)))
                                  (if false-lbl
                                      (make-jump
                                      (make-lbl false-lbl)
                                      #f
                                      #f
                                      (ifjump-poll? gvm-instr)
                                      #f
                                      (gvm-instr-frame gvm-instr)
                                      (gvm-instr-comment gvm-instr))
                                      (error "impossible true and false outcomes from test" (proc-obj-name test))))))
                          (make-ifjump
                          test
                          new-opnds
                          (reach* (ifjump-true gvm-instr)
                                  types-after)
                          (reach* (ifjump-false gvm-instr)
                                  types-after)
                          (ifjump-poll? gvm-instr)
                          (gvm-instr-frame gvm-instr)
                          (gvm-instr-comment gvm-instr)))))
                (gvm-instr-types-set! new-instr types-after)
                new-instr))

            ((switch)
;;               (pprint '****switch) (exit 1)
              (let ((opnd (walk-opnd (switch-opnd gvm-instr))))
                '(for-each (lambda (c) (scan-obj (switch-case-obj c)))
                          (switch-cases gvm-instr))
                types-after))

            ((jump)
;;               (pprint '****jump)
              (let* ((opnd
                      (jump-opnd gvm-instr))
                    (opnd-type-before (and (locenv-loc? opnd) (opnd-type opnd opnd types-before)))
                    (opnd-singleton (and (type-singleton? opnd-type-before) (type-singleton-val opnd-type-before)))
                    (opnd-is-proc? (and opnd-singleton (proc-obj? opnd-singleton)))
                    (opnd-is-primitive? (and opnd-is-proc? (proc-obj-primitive? opnd-singleton)))
                    (ret
                      (jump-ret gvm-instr))
                    (types-return
                      (and ret
                          (let* ((result-loc
                                  (gvm-loc->locenv-index types-after (make-reg 1)))
                                  (types-at-ret
                                  (if (and (jump-safe? gvm-instr)
                                            (locenv-loc? opnd)
                                            (not opnd-is-proc?))
                                      ;; TODO: instead of repeating a resize, there should be a way
                                      ;; to check if opnd is still live in types-after
                                      (resized-frame-types (gvm-instr-frame gvm-instr)
                                        (locenv-set types-before
                                                  (gvm-loc->locenv-index types-before opnd)
                                                  type-procedure))
                                      types-after)))
                            (locenv-set types-at-ret
                                        result-loc
                                        (if use-return-point-versioning?
                                            (make-type-top-with-new-length-bound bb)
                                            type-top)))))
                    (new-ret
                      (and ret
                          (reach-ret* ret
                                      new-lbl
                                      types-return))) ;;;;;;;;;TODO
                    (types-after
                      (if new-ret
                          (locenv-set
                          types-after
                          (gvm-loc->locenv-index types-after return-addr-reg)
                          (make-type-from-lbl-obj
                            (make-lbl-obj ret new-ret 'return types-return)))
                          types-after))
                    (new-opnd
                      (if (locenv-loc? opnd)
                          (let ((type (opnd-type opnd opnd types-before)))
                            (if (type-singleton? type)
                                (let ((val (type-singleton-val type)))
                                  (if (lbl-obj? val)
                                      (let* ((lbl (lbl-obj-lbl val))
                                            (types (lbl-obj-types val))
                                            (merged-types
                                              (if types
                                                  (locenv-merge types
                                                                types-after
                                                                0
                                                                (lambda (type1 type2)
                                                                  type2))
                                                  types-after)))
                                        (make-lbl (reach* lbl
                                                          merged-types)))
                                      (make-obj val)))
                                opnd))
                          (if (lbl? opnd)
                              (make-lbl (reach* (lbl-num opnd)
                                                types-after))
                              opnd)))
                    (new-instr
                      (make-jump
                      new-opnd
                      new-ret
                      (jump-nb-args gvm-instr)
                      (jump-poll? gvm-instr)
                      (if (type-motley-included?
                            (type-motley-force tctx
                                              (opnd-type opnd new-opnd types-before))
                            type-procedure)
                          #f
                          (jump-safe? gvm-instr))
                      (gvm-instr-frame gvm-instr)
                      (gvm-instr-comment gvm-instr))))
                (gvm-instr-types-set! new-instr types-after)
                new-instr)))))

        (let ((new-label-instr (walk-instr (bb-label-instr bb) types-before)))
          (set! new-bb (make-bb new-label-instr new-bbs)))

        (let ((label-instr (bb-label-instr new-bb)))
          (instr-comment-add!
            label-instr
            'cfg-bb-info
            (list
            (cons 'info
                  (string-append (format-gvm-lbl orig-lbl '())
                                  "->"
                                  (format-gvm-lbl new-lbl '(new)))))))

        (let loop ((instrs
                    (bb-non-branch-instrs bb))
                    (types-before
                    (gvm-instr-types (bb-label-instr new-bb))))
          (if (pair? instrs)
              (let ((new-instr
                      (walk-instr (car instrs) types-before)))
                (bb-put-non-branch! new-bb new-instr)
                (loop (cdr instrs)
                      (gvm-instr-types new-instr)))
              (let ((new-instr
                      (walk-instr (bb-branch-instr bb) types-before)))
                (bb-put-branch! new-bb new-instr))))))

    (define (get-bb-versions bb)
      (get-bb-versions-from-lbl (bb-lbl-num bb)))

    (define (get-bb-versions-from-lbl lbl)
      (or (table-ref versions lbl #f)
          (let ((bb-versions
                  (if track-version-history?
                      (vector (make-table test: locenv-eqv?)
                              (make-table test: locenv-eqv?)
                              (make-text-grid)
                              (make-table))
                      (vector (make-table test: locenv-eqv?)
                              (make-table test: locenv-eqv?)))))
            (table-set! versions lbl bb-versions)
            bb-versions)))
    
    (define (bb-versions-active-lbl-get bb-versions types-before)
      (table-ref (vector-ref bb-versions 0) types-before #f))
    (define (bb-versions-active-lbl-remove! bb-versions types-before)
      (table-set! (vector-ref bb-versions 0) types-before))
    (define (bb-versions-active-lbl-add! bb-versions types-before version-lbl)
      (bb-versions-all-lbl-add! bb-versions types-before version-lbl)
      (table-set! (vector-ref bb-versions 0) types-before version-lbl))
    (define (bb-versions-active-lbl->list bb-versions #!key (sort? use-directional-widening?))
      (if sort?
          (list-sort (lambda (v1 v2) (< (cdr v1) (cdr v2)))
                (table->list (vector-ref bb-versions 0)))
          (table->list (vector-ref bb-versions 0))))
    (define (bb-versions-active-lbl-for-each f bb-versions)
      (table-for-each f (vector-ref bb-versions 0)))
    (define (bb-versions-active-lbl-length bb-versions)
      (table-length (vector-ref bb-versions 0)))
    (define (bb-versions-active-lbl-remove-unreachable! bb-versions)
      (define changed? #f)
      (for-each
        (lambda (type-lbl)
          (if (not (reachable? (replacement-lbl-num (cdr type-lbl))))
              (begin
                (set! changed? #t)
                (bb-versions-active-lbl-remove! bb-versions (car type-lbl)))))
        (bb-versions-active-lbl->list bb-versions))
      changed?)

    (define (bb-versions-all-lbl-get bb-versions types-before)
      (table-ref (vector-ref bb-versions 1) types-before #f))
    (define (bb-versions-all-lbl-add! bb-versions types-before version-lbl)
      (set-version-types! version-lbl types-before)
      (table-set! (vector-ref bb-versions 1) types-before version-lbl))

    (define (bb-versions-text-grid bb-versions)
      (vector-ref bb-versions 2))

    (define (bb-versions-index-table bb-versions)
      (vector-ref bb-versions 3))

    (define (need-merge? bb)
      (let* ((lbl (bb-lbl-num bb))
              (bb-versions (get-bb-versions bb)))
        (> (bb-versions-active-lbl-length bb-versions) (max 1 (bb-version-limit bb)))))

    (define (onrevive lbl)
      (if (new-lbl? lbl new-bbs)
          (let* ((orig-lbl (orig-lbl-mapping-ref lbl))
                  (bb (lbl-num->bb orig-lbl bbs))
                  (bb-versions (get-bb-versions-from-lbl orig-lbl)))
            ;(pp (list 'onrevive lbl)) 
            (reachability-debug lbl 'revive)
            (bb-versions-active-lbl-add!
              bb-versions
              (get-version-types lbl)
              lbl)
            (queue-put! work-queue (make-queue-task bb lbl)))))

    (define (onkill lbl)
      (let* ((orig-lbl (orig-lbl-mapping-ref lbl))
              (bb-versions (get-bb-versions-from-lbl orig-lbl)))
        ;(pp (list 'onkill lbl)) 
        (reachability-debug lbl 'kill)
        (bb-versions-active-lbl-remove-unreachable! bb-versions)))

    (define (merge bb)
      (let* ((lbl (bb-lbl-num bb))
              (bb-versions (get-bb-versions bb))
              (types-lbl-vect (list->vector (bb-versions-active-lbl->list bb-versions)))
              (in-out-details (find-merge-candidates tctx types-lbl-vect))
              (in (vector-ref in-out-details 0))
              (out (vector-ref in-out-details 1))
              (details (vector-ref in-out-details 2))
              (versions-to-merge (map (lambda (i) (vector-ref types-lbl-vect i)) in))
              (versions-to-keep (map (lambda (i) (vector-ref types-lbl-vect i)) out))
              (merged-types (types-merge-multi (map car versions-to-merge) #t))
              (existing-lbl-of-merged-type 
                (bb-versions-all-lbl-get bb-versions merged-types))
              (new-lbl (or (and existing-lbl-of-merged-type
                                (replacement-lbl-num existing-lbl-of-merged-type))
                            (new-lbl! lbl)))
              (merged-types (if (not existing-lbl-of-merged-type)
                                merged-types
                                (get-version-types new-lbl))))

        (bb-versions-active-lbl-add! bb-versions merged-types new-lbl)

        (for-each
          (lambda (types-lbl)
            (let ((types (car types-lbl))
                  (lbl (cdr types-lbl)))
              (table-set! lbl-mapping lbl new-lbl)
              (reachability-debug lbl 'merge new-lbl '<-)
              (reachability-debug new-lbl 'merge lbl '->)
              (if (not (eq? lbl new-lbl))
                  (replace!
                    BFSTree lbl new-lbl
                    onrevive
                    onkill))))
          versions-to-merge)

        (reachability-debug new-lbl 'merged 'created)

        (for-each
          (lambda (type-lbl) (bb-versions-active-lbl-remove! bb-versions (car type-lbl)))
          versions-to-merge)

        (track-version-history lbl (list 'merge #f details)) ;; track history of versions

        (if (new-lbl? new-lbl new-bbs)
            (queue-put! work-queue (make-queue-task bb new-lbl)))))

    (define bfs-source-node -1)
    (define BFSTree (make-BFSTree bfs-source-node))

    (let* ((entry-lbl
            (bbs-entry-lbl-num bbs))
            (entry-bb
            (lbl-num->bb entry-lbl bbs))
            (entry-label
            (bb-label-instr entry-bb))
            (types-before
            (generic-entry-frame-types (gvm-instr-frame entry-label))))

      (bbs-entry-lbl-num-set! new-bbs (reach entry-lbl #f (make-bbvctx types-before)))
      (add-edge! BFSTree bfs-source-node (bbs-entry-lbl-num new-bbs) onrevive)
      (let loop ()
        (let* ((task (queue-get! work-queue))
                (bb (queue-task-bb task))
                (version-lbl (queue-task-version-lbl task))
                (types (get-version-types version-lbl)))

          (reachability-debug version-lbl 'dequeued)

          (when (reachable? version-lbl)
            (if (need-merge? bb) (merge bb))
            (walk-bb bb types version-lbl))
          
          (if (not (queue-empty? work-queue)) (loop))))

      (bbs-entry-lbl-num-set! new-bbs (replacement-lbl-num (bbs-entry-lbl-num bbs)))

      (bbs-cleanup)))

  (define (finalize)

    (bbs-for-each-bb
     (lambda (bb)
       (bb-clone-replacing-lbls bb new-bbs replacement-lbl-num #f))
     new-bbs)

    new-bbs)

  (set! type-top-counter 0) ;; TODO: find a better place for this...

;;  (write-bbs bbs '() (current-output-port))

  (walk-bbs bbs)

  (if track-version-history?
      (bbs-for-each-bb
       (lambda (bb)
         (let* ((port (current-output-port))
                (lbl (bb-lbl-num bb))
                (bb-versions (table-ref versions lbl #f)))
           (if (and bb-versions (show-version-history-of-lbl lbl))
               (let ((text-grid (vector-ref bb-versions 2)))
                 (display "-------------------------------------------------------------------------------\n" port)
                 (text-grid-set! text-grid 0 (text-grid-cols text-grid) column-sep)
                 (let loop1 ((col 0))
                   (if (< col (text-grid-cols text-grid))
                       (let ((x (text-grid-ref text-grid 0 col)))
                         (if (equal? x column-sep)
                             (let loop2 ((row 1))
                               (if (< row (text-grid-rows text-grid))
                                   (begin
                                     (text-grid-set! text-grid row col x)
                                     (loop2 (+ row 1))))))
                         (loop1 (+ col 1)))))
                 (text-grid-display text-grid port)
                 (newline port)
                 (write-bb bb '() port)
                 (newline port)))))
       bbs))

  (finalize))

(define (debug-this-bb? bb)
  (let ((label (bb-label-instr bb))
        (lbl (bb-lbl-num bb)))

    (and (= 34 lbl)
         (let* ((node (instr-comment-get label 'node))
                (expr (and node (parse-tree->expression node))))
           (and expr
                (object->string expr 75))))

    #;
    (let* ((node (instr-comment-get label 'node))
           (expr (and node (parse-tree->expression node))))
      (and (pair? expr)
           (eq? 'lambda (car expr))
           (object->string expr 75)))))

;; Linear distance
(define (linear-type-distance tctx type1 type2)
  (define (bs type bitset)
    (+ (bitwise-and bitset (- (expt 2 30) 1))
       (if (type-motley-included? type type-fixnum)
           (expt 2 30)
           0)))
  (let* ((t1 (type-motley-force tctx type1))
         (t2 (type-motley-force tctx type2)))
    (+ (bit-count
        (bitwise-eqv (bs t1 (type-motley-mut-bitset t1))
                     (bs t2 (type-motley-mut-bitset t2))))
       (bit-count
        (bitwise-eqv (bs t1 (type-motley-not-mut-bitset t1))
                     (bs t2 (type-motley-not-mut-bitset t2)))))))

(define (types-count tctx type)
  (define count 0)
  (for-each-motley-bit tctx (lambda (_) (set! count (+ count 1))) (type-motley-force tctx type) #t)
  count)

;; Entropy-based distance
(define (entropy-difference tctx type1 type2)
  (define type-fixnum-marker (gensym))

  (define (geometric n) 
    (define r 1/10)
    (/ (- 1 (expt r n)) (- 1 r)))

  (define (geometric-difference type supertype)
    (- (geometric (types-count tctx supertype)) (geometric (types-count tctx type))))

  (let* ((t1 (type-motley-force tctx type1))
         (t2 (type-motley-force tctx type2))
         (merged (type-union tctx t1 t2 #f)))
    (norm1 (list (geometric-difference t1 merged) (geometric-difference t2 merged)))))

;; Sametypes strategy
(define (types-distance-sametypes tctx types1 types2)
  ;; sametypes chooses to merge 
  (define (compute-score types)
    (define (score type)
      (if (type-included? tctx type type-fixnum)
        1.001 ;; slightly favor fixnums
        (expt 1/10 (- (types-count tctx type) 1))))

    (define score-by-type '())

    (define (get-type-cell type)
      (let loop ((lst score-by-type))
        (cond
          ((null? lst)
            (set! score-by-type (cons (cons type 0) score-by-type))
            (car score-by-type))
          ((type-eqv? (caar lst) type)
            (car lst))
          (else
            (loop (cdr lst))))))

    (define (increment-score type)
      (let ((cell (get-type-cell type)))
        (set-cdr! cell (+ (cdr cell) (score type)))))
    
    (let ((len (vector-length types)))
      (let loop ((i locenv-start-regs))
        (if (< i len)
            (let* ((type (vector-ref types (+ i 1))))
              (increment-score type)
              (loop (+ i locenv-entry-size)))))
      (apply max (map cdr score-by-type))))
      
  ;; highscore means higher distance
  ;; the versions with two lowest score are merged
  ;; break ties with entropy strategy
  (let ((entropy (types-distance-entropy tctx types1 types2)))
    ;; merge these if they are nearly the same otherwise keep valuable versions
    (if (> entropy 0)
        (+ (* 100 (+ (compute-score types1) (compute-score types2)))
           (types-distance-entropy tctx types1 types2))
        0)))

(define (norm1 points) (apply + points))
(define (norm2 points) (sqrt (norm1 (map (lambda (x) (* x x)) points))))
(define (norm-inf points) (apply max points))

(define (make-types-distance-with-norm type-norm type-distance tctx types1 types2)
  (let ((len (vector-length types1)))
    (let loop ((i locenv-start-regs) (acc '()))
      (if (< i len)
          (let* ((type1 (vector-ref types1 (+ i 1)))
                  (type2 (vector-ref types2 (+ i 1))))
            (loop (+ i locenv-entry-size) (cons (type-distance tctx type1 type2) acc)))
          (type-norm acc)))))

(define (types-distance-entropy tctx types1 types2) (make-types-distance-with-norm norm1 entropy-difference tctx types1 types2))
(define (types-distance-linear tctx types1 types2) (make-types-distance-with-norm norm1 linear-type-distance tctx types1 types2))

(define (types-distance-feeley tctx types1 types2)

  (declare (generic))

  (define single-type-specificity 31)

  (define (specificity type)
    ;; returns an integer indicating how specific that type is
    ;; roughly speaking the log2 of the cardinality of the possible values
    ;; the whole fixnum range counts as 31
    ;; other types count as 31
    ;; 0 is the most specific (a singleton type), 1 means 2 possible values, etc
    (if (type-singleton? type)
        0
        (let* ((t (type-motley-force tctx type))
               (fixnum-range (type-fixnum-range-numeric tctx t))
               (lo (type-fixnum-range-lo fixnum-range))
               (hi (type-fixnum-range-hi fixnum-range))
               (n (if (>= hi lo)
                      (integer-length (+ 1 (- hi lo)))
                      0)))
          (+ n
             (* single-type-specificity
                (bit-count
                 (bitwise-and (- (expt 2 30) 1)
                              (bitwise-ior (type-motley-mut-bitset t)
                                           (type-motley-not-mut-bitset t)))))))))

  (define (specificity-of-types types)
    (let ((len (vector-length types1)))
      (let loop ((i locenv-start-regs) (acc 0) (n 0))
        (if (< i len)
            (let* ((type (vector-ref types (+ i 1)))
                   (spec (specificity type)))
              (loop (+ i locenv-entry-size) (+ acc spec) (+ n 1)))
            (quotient acc n)))))

  (define (usefulness-of-types types)
    ;; 0 is the most useful (a single type)
    (abs (- (specificity-of-types types)
            single-type-specificity)))

  (let* ((len (vector-length types1))
         (ut1 (usefulness-of-types types1))
         (ut2 (usefulness-of-types types2)))
    (let loop ((i locenv-start-regs) (acc 0))
      (if (< i len)
          (let* ((type1 (vector-ref types1 (+ i 1)))
                 (type2 (vector-ref types2 (+ i 1)))
                 (ltd (linear-type-distance tctx type1 type2))
                 (dist ltd))
            (loop (+ i locenv-entry-size) (+ acc dist)))
          (+ (* acc 100000) (quotient 99999 (+ 1 ut1 ut2)))))))

(define types-distance #f)

(define (set-bbv-merge-strategy! opt)
  (set! types-distance
    (case opt
      ((entropy) types-distance-entropy)
      ((sametypes) types-distance-sametypes)
      ((linear) types-distance-linear)
      ((feeley #f) types-distance-feeley)
      (else (error "unknown bbv-merge-strategy strategy" opt)))))

(define (find-merge-candidates tctx types-lbl-vect)
  (let* ((n (vector-length types-lbl-vect))
         (min-dist 99999999)
         (min-dist-pair #f)
         (dist-matrix (make-vector n))
         (details '()))

    (define (get-distance i j)
      (vector-ref
        (vector-ref dist-matrix (max i j))
        (min i j)))

    (define (partition-distance i d details)
      (let loop ((j 0) (in (list i)) (out '()))
        (cond
         ((= j n)
          (vector in out details))
         ((= i j)
          (loop (+ j 1) in out))
         ((<= (apply max (map (lambda (i) (get-distance i j)) in)) d)
          (loop (+ j 1) (cons j in) out))
         (else
          (loop (+ j 1) in (cons j out))))))

    (for-each
      (lambda (i)
        (let ((row (make-vector (+ i 1) 0)))
          (vector-set! dist-matrix i row)
          (for-each
            (lambda (j)
              (let* ((ti (vector-ref types-lbl-vect i))
                     (tj (vector-ref types-lbl-vect j))
                     (d (types-distance tctx (car ti) (car tj))))
                (if track-version-history?
                    (set! details
                      (cons (string-append
                             (format-gvm-lbl (cdr ti) '(new))
                             " "
                             (format-gvm-lbl (cdr tj) '(new))
                             " = "
                             (number->string d))
                            details)))
                (vector-set! row j d)
                (when (< d min-dist)
                  (set! min-dist d)
                  (set! min-dist-pair (cons i j)))))
            (iota i))))
      (iota n))

    (partition-distance (car min-dist-pair) min-dist details)))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Environments for virtual machine locations:
;; ------------------------------------------

;; The locenv structure is used to track the properties (currently
;; only the type) of the contents of virtual machine locations
;; (registers, stack slot and closed variables).  It also tracks if
;; two locations are in the same equivalence class (i.e. they contain
;; the same value).  There could be different equivalence classes for
;; eq?, eqv?, etc but currently only eq? equivalence is tracked.

(define locenv-start-regs 1)
(define locenv-entry-size 2)

(define (locenv-loc? gvm-opnd)
  (and gvm-opnd
       (or (reg? gvm-opnd)
           (stk? gvm-opnd)
           (clo? gvm-opnd))))

(define (gvm-loc->locenv-index locenv gvm-loc)
  (if (reg? gvm-loc)
      (+ locenv-start-regs
         (* locenv-entry-size (reg-num gvm-loc)))
      (let ((start-slots
             (+ locenv-start-regs
                (* locenv-entry-size
                   (vector-ref (vector-ref locenv 0) 0)))))
        (if (stk? gvm-loc)
            (+ start-slots
               (* locenv-entry-size
                  (- (stk-num gvm-loc) 1)))
            ;; (clo? gvm-loc) must be true
            (let ((start-closed
                   (+ start-slots
                      (* locenv-entry-size
                         (vector-ref (vector-ref locenv 0) 1)))))
              (+ start-closed
                 (* locenv-entry-size
                    (- (clo-index gvm-loc) 1))))))))

(define (locenv-val-eqv? locenv val1 val2)
  (type-eqv? val1 val2))

(define (locenv-eqv? locenv1 locenv2)
  (if (and (= (vector-length locenv1) (vector-length locenv2))
           (equal? (vector-ref locenv1 0) (vector-ref locenv2 0))) ;; compare register/stack size
      (let loop ((i 1))
        (if (< i (vector-length locenv1))
            (and (= (locenv-ec locenv1 i) (locenv-ec locenv2 i))
                 (type-eqv? (vector-ref locenv1 (+ i 1)) (vector-ref locenv2 (+ i 1)))
                 (loop (+ i 2)))
            #t))))

(define (make-locenv nb-regs nb-slots nb-closed init-type)
  (let* ((locenv
          (make-locenv-from-lengths (vector nb-regs nb-slots nb-closed)))
         (len
          (+ locenv-start-regs
             (* locenv-entry-size (+ nb-regs nb-slots nb-closed)))))
    (let loop ((i locenv-start-regs))
      (if (< i len)
          (let ((type (or init-type (make-type-top-with-new-length-bound))))
            (vector-set! locenv i i)
            (vector-set! locenv (+ i 1) type)
            (loop (+ i locenv-entry-size)))
          locenv))))

(define (make-locenv-from-lengths lengths)
  (let* ((nb-regs (vector-ref lengths 0))
         (nb-slots (vector-ref lengths 1))
         (nb-closed (vector-ref lengths 2))
         (len (+ locenv-start-regs
                 (* locenv-entry-size (+ nb-regs nb-slots nb-closed))))
         (locenv (make-vector len 0)))
    (vector-set! locenv 0 lengths)
    locenv))

(define (locenv-keep-topmost-slots locenv topmost-slots init-type)
  (let* ((lengths (vector-ref locenv 0))
         (nb-regs (vector-ref lengths 0))
         (nb-slots (vector-ref lengths 1))
         (nb-closed (vector-ref lengths 2))
         (slot-shift (- topmost-slots nb-slots)))
    (locenv-resize-from-lengths locenv
                                (vector nb-regs topmost-slots nb-closed)
                                slot-shift
                                init-type)))

(define (locenv-resize locenv nb-regs nb-slots nb-closed slot-shift init-type)
  (let ((lengths (vector-ref locenv 0)))
    (if (and (= nb-regs (vector-ref lengths 0))
             (= nb-slots (vector-ref lengths 1))
             (= nb-closed (vector-ref lengths 2))
             (= slot-shift 0))
        locenv ;; no change
        (locenv-resize-from-lengths locenv
                                    (vector nb-regs nb-slots nb-closed)
                                    slot-shift
                                    init-type))))

(define (locenv-resize-from-lengths locenv new-lengths slot-shift init-type)
  (let* ((new-locenv
          (make-locenv-from-lengths new-lengths))
         (lengths
          (vector-ref locenv 0))
         (nb-regs
          (vector-ref lengths 0))
         (nb-slots
          (vector-ref lengths 1))
         (nb-closed
          (vector-ref lengths 2))
         (start-slots
          (+ locenv-start-regs (* locenv-entry-size nb-regs)))
         (start-closed
          (+ start-slots (* locenv-entry-size nb-slots)))
         (new-nb-regs
          (vector-ref new-lengths 0))
         (new-nb-slots
          (vector-ref new-lengths 1))
         (new-nb-closed
          (vector-ref new-lengths 2))
         (new-start-slots
          (+ locenv-start-regs (* locenv-entry-size new-nb-regs)))
         (new-start-closed
          (+ new-start-slots (* locenv-entry-size new-nb-slots)))
         (len
          (+ locenv-start-regs
             (* locenv-entry-size (+ nb-regs nb-slots nb-closed)))))

    (define (index->new i) ;; map index from locenv to new-locenv
      (cond ((< i start-slots)
             (and (< i new-start-slots) i))
            ((< i start-closed)
             (let ((i* (+ (- i start-slots) (* locenv-entry-size slot-shift))))
               (and (>= i* 0)
                    (< i* (* locenv-entry-size new-nb-slots))
                    (+ i* new-start-slots))))
            (else
             (let ((i* (- i start-closed)))
               (and (< i* (* locenv-entry-size new-nb-closed))
                    (+ i* new-start-closed))))))

    (let loop1 ((i locenv-start-regs))
      (if (< i len)
          (let ((j (index->new i)))
            (if (not j) ;; location removed by resize?
                (loop1 (+ i locenv-entry-size))
                (let ((ec (vector-ref locenv i)))
                  (if (= ec i) ;; alone in equivalence class
                      (begin
                        (vector-set!
                         new-locenv
                         j
                         j)
                        (vector-set!
                         new-locenv
                         (+ j 1)
                         (vector-ref locenv (+ i 1)))
                        (loop1 (+ i locenv-entry-size)))
                      (let ((x (vector-ref new-locenv j)))
                        (if (not (eqv? x 0)) ;; not head of equivalence class
                            ;; new-locenv already ok for this i
                            (loop1 (+ i locenv-entry-size))
                            (let loop2 ((prev i)
                                        (curr ec)
                                        (new-prev j))
                              (if (= curr i) ;; finished iterating over class?
                                  (begin
                                    (vector-set!
                                     new-locenv
                                     new-prev
                                     j)
                                    (vector-set!
                                     new-locenv
                                     (+ new-prev 1)
                                     (vector-ref locenv (+ prev 1)))
                                    (loop1 (+ i locenv-entry-size)))
                                  (let ((new-curr (index->new curr)))
                                    (if (not new-curr) ;; removed by resize?
                                        (loop2 prev
                                               (vector-ref locenv curr)
                                               new-prev)
                                        (begin
                                          (vector-set!
                                           new-locenv
                                           new-prev
                                           new-curr)
                                          (vector-set!
                                           new-locenv
                                           (+ new-prev 1)
                                           (vector-ref locenv (+ prev 1)))
                                          (loop2 curr
                                                 (vector-ref locenv curr)
                                                 new-curr))))))))))))
          (let loop3 ((j locenv-start-regs))
            (if (< j (vector-length new-locenv))
                (begin
                  (if (eqv? (vector-ref new-locenv j) 0)
                      (let ((type (or init-type
                                      (make-type-top-with-new-length-bound))))
                        (vector-set!
                         new-locenv
                         j
                         j)
                        (vector-set!
                         new-locenv
                         (+ j 1)
                         type)))
                  (loop3 (+ j locenv-entry-size)))
                new-locenv))))))

(define (locenv-merge locenv other-locenv slot-shift union)
  (let* ((lengths
          (vector-ref locenv 0))
         (nb-regs
          (vector-ref lengths 0))
         (nb-slots
          (vector-ref lengths 1))
         (nb-closed
          (vector-ref lengths 2))
         (new-locenv
          (make-locenv-from-lengths lengths))
         (start-slots
          (+ locenv-start-regs (* locenv-entry-size nb-regs)))
         (start-closed
          (+ start-slots (* locenv-entry-size nb-slots)))
         (other-lengths
          (vector-ref other-locenv 0))
         (other-nb-regs
          (vector-ref other-lengths 0))
         (other-nb-slots
          (vector-ref other-lengths 1))
         (other-nb-closed
          (vector-ref other-lengths 2))
         (other-start-slots
          (+ locenv-start-regs (* locenv-entry-size other-nb-regs)))
         (other-start-closed
          (+ other-start-slots (* locenv-entry-size other-nb-slots)))
         (len
          (+ locenv-start-regs
             (* locenv-entry-size (+ nb-regs nb-slots nb-closed)))))

    (define (index->other i) ;; map index from locenv to other-locenv
      (cond ((< i start-slots)
             (and (< i other-start-slots) i))
            ((< i start-closed)
             (let ((i* (+ (- i start-slots) (* locenv-entry-size slot-shift))))
               (and (>= i* 0)
                    (< i* (* locenv-entry-size other-nb-slots))
                    (+ i* other-start-slots))))
            (else
             (let ((i* (- i start-closed)))
               (and (< i* (* locenv-entry-size other-nb-closed))
                    (+ i* other-start-closed))))))

    (let loop ((i locenv-start-regs))
      (if (< i len)
          (let* ((j (index->other i))
                 (type (vector-ref locenv (+ i 1))))
            (vector-set! new-locenv i i) ;; TODO: merge ec
            (vector-set!
             new-locenv
             (+ i 1)
             (if (not j)
                 type
                 (union type (vector-ref other-locenv (+ j 1)))))
            (loop (+ i locenv-entry-size)))
          new-locenv))))

(define (locenv-ec locenv loc)

  ;; This procedure returns the identifier of the equivalence class
  ;; of loc (which is the loc in the same equivalence class with
  ;; the smallest index).

  (let ((ec (vector-ref locenv loc)))
    (if (= ec loc) ;; in its own equivalence class?
        ec
        (let loop ((curr ec) (ec loc))
          (let ((min-ec (min curr ec)))
            (if (= curr loc)
                min-ec
                (loop (vector-ref locenv curr) min-ec)))))))

(define (locenv-ec-detach locenv loc)

  ;; This procedure removes the location loc from its current
  ;; equivalence class.

  (let ((new-locenv (vector-copy locenv)))
    (locenv-ec-detach! new-locenv loc)))

(define (locenv-ec-detach! locenv loc)

  ;; This procedure removes the location loc from its current
  ;; equivalence class.

  (let ((ec (vector-ref locenv loc)))
    (if (= ec loc) ;; already in its own equivalence class?
        locenv
        (begin
          (vector-set! locenv loc loc)
          (let loop ((prev loc) (curr ec))
            (if (= curr loc)
                (begin
                  (vector-set! locenv prev ec)
                  locenv)
                (loop curr (vector-ref locenv curr))))))))

(define (locenv-add! locenv loc-dst loc-src)

  ;; This procedure adds the location loc-dst to the equivalence
  ;; class of the location loc-src.

  (vector-set! locenv loc-dst (vector-ref locenv loc-src))
  (vector-set! locenv (+ loc-dst 1) (vector-ref locenv (+ loc-src 1)))
  (vector-set! locenv loc-src loc-dst)
  locenv)

(define (locenv-copy locenv loc-dst loc-src)

  ;; This procedure adds the location loc-dst to the equivalence
  ;; class of the loc-src location (after removing the loc-dst
  ;; location from its current equivalence class).

  ;; As an optimization, check if the src and dst locations are in the
  ;; same equivalence class and the only ones in that class (this also
  ;; covers the case src = dst).

  (if (and (= (vector-ref locenv loc-src) loc-dst)
           (= (vector-ref locenv loc-dst) loc-src))

      locenv ;; nothing needs to change

      (let ((new-locenv (vector-copy locenv)))
        (locenv-ec-detach! new-locenv loc-dst)
        (locenv-add! new-locenv loc-dst loc-src))))

(define (locenv-set locenv loc val)

  ;; This procedure stores val in the location loc after removing it
  ;; from its current equivalence class.

  ;; As an optimization, check if the location loc is alone in its
  ;; equivalence class and it currently contains val.

  (if (and (= (vector-ref locenv loc) loc)
           (locenv-val-eqv? locenv (vector-ref locenv (+ loc 1)) val))

      locenv ;; nothing needs to change

      (let ((new-locenv (vector-copy locenv)))
        (locenv-ec-detach! new-locenv loc)
        (vector-set! new-locenv (+ loc 1) val)
        new-locenv)))

(define (locenv-set! locenv loc val)

  ;; This procedure stores val in the location loc after removing it
  ;; from its current equivalence class. The locenv is mutated.

  (locenv-ec-detach! locenv loc)
  (vector-set! locenv (+ loc 1) val))

(define (locenv-update locenv opnds vals)

  ;; This procedure stores the values in vals in the corresponding
  ;; locations in opnds and the locations in its equivalence class.

  ;; As an optimization, only create a new locenv if there is a change.

  (let loop1 ((opnds opnds)
              (vals vals)
              (new-locenv #f))
    (if (pair? opnds)
        (let ((opnd (car opnds)))
          (if (locenv-loc? opnd)
              (let* ((le (or new-locenv locenv))
                     (loc (gvm-loc->locenv-index le opnd))
                     (val (vector-ref le (+ loc 1)))
                     (new-val (car vals)))
                (if (locenv-val-eqv? le val new-val)
                    (loop1 (cdr opnds)
                           (cdr vals)
                           new-locenv)
                    (let ((new-locenv
                           (or new-locenv
                               (vector-copy locenv))))
                      (let loop2 ((i (vector-ref new-locenv loc)))
                        (vector-set! new-locenv (+ i 1) new-val)
                        (if (= i loc)
                            (loop1 (cdr opnds)
                                   (cdr vals)
                                   new-locenv)
                            (loop2 (vector-ref new-locenv i)))))))
              (loop1 (cdr opnds)
                     (cdr vals)
                     new-locenv)))
        (or new-locenv locenv))))

(define (locenv-ref locenv loc)

  ;; This procedure retrieves the value associated with the location loc.

  (vector-ref locenv (+ loc 1)))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Basic block writing:
;; -------------------

(define (write-bb bb options port)
  (write-gvm-instr (bb-label-instr bb) options port bb)
  (newline port)

  (for-each (lambda (gvm-instr)
              (if (useful-gvm-instr? gvm-instr)
                  (begin
                    (write-gvm-instr gvm-instr options port)
                    (newline port))))
            (bb-non-branch-instrs bb))

  (if (not (null? (bb-branch-instr bb)))
      (write-gvm-instr (bb-branch-instr bb) options port)))

(define (useful-gvm-instr? gvm-instr)
  (or show-frame-padding?
      (not (and (eq? (gvm-instr-kind gvm-instr) 'copy)
                (not (copy-opnd gvm-instr))))))

(define (write-bbs bbs options port)
  (bbs-for-each-bb
    (lambda (bb)
      (if (= (bb-lbl-num bb) (bbs-entry-lbl-num bbs))
        (begin (display "**** Entry block:" port) (newline port)))
      (write-bb bb options port)
      (newline port))
    bbs))

(define show-slots-needed? #f)
(set! show-slots-needed? #f)

(define show-frame-padding? #f)
(set! show-frame-padding? #f)

(define show-frame? #t)
(set! show-frame? #t)

(define show-source-location? #f)
(set! show-source-location? #f)

(define (virtual.dump-gvm procs port)

  (define (dump-proc p)

    (define (dump-code code)
      (let ((gvm-instr (code-gvm-instr code)))
        (if (useful-gvm-instr? gvm-instr)
            (begin

              (if show-slots-needed?
                  (begin
                    (display "sn=" port)
                    (display (code-slots-needed code) port)
                    (display " | " port)))

              (write-gvm-instr gvm-instr '() port (code-bb code))
              (newline port)))))

    (if (proc-obj-primitive? p)
        (display "**** #<primitive " port)
        (display "**** #<procedure " port))
    (write (string->canonical-symbol (proc-obj-name p)) port)
    (display "> =" port)
    (newline port)

    (let ((x (proc-obj-code p)))
      (if (bbs? x)

          (let loop ((l (bbs->code-list x))
                     (prev-filename "")
                     (prev-line 0))
            (if (pair? l)
                (let* ((code (car l))
                       (instr (code-gvm-instr code))
                       (node (instr-comment-get instr 'node))
                       (src (node-source node))
                       (loc (and src (source-locat src)))
                       (filename
                        (if (and loc (string? (vector-ref loc 0))) ;;;;;;;;;;;;;
                            (vector-ref loc 0)
                            prev-filename))
                       (line
                        (if (and loc (string? (vector-ref loc 0)))
                            (+ (**filepos-line (vector-ref loc 1)) 1)
                            prev-line)))
                  (if (and show-source-location?
                           (or (not (string=? filename prev-filename))
                               (not (= line prev-line))))
                      (begin
                        (display "#line " port)
                        (display line port)
                        (if (not (string=? filename prev-filename))
                            (begin
                              (display " " port)
                              (write filename port)))
                        (newline port)))

                  (dump-code code)
                  (loop (cdr l) filename line))
                (newline port)))

          (begin
            (display "C procedure of arity " port)
            (display (c-proc-arity x) port)
            (display " and body:" port)
            (newline port)
            (display (c-proc-body x) port)
            (newline port)))))

  (for-each dump-proc (reachable-procs procs)))

(define (virtual.dump-cfg gvm-interpret-ctx port)

  ;; For generating visual representation of control flow graph with "dot".

  (define procs (vector-ref gvm-interpret-ctx 0))
  (define max-branch-count (vector-ref gvm-interpret-ctx 1))

  (define dd (make-dot-digraph (proc-obj-name (car procs))))

  (define node-entry-bgcolor dot-digraph-black)
  (define node-type-bgcolor  dot-digraph-gray60)
  (define node-info-default-bgcolor  dot-digraph-gray70)
  (define node-bgcolor       dot-digraph-gray80)

  (define (get-unique-node-info-bgcolor orig-lbl force-default-color)
    ;; loop through pre-selected distinct colors
    ;; https://stackoverflow.com/a/20298027/5079316
    (define colors
      #("#ff0056" "#00ff00" "#0000ff" "#ff0000" "#01fffe" "#ffa6fe"
        "#ffdb66" "#006401" "#010067" "#95003a" "#007db5" "#ff00f6"
        "#ffeee8" "#774d00" "#90fb92" "#0076ff" "#d5ff00" "#ff937e"
        "#6a826c" "#ff029d" "#fe8900" "#7a4782" "#7e2dd2" "#85a900"
        "#e85ebe" "#a42400" "#00ae7e" "#683d3b" "#bdc6ff" "#263400"
        "#bdd393" "#00b917" "#9e008e" "#001544" "#c28c9f" "#ff74a3"
        "#01d0ff" "#004754" "#e56ffe" "#788231" "#0e4ca1" "#91d0cb"
        "#be9970" "#968ae8" "#bb8800" "#43002c" "#deff74" "#00ffc6"
        "#ffe502" "#620e00" "#008f9c" "#98ff52" "#7544b1" "#b500ff"
        "#00ff78" "#ff6e41" "#005f39" "#6b6882" "#5fad4e" "#a75740"
        "#a5ffd2" "#ffb167" "#009bff"))

    (if (and orig-lbl (not force-default-color))
      (vector-ref colors (modulo orig-lbl (vector-length colors)))
      node-info-default-bgcolor))

  (let ((bbs-tbl (make-table 'test: eq?))
        (proc-tbl (make-table)))

    (define (proc-repr proc)
      (format-gvm-opnd (make-obj proc) '()))

    (define (bb-id bb-index proc-index)
      (string-append "proc"
                     (number->string proc-index)
                     "_"
                     (number->string bb-index)))

    (define (dump-proc proc proc-index)
      (let ((x (proc-obj-code proc)))
        (if (bbs? x)
            (dump-proc-bbs proc proc-index x))))

    (define (dump-proc-bbs proc proc-index bbs)

      (define (make-versions-table)
        (define table (make-table))

        (define (add-to-table bb)
          (let* ((orig-lbl (instr-comment-get (bb-label-instr bb) 'orig-lbl))
                 (versions (table-ref table orig-lbl '())))
            (table-set! table orig-lbl (cons bb versions))))
        (bbs-for-each-bb add-to-table bbs)
        table)

      (define versions-table (make-versions-table))

      (define (bb-has-cousin-versions? bb)
        (let* ((orig-lbl (instr-comment-get (bb-label-instr bb) 'orig-lbl)))
          (> (length (table-ref versions-table orig-lbl)) 1)))

      (define (dump-bb bb)
        (let ((id (bb-id (bb-lbl-num bb) proc-index))
              (port-count 0)
              (rev-rows '())
              (branch-counters (get-branch-counters (bb-branch-instr bb))))

          (define (add-row row)
            (set! rev-rows (cons row rev-rows)))

          (define (gen-port)
            (set! port-count (+ port-count 1))
            (number->string port-count))

          (define nb-ports 0) ;; need to count ports to work around dot bug

          (define (decorate-instr code-and-rest last-instr?)
            (let ((code (car code-and-rest))
                  (rest (cdr code-and-rest))
                  (line-id (gen-port)))

              (define (target-id ref)
                (cond ((pair? ref)
                       ;; a label outside of this bbs
                       ;; lbl=(car ref), bbs=(cdr ref)
                       (let ((info (table-ref bbs-tbl (cdr ref))))
                         (bb-id (car ref) (cdr info))))
                      (else
                       ;; a label in this bbs
                       (bb-id ref proc-index))))

              (define (reference? x)
                (let ((info (table-ref proc-tbl x #f)))
                  (if info ;; a label outside of this bbs?
                      (let* ((proc (car info))
                             (proc-index (cdr info))
                             (bbs (proc-obj-code proc)))
                        (cons (bbs-entry-lbl-num bbs) bbs))
                      (and (>= (string-length x) 2) ;; a label in this bbs?
                           (char=? (string-ref x 0) #\#)
                           (string->number (substring x 1 (string-length x)))))))

              (define (add-edge from side targ-id width color label)
                (dot-digraph-add-edge!
                 dd
                 (dot-digraph-gen-edge
                  (string-append id ":" from side)
                  targ-id
                  width
                  color
                  label)))

              (define (add-branch-edge from targ-bbs targ-lbl)
                (let* ((t (table-ref branch-counters targ-bbs #f))
                       (count (if t (table-ref t targ-lbl 0) 0)))
                  (add-branch-edge-with-count from targ-bbs targ-lbl count)))

              (define (add-branch-edge-with-count from targ-bbs targ-lbl count)

                (define (edge width color label)
                  (add-edge
                   from
                   ":s"
                   (let ((info (table-ref bbs-tbl targ-bbs)))
                     (bb-id targ-lbl (cdr info)))
                   width
                   color
                   label))

                (if (> count 0)
                    (let ((cbrt
                           (inexact->exact
                            (round (expt max-branch-count 0.333))))
                          (label
                           (number->string count)))
                      (cond ((<= count cbrt)
                             (edge 3 "#9DC262" label)) ;; greenish
                            ((<= count (* cbrt cbrt))
                             (edge 6 "#F8A804" label)) ;; yellowish
                            (else
                             (edge 9 "#E40303" label)))) ;; redish
                    (edge 1 #f #f))) ;; black

              (define (add-branch-edges from ref)
                (cond ((not ref)
                       ;; general GVM operand (register, stack, etc)
                       ;; add all branches that were observed
                       (for-each
                        (lambda (targ-bbs-and-table)
                          (let ((targ-bbs (car targ-bbs-and-table)))
                            (for-each
                             (lambda (targ-lbl-and-count)
                               (let ((targ-lbl (car targ-lbl-and-count))
                                     (count (cdr targ-lbl-and-count)))
                                 (add-branch-edge-with-count from targ-bbs targ-lbl count)))
                             (table->list (cdr targ-bbs-and-table)))))
                        (table->list branch-counters)))
                      ((pair? ref)
                       ;; a label outside of this bbs...
                       ;; lbl=(car ref), bbs=(cdr ref)
                       (add-branch-edge from (cdr ref) (car ref)))
                      (else
                       ;; a label inside this bbs
                       (add-branch-edge from bbs ref))))

              (define (add-ref-edge from side ref)
                (add-edge from side (target-id ref) 0 #f #f))

              (dot-digraph-gen-row
               (dot-digraph-gen-col
                #f
                "left"
                (dot-digraph-gen-table
                 line-id
                 #f
                 (dot-digraph-gen-row
                  (let loop1 ((before
                               (list (dot-digraph-gen-html-escape
                                      (car code))))
                              (code
                               (cdr code)))
                    (if (pair? code)
                        (let* ((x
                                (car code))
                               (branch-destination?
                                (and last-instr?
                                     (pair? before)
                                     (equal? (car before) "")))
                               (ref
                                (reference? x)));;either (bbs . lbl) / lbl / #f
                          (if (or branch-destination? ref)
                              (if last-instr? ;; should arrow exit south?
                                  (let ((ref-id (gen-port)))
                                    (set! nb-ports (+ nb-ports 1))
                                    (if branch-destination?
                                        (add-branch-edges ref-id ref)
                                        (add-ref-edge ref-id ":s" ref))
                                    `(,@(dot-digraph-gen-col
                                         #f
                                         "left"
                                         (reverse before))
                                      ,@(dot-digraph-gen-col
                                         ref-id
                                         "left"
                                         `(,(dot-digraph-gen-html-escape x)))
                                      ,@(loop1 '()
                                               (cdr code))))
                                  (begin
                                    (add-ref-edge line-id ":w" ref)
                                    (loop1 (cons
                                            (dot-digraph-gen-html-escape x)
                                            before)
                                           (cdr code))))
                              (loop1 (cons
                                      (dot-digraph-gen-html-escape x)
                                      before)
                                     (cdr code))))
                        `(,@(dot-digraph-gen-col
                             #f
                             "left"
                             (reverse before))
                          ,@(if (pair? rest)
                                (let loop2 ((n (* 2 (if last-instr? 0 nb-ports))))
                                  (if (> n 0)
                                      `(,@(dot-digraph-gen-col
                                           #f
                                           "left"
                                           `())
                                        ,@(loop2 (- n 1)))
                                      (dot-digraph-gen-col
                                       #f
                                       "left"
                                       (dot-digraph-gen-text-style
                                        'comment
                                        (map dot-digraph-gen-html-escape
                                             rest)))))
                                `()))))))))))

          (define (format-instr gvm-instr)
            (cons gvm-instr
                  (format-gvm-instr-code gvm-instr '())))

          (define (format-length lst)
            (let loop ((lst lst) (len 0))
              (if (pair? lst)
                  (loop (cdr lst)
                        (+ len
                           (let ((x (car lst)))
                             (if (list? x)
                                 (format-length x)
                                 (string-length x)))))
                  len)))

          (define (max-format-length lst)
            (let loop ((lst lst) (len 0))
              (if (pair? lst)
                  (loop (cdr lst) (max len (format-length (car lst))))
                  len)))

          (let* ((gvm-instrs
                  (cons (bb-label-instr bb)
                        (append (keep useful-gvm-instr?
                                      (bb-non-branch-instrs bb))
                                (list
                                 (bb-branch-instr bb)))))
                 (code-rows
                  (map (lambda (gvm-instr)
                         (format-gvm-instr-code gvm-instr '()))
                       gvm-instrs))
                 (rows
                  (if #f
                      (map list code-rows)
                      (let* ((frame-rows
                              (map (lambda (gvm-instr)
                                     (format-gvm-instr-frame gvm-instr '()))
                                   gvm-instrs))
                             (width-code
                              (max-format-length code-rows))
                             (width-frame
                              (max-format-length frame-rows)))
                        (map (lambda (code-row frame-row)
                               (cons `(,@code-row
                                       ,(make-string
                                         (+ 1 (- width-code (format-length code-row)))
                                         #\space))
                                     `(,@frame-row
                                       ,(make-string
                                         (- width-frame (format-length frame-row))
                                         #\space))))
                             code-rows
                             frame-rows))))
                 (bb-info
                  (append
                   (if (= (bbs-entry-lbl-num bbs)
                          (bb-lbl-num bb))
                       (list (cons 'entry (format-gvm-obj proc #f)))
                       '())
                   (or (instr-comment-get (bb-label-instr bb) 'cfg-bb-info)
                       '()))))
            (dot-digraph-add-node!
             dd
             (dot-digraph-gen-node
              id
              (dot-digraph-gen-html-label
               (dot-digraph-gen-table
                #f
                node-bgcolor
                `(,@(apply append
                           (map (lambda (x)
                                  (let* ((style (if (pair? x) (car x) 'plain))
                                         (line (if (pair? x) (cdr x) x))
                                         (bgcolor
                                          (case style
                                            ((entry)
                                             node-entry-bgcolor)
                                            ((type)
                                             node-type-bgcolor)
                                            ((info)
                                              (get-unique-node-info-bgcolor
                                                (instr-comment-get
                                                  (bb-label-instr bb)
                                                  'orig-lbl)
                                                (not (bb-has-cousin-versions? bb))))
                                            (else
                                             #f)))
                                         (esc-line
                                          (list (dot-digraph-gen-html-escape
                                                 line)))
                                         (decorated-line
                                          (case style
                                            ((entry info)
                                             (dot-digraph-gen-text-style
                                              style
                                              esc-line))
                                            (else
                                             esc-line)))
                                         (align
                                          (case style
                                            ((entry)
                                             #f)
                                            (else
                                             "left"))))
                                  (dot-digraph-gen-row
                                   (dot-digraph-gen-col
                                    #f
                                    "left"
                                    (dot-digraph-gen-table
                                     #f
                                     bgcolor
                                     (dot-digraph-gen-row
                                      (dot-digraph-gen-col
                                       #f
                                       align
                                       decorated-line)))))))
                                bb-info))
                  ,@(let loop ((lst (reverse rows))
                               (last-instr? #t)
                               (result '()))
                      (if (pair? lst)
                          (loop (cdr lst)
                                #f
                                `(,@(decorate-instr (car lst) last-instr?)
                                  ,@result))
                          result))))))))))

      (bbs-for-each-bb dump-bb bbs))

    (let ((rprocs
           (reachable-procs procs)))

      (let loop1 ((i 0) (lst rprocs))
        (if (pair? lst)
            (let* ((proc (car lst))
                   (info (cons proc i)))
              (table-set! bbs-tbl (proc-obj-code proc) info)
              (table-set! proc-tbl (proc-repr proc) info)
              (loop1 (+ i 1) (cdr lst)))))

      (let loop2 ((i 0) (lst rprocs))
        (if (pair? lst)
            (let ((proc (car lst)))
              (dump-proc proc i)
              (loop2 (+ i 1) (cdr lst)))))

      (dot-digraph-write dd port))))

(define (virtual.dump-dg name dependency-graph port)

  ;; For generating visual representation of dependency graph with "dot".

  (define dd (make-dot-digraph name))

  (define (gen-label referrer)
    (object->string (gen-label-string referrer)))

  (define (gen-label-string referrer)
    (object->string referrer))

  (define (interesting? sym)
    ;; modify to filter out some symbols
    #t)

  (define (sort-syms t)
   (sort-list (table->list t)
              (lambda (x y)
                (string<? (symbol->string (car x))
                          (symbol->string (car y))))))

  (define not-defined (make-table 'test: eq?))

  (for-each
   (lambda (referrer-dependencies)
     (let ((referrer (car referrer-dependencies))
           (deps (cdr referrer-dependencies)))

       (define (add dependencies jump?)
         (for-each
          (lambda (var)
            (if (and (not (eq? var referrer)) ;; avoid self cycle
                     (interesting? var))
                (begin
                  (if (not (table-ref dependency-graph var #f))
                      (table-set! not-defined var #t))
                  (dot-digraph-add-edge!
                   dd
                   (dot-digraph-gen-edge
                    (gen-label referrer)
                    (gen-label var)
                    (if jump? 1 0) ;; solid or dotted line
                    #f ;; color
                    #f))))) ;; no label
          (sort-list (map var-name (varset->list dependencies))
                     (lambda (x y)
                       (string<? (symbol->string x)
                                 (symbol->string y))))))

       (if (interesting? referrer)
           (begin

             '
             (dot-digraph-add-node!
              dd
              (dot-digraph-gen-node
               (gen-label referrer)
               (list (gen-label referrer))))

             (add (vector-ref deps 0) #t)
             (add (vector-ref deps 1) #f)))))

   (sort-syms dependency-graph))

  (for-each
   (lambda (x)
     (let ((var (car x)))
       (dot-digraph-add-node!
        dd
        (dot-digraph-gen-node
         (gen-label var)
         (dot-digraph-gen-html-label
          (dot-digraph-gen-table
           #f
           dot-digraph-black
           (dot-digraph-gen-row
            (dot-digraph-gen-col
             #f
             #f
             (dot-digraph-gen-text-style
              'invert
              (list
               " "
               (dot-digraph-gen-html-escape (gen-label-string var))
               " "))))))))))
   (sort-syms not-defined))

  (dot-digraph-write dd port))

(define (reachable-procs procs)
  (let ((proc-seen (queue-empty))
        (proc-left (queue-empty)))

    (define (scan-obj obj)
      (if (and (proc-obj? obj)
               (proc-obj-code obj)
               (not (memq obj (queue->list proc-seen))))
        (begin
          (queue-put! proc-seen obj)
          (queue-put! proc-left obj))))

    (define (scan-opnd gvm-opnd)
      (cond ((not gvm-opnd))
            ((obj? gvm-opnd)
             (scan-obj (obj-val gvm-opnd)))
            ((clo? gvm-opnd)
             (scan-opnd (clo-base gvm-opnd)))))

    (define (scan-proc proc)

      (define (scan-bb bb)

        (define (scan-gvm-instr gvm-instr)
          (case (gvm-instr-kind gvm-instr)

            ((apply)
             (for-each scan-opnd (apply-opnds gvm-instr))
             (if (apply-loc gvm-instr)
                 (scan-opnd (apply-loc gvm-instr))))

            ((copy)
             (scan-opnd (copy-opnd gvm-instr))
             (scan-opnd (copy-loc gvm-instr)))

            ((close)
             (for-each (lambda (parms)
                         (scan-opnd (closure-parms-loc parms))
                         (for-each scan-opnd (closure-parms-opnds parms)))
                       (close-parms gvm-instr)))

            ((ifjump)
             (for-each scan-opnd (ifjump-opnds gvm-instr)))

            ((switch)
             (scan-opnd (switch-opnd gvm-instr))
             (for-each (lambda (c) (scan-obj (switch-case-obj c)))
                       (switch-cases gvm-instr)))

            ((jump)
             (scan-opnd (jump-opnd gvm-instr)))))

        (scan-gvm-instr (bb-label-instr bb))
        (for-each (lambda (gvm-instr) (scan-gvm-instr gvm-instr))
                  (bb-non-branch-instrs bb))
        (scan-gvm-instr (bb-branch-instr bb)))

      (let ((x (proc-obj-code proc)))
        (if (bbs? x)
            (bbs-for-each-bb (lambda (bb) (scan-bb bb)) x))))

    (for-each (lambda (proc) (scan-opnd (make-obj proc))) procs)

    (let loop ()
      (if (not (queue-empty? proc-left))
        (begin
          (scan-proc (queue-get! proc-left))
          (loop))))

    (queue->list proc-seen)))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; 'dot' graph generation:
;; ----------------------

(define (make-dot-digraph name)
  (vector '() '() name))

(define (dot-digraph-nodes dd)            (vector-ref dd 0))
(define (dot-digraph-nodes-set! dd nodes) (vector-set! dd 0 nodes))

(define (dot-digraph-edges dd)            (vector-ref dd 1))
(define (dot-digraph-edges-set! dd edges) (vector-set! dd 1 edges))

(define (dot-digraph-name dd)           (vector-ref dd 2))
(define (dot-digraph-name-set! dd name) (vector-set! dd 2 name))

(define (dot-digraph-add-node! dd node)
  (dot-digraph-nodes-set!
   dd
   `(,@node
     ,@(dot-digraph-nodes dd))))

(define (dot-digraph-add-edge! dd edge)
  (dot-digraph-edges-set!
   dd
   `(,@edge
     ,@(dot-digraph-edges dd))))

(define (dot-digraph-gen-digraph dd)
  `("digraph \"" ,(dot-digraph-name dd) "\" {\n"
    "  graph [splines = true overlap = false rankdir = \"TD\"];\n"
    "  node [fontname = \"" ,dot-digraph-font-default "\" shape = \"none\"];\n"
    ,@(dot-digraph-nodes dd)
    ,@(dot-digraph-edges dd)
    "}\n"))

(define (dot-digraph-gen-edge from to width color label)
  `("  " ,from " -> " ,to
    ,@(if (and (= width 1) (not color) (not label))
          '()
          `(" ["
            ,@(if label `("headlabel=\"" ,label "\" labelfontsize=" ,(number->string (* 4 (max 3 width)))) '())
            ,@(if (= width 1)
                  '()
                  (if (< width 1)
                      `(" style=dotted")
                      `(" style=\"setlinewidth(" ,(number->string width) ")\"")))
            ,@(if (not color)
                  '()
                  `(" color=\"" ,color "\""))
            "]"))
    ";\n"))

(define (dot-digraph-gen-node id label)
  `("  " ,id " [label = "
    ,@label
    "];\n"))

(define (dot-digraph-gen-table id bgcolor content)
  `("<table border=\"0\" cellborder=\"0\" cellspacing=\"0\" cellpadding=\"0\""
    ,@(if bgcolor
          `(" bgcolor=\"" ,bgcolor "\"")
          '())
    ,@(if id
          `(" port=\"" ,id "\"")
          '())
    ">"
    ,@content
    "</table>"))

(define (dot-digraph-gen-row content)
  `("<tr>"
    ,@content
    "</tr>"))

(define (dot-digraph-gen-col id align content)
  `("<td"
    ,@(if align
          `(" align=\"" ,align "\"")
          '())
    ,@(if id
          `(" port=\"" ,id "\"")
          '())
    ">"
    ,@content
    "</td>"))

(define dot-digraph-font-default "Courier")
;;(define dot-digraph-font-default "Courier New")
;;(define dot-digraph-font-default "Andale Mono")
;;(define dot-digraph-font-default "Monaco")

(define (dot-digraph-gen-text-style style content)
  (let* ((x (assq style
                  '((plain   #f #f   #f        #f #f)
                    (invert  #f #f   "#ffffff" #f #f)
                    (comment #f "9"  "#000080" #t #f)
                    (info    #f "7"  #f        #t #f)
                    (entry   #f "18" "#ffffff" #t #f))))
         (face       (and x (list-ref x 1)))
         (point-size (and x (list-ref x 2)))
         (color      (and x (list-ref x 3)))
         (bold?      (and x (list-ref x 4)))
         (italic?    (and x (list-ref x 5))))
    (dot-digraph-gen-font face point-size color bold? italic? content)))

(define (dot-digraph-gen-font face point-size color bold? italic? content)
  `(,@(if (or face point-size color)
          `("<font"
            ,@(if face
                  `(" face=\"" ,face "\"")
                  '())
            ,@(if point-size
                  `(" point-size=\"" ,point-size "\"")
                  '())
            ,@(if color
                  `(" color=\"" ,color "\"")
                  '())
            ">")
          '(""))
    ,@(if bold? '("<b>") '(""))
    ,@(if italic? '("<i>") '(""))
    ,@content
    ,@(if italic? '("</i>") '(""))
    ,@(if bold? '("</b>") '(""))
    ,(if (or face point-size color)
         "</font>"
         "")))

(define (dot-digraph-gen-html-label content)
  `("<"
    ,@content
    ">"))

(define (dot-digraph-gen-html-escape str)
  (string-concatenate
   (map (lambda (c)
          (cond ((char=? c #\<) "&lt;")
                ((char=? c #\>) "&gt;")
                ((char=? c #\&) "&amp;")
                (else           (string c))))
        (string->list (format-concatenate str)))))

(define (dot-digraph-write dd port)
  (for-each
   (lambda (str)
     (display str port))
   (dot-digraph-gen-digraph dd)))

(define dot-digraph-gray60 "gray60")
(define dot-digraph-gray70 "gray70")
(define dot-digraph-gray80 "gray80")
(define dot-digraph-black  "black")

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Virtual instruction writing:
;; ---------------------------

(define (write-gvm-instr gvm-instr options port . bb)

  (define (spaces n)
    (if (> n 0)
      (if (> n 7)
        (begin (display "        " port) (spaces (- n 8)))
        (begin (display " " port) (spaces (- n 1))))))

  (let ((str
         (format-concatenate
          (apply format-gvm-instr-code (cons gvm-instr (cons options bb))))))
    (display str port)
    (spaces (- 43 (string-length str)))
    (display " " port)
    (if show-frame?
        (write-gvm-instr-frame gvm-instr options port)))


  (let ((y (instr-comment-get gvm-instr 'text)))
    (if y
      (begin
        (display " ; " port)
        (display y port)))))

(define (write-gvm-instr-frame gvm-instr options port)
  (display (format-concatenate (format-gvm-instr-frame gvm-instr options))
           port))

(define (format-gvm-instr-frame gvm-instr options)
  (let ((frame (gvm-instr-frame gvm-instr))
        (types (gvm-instr-types gvm-instr)))
    (format-frame frame types 'combined options)))

(define (write-frame frame types port)
  (display (format-concatenate (format-frame frame types 'combined '()))
           port))

(define (format-frame frame types style options)

  (define (format-type-gvm-loc gvm-loc)
    (and types
         (let ((type
                (locenv-ref types (gvm-loc->locenv-index types gvm-loc))))
           (if (and (not (eq? style 'types)) (type-top? type))
               #f ;; don't show universal type
               (format-type type)))))

  (define brief? (memq 'brief options))

  (define (uninteresting? var)
    (eq? var ret-var))

  (define (format-var var prefix suffix)

    (define (format-var-name var)
      (symbol->string (var-name var)))

    (cond ((eq? var closure-env-var)
           (let ((closed (frame-closed frame)))
             (let loop ((i (length closed))
                        (lst (reverse closed))
                        (sep `())
                        (result `(,(if (eq? style 'types) "" ")"))))
               (if (pair? lst)
                   (loop (- i 1)
                         (cdr lst)
                         `(" ")
                         (let ((var (car lst)))
                           (if (eq? style 'header)
                               `(,(format-var-name var)
                                 ,@sep
                                 ,@result)
                               (let ((type
                                      (format-type-gvm-loc (make-clo #f i))))
                                 (if (eq? style 'types)
                                     `(,(or type '())
                                       ,@sep
                                       ,@result)
                                     `(,(format-var-name var)
                                       ,@(or type '())
                                       ,@type
                                       ,@sep
                                       ,@result))))))
                   (if (eq? style 'types)
                       `(,suffix
                         ""
                         ,@result)
                       `(,prefix
                         "("
                         ,@result))))))
          ((eq? style 'types)
           `(,suffix))
          ((eq? var ret-var)
           `((,@prefix ,(if brief? "#" "#ret") ,@suffix)))
          ((var-temp? var)
           `((,@prefix "#" ,@suffix)))
          (else
           `((,@prefix ,(format-var-name var) ,@suffix)))))

  (let ((regs (frame-regs frame)))
    (let loop1 ((i (- (length regs) 1))
                (lst (reverse regs))
                (sep `())
                (result `()))
      (if (pair? lst)
          (let ((var (car lst)))
            (if (and (frame-live? var frame) ;; only include live registers
                     (not (and brief? (uninteresting? var))))
                (loop1 (- i 1)
                       (cdr lst)
                       `(" ")
                       (let ((reg (make-reg i)))
                         (if (eq? style 'header)
                             `(,@(format-var
                                  var
                                  `(,(format-gvm-opnd reg options)
                                    "=")
                                  `())
                               ,@sep
                               ,@result)
                             (let ((type
                                    (format-type-gvm-loc reg)))
                               `(,@(if (eq? style 'types)
                                       (format-var
                                        var
                                        `()
                                        (or type `()))
                                       (format-var
                                        var
                                        `(,(format-gvm-opnd reg options)
                                          "=")
                                        (if type `("|" ,@type) `())))
                                 ,@sep
                                 ,@result)))))
                (loop1 (- i 1)
                       (cdr lst)
                       sep
                       result)))
          (let ((slots (frame-slots frame)))
            (let loop2 ((i (length slots))
                        (lst slots)
                        (sep `())
                        (result `(,(if (eq? style 'types) "" "]")
                                  ,@sep
                                  ,@result)))
              (if (pair? lst)
                  (let* ((var
                          (car lst))
                         (live?
                          (frame-live? var frame)))
                    (if (eq? style 'header)
                        (if live?
                            (loop2 (- i 1)
                                   (cdr lst)
                                   `(" ")
                                   `(,@(format-var var `() `())
                                     ,@sep
                                     ,@result))
                            (if (and (null? sep) brief?)
                                (loop2 (- i 1)
                                       (cdr lst)
                                       sep
                                       result)
                                (loop2 (- i 1)
                                       (cdr lst)
                                       `(" ")
                                       `("."
                                         ,@sep
                                         ,@result))))
                        (let* ((stk (make-stk i))
                               (type (and live?
                                          (format-type-gvm-loc stk))))
                          (if live?
                              (loop2 (- i 1)
                                     (cdr lst)
                                     `(" ")
                                     `(,@(format-var
                                          var
                                          `()
                                          (if type
                                              (if (eq? style 'types)
                                                  type
                                                  `("|" ,@type))
                                              `()))
                                       ,@sep
                                       ,@result))
                              (if (and (null? sep) brief?)
                                  (loop2 (- i 1)
                                         (cdr lst)
                                         sep
                                         result)
                                  (loop2 (- i 1)
                                         (cdr lst)
                                         `(" ")
                                         `(,(if (eq? style 'types) "" ".")
                                           ,@sep
                                           ,@result)))))))
                  `(,(if (eq? style 'types) "" "[") ,@result))))))))

(define (make-text-grid)
  (vector 0 0 (make-stretchable-vector #f)))

(define (text-grid-rows text-grid)
  (vector-ref text-grid 0))

(define (text-grid-cols text-grid)
  (vector-ref text-grid 1))

(define (text-grid-row text-grid row)
  (let ((sv (vector-ref text-grid 2)))
    (or (stretchable-vector-ref sv row)
        (let ((sv2 (make-stretchable-vector "")))
          (stretchable-vector-set! sv row sv2)
          sv2))))

(define (text-grid-ref text-grid row col)
  (let ((sv (text-grid-row text-grid row)))
    (stretchable-vector-ref sv col)))

(define (text-grid-set! text-grid row col text)
  (if (>= row (vector-ref text-grid 0))
      (vector-set! text-grid 0 (+ row 1)))
  (if (>= col (vector-ref text-grid 1))
      (vector-set! text-grid 1 (+ col 1)))
  (let ((sv (text-grid-row text-grid row)))
    (stretchable-vector-set! sv col text)))

(define (text-grid-line-set! text-grid row col lst)
  (let loop ((lst lst) (col col))
    (if (pair? lst)
        (begin
          (text-grid-set! text-grid row col (car lst))
          (loop (cdr lst) (+ col 1))))))

(define (format-concatenate text-or-list)

  (define (flatten x rest)
    (cond ((pair? x)
           (if (eq? (car x) 'span)
               (flatten (cddr x) rest)
               (flatten (car x) (flatten (cdr x) rest))))
          ((null? x)
           rest)
          (else
           (cons x rest))))

  (string-concatenate (flatten text-or-list '())))

(define (text-grid-display text-grid port)

  (define (get row col)
    (format-concatenate (text-grid-ref text-grid row col)))

  (define (output text width port)
    (let ((pad (- width (string-length text))))
      (display text port)
      (display (make-string pad #\space) port)))

  (let* ((start (make-stretchable-vector '()))
         (rows (vector-ref text-grid 0))
         (cols (vector-ref text-grid 1)))
    (let loop1 ((col (- cols 1)) (widths '()))
      (if (>= col 0)
          (let loop2 ((row 0) (width 0))
            (if (< row rows)
                (let ((cell (text-grid-ref text-grid row col)))
                  (if (and (pair? cell) (eq? (car cell) 'span))
                      (let* ((span
                              (cadr cell))
                             (text
                              (format-concatenate (cddr cell)))
                             (last-col
                              (+ col (- span 1))))
                        (stretchable-vector-set!
                         start
                         last-col
                         (cons (cons col (string-length text))
                               (stretchable-vector-ref start last-col)))
                        (loop2 (+ row 1)
                               width))
                      (loop2 (+ row 1)
                             (if (char? cell)
                                 width
                                 (max width
                                      (string-length
                                       (format-concatenate cell)))))))
                (loop1 (- col 1)
                       (cons width widths))))
          (let loop3 ((col 0) (pos 0) (widths widths))
            (if (pair? widths)
                (let* ((width (car widths))
                       (end (+ pos width))
                       (spans (stretchable-vector-ref start col)))
                  (stretchable-vector-set! start col pos)
                  (for-each
                   (lambda (col-width)
                     (let ((span-col (car col-width))
                           (span-width (cdr col-width)))
                       (set! end
                         (max end
                              (+ (stretchable-vector-ref start span-col)
                                 span-width)))))
                   spans)
                  (loop3 (+ col 1)
                         end
                         (cdr widths)))
                (stretchable-vector-set! start col pos)))))
    (let loop4 ((row 0))
      (if (< row rows)
          (let loop5 ((col 0))
            (if (< col cols)
                (let ((cell (text-grid-ref text-grid row col)))
                  (if (and (pair? cell) (eq? (car cell) 'span))
                      (let* ((span
                              (cadr cell))
                             (text
                              (format-concatenate (cddr cell)))
                             (width
                              (- (stretchable-vector-ref start (+ col span))
                                 (stretchable-vector-ref start col))))
                        (output text width port)
                        (loop5 (+ col span)))
                      (let* ((span
                              1)
                             (width
                              (- (stretchable-vector-ref start (+ col span))
                                 (stretchable-vector-ref start col)))
                             (text
                              (if (char? cell)
                                  (make-string width cell)
                                  (format-concatenate cell))))
                        (output text width port)
                        (loop5 (+ col span)))))
                (begin
                  (newline port)
                  (loop4 (+ row 1)))))))))

(define (format-gvm-instr-code gvm-instr options . bb)

  (define (format-closure-parms parms)
    `(" "
      ,(format-gvm-opnd (closure-parms-loc parms) options)
      " = ("
      ,(format-gvm-lbl (closure-parms-lbl parms) options)
      ,@(format-spaced-opnd-list (closure-parms-opnds parms))))

  (define (format-spaced-opnd-list lst)
    (let loop ((lst lst)
               (rev-result '()))
      (if (pair? lst)
          (loop (cdr lst)
                `(,(format-gvm-opnd (car lst) options)
                  " "
                  ,@rev-result))
          (reverse `(")" ,@rev-result)))))

  (define (format-opnd-list lst)
    (if (pair? lst)
        `(,(format-gvm-opnd (car lst) options)
          ,@(format-spaced-opnd-list (cdr lst)))
        (format-spaced-opnd-list lst)))

  (define (format-key-pair-list keys)
    (if keys
        `(" ("
          ,@(if (pair? keys)
                (let loop ((lst keys))
                  (let* ((key-pair (car lst))
                         (key (car key-pair))
                         (opnd (cdr key-pair))
                         (rest (cdr lst)))
                    `(,(string-append "(" (object->string key))
                      " "
                      ,(format-gvm-opnd opnd options)
                      ")"
                      ,@(if (pair? rest)
                            `(" "
                              ,@(loop rest))
                            `(")")))))
                `(")")))
        '()))

  (define (format-param-pattern gvm-instr)
    `("nparams="
      ,(number->string (label-entry-nb-parms gvm-instr))
      " ("
      ,@(format-opnd-list (label-entry-opts gvm-instr))
      ,@(format-key-pair-list (label-entry-keys gvm-instr))
      ,@(if (label-entry-rest? gvm-instr)
            `(" +")
            '())))

  (define (format-prim-applic prim opnds)
    (if (eq? prim **identity-proc-obj)
        `(,(format-gvm-opnd (car opnds) options))
        (cons (string-append "(" (proc-obj-name prim))
              (format-spaced-opnd-list opnds))))

  (case (gvm-instr-kind gvm-instr)

    ((label)
     `(,(format-gvm-lbl (label-lbl-num gvm-instr) options)
       " fs="
       ,(number->string (frame-size (gvm-instr-frame gvm-instr)))
       ,@(case (label-kind gvm-instr)
           ((simple)
            (let ((precedents (if (pair? bb) (bb-precedents (car bb)) '())))
              (if (pair? precedents)
                  (cons "   <-"
                        (apply
                         append
                         (map (lambda (i)
                                (list " " (format-gvm-lbl i options)))
                              precedents)))
                  '())))
           ((entry)
            `(,(if (label-entry-closed? gvm-instr)
                   " closure-entry-point "
                   " entry-point ")
              ,@(format-param-pattern gvm-instr)))
           ((return)
            `(" return-point"))
           ((task-entry)
            `(" task-entry-point"))
           ((task-return)
            `(" task-return-point"))
           (else
            (compiler-internal-error
             "format-gvm-instr-code, unknown label kind")))))

    ((apply)
     `("  "
       ,(format-gvm-opnd (apply-loc gvm-instr) options)
       " = "
       ,@(format-prim-applic (apply-prim gvm-instr)
                             (apply-opnds gvm-instr))))

    ((copy)
     `("  "
       ,(format-gvm-opnd (copy-loc gvm-instr) options)
       " = "
       ,(format-gvm-opnd (copy-opnd gvm-instr) options)))

    ((close)
     (let loop ((lst (close-parms gvm-instr))
                (sep "  close"))
       (if (pair? lst)
           `(,sep
             ,@(format-closure-parms (car lst))
             ,@(loop (cdr lst)
                     ","))
           '())))

    ((ifjump)
     `("  if "
       ,@(format-prim-applic (ifjump-test gvm-instr)
                             (ifjump-opnds gvm-instr))
       ,(if (ifjump-poll? gvm-instr)
            " jump/poll"
            " jump")
       " fs="
       ,(number->string (frame-size (gvm-instr-frame gvm-instr)))
       " "
       "" ;; tag as a branch destination
       ,(format-gvm-lbl (ifjump-true gvm-instr) options)
       " else "
       "" ;; tag as a branch destination
       ,(format-gvm-lbl (ifjump-false gvm-instr) options)))

    ((switch)
     `("  "
       ,(if (switch-poll? gvm-instr)
            "switch/poll"
            "switch")
       " fs="
       ,(number->string (frame-size (gvm-instr-frame gvm-instr)))
       " "
       ,(format-gvm-opnd (switch-opnd gvm-instr) options)
       " ("
       ,@(let loop ((cases (switch-cases gvm-instr)))
           (if (pair? cases)
               (let ((c (car cases))
                     (next (cdr cases)))
                 `(,(format-gvm-obj (switch-case-obj c) #f)
                   " => "
                   "" ;; tag as a branch destination
                   ,(format-gvm-lbl (switch-case-lbl c) options)
                   ,@(if (null? next)
                         '()
                         `(", "
                           ,@(loop next)))))
               '()))
       ") "
       "" ;; tag as a branch destination
       ,(format-gvm-lbl (switch-default gvm-instr) options)))

    ((jump)
     `("  "
       ,(if (jump-poll? gvm-instr)
            (if (jump-safe? gvm-instr) "jump/poll/safe" "jump/poll")
            (if (jump-safe? gvm-instr) "jump/safe" "jump"))
       " fs="
       ,(number->string (frame-size (gvm-instr-frame gvm-instr)))
       " "
       "" ;; tag as a branch destination
       ,(format-gvm-opnd (jump-opnd gvm-instr) options)
       ,@(if (jump-ret gvm-instr)
             `(" "
               ,(format-gvm-opnd return-addr-reg options)
               "="
               ,(format-gvm-opnd (make-lbl (jump-ret gvm-instr)) options))
             '())
       ,@(if (jump-nb-args gvm-instr)
             `(" nargs="
               ,(number->string (jump-nb-args gvm-instr)))
             '())))

    (else
     (compiler-internal-error
      "format-gvm-instr-code, unknown 'gvm-instr':"
      gvm-instr))))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
;;
;; Operand writing:
;; ---------------

(define (write-gvm-opnd gvm-opnd options port)
  (let ((str (format-gvm-opnd gvm-opnd options)))
    (display str port)
    (string-length str)))

(define (format-gvm-opnd gvm-opnd options)
  (cond ((not gvm-opnd)
         ".")
        ((reg? gvm-opnd)
         (string-append "r" (number->string (reg-num gvm-opnd))))
        ((stk? gvm-opnd)
         (string-append "frame[" (number->string (stk-num gvm-opnd)) "]"))
        ((glo? gvm-opnd)
         (string-append "global[" (object->string (glo-name gvm-opnd)) "]"))
        ((clo? gvm-opnd)
         (string-append (format-gvm-opnd (clo-base gvm-opnd) options)
                        "["
                        (number->string (clo-index gvm-opnd))
                        "]"))
        ((lbl? gvm-opnd)
         (format-gvm-lbl (lbl-num gvm-opnd) options))
        ((obj? gvm-opnd)
         (format-gvm-obj (obj-val gvm-opnd) #t))
        (else
         (compiler-internal-error
           "format-gvm-opnd, unknown 'gvm-opnd':"
           gvm-opnd))))

(define (format-gvm-lbl lbl options)
  (string-append (if (memq 'new options) "%" "#") (number->string lbl)))

(define (format-gvm-obj val quote?)
  (let ((str
         (cond ((proc-obj? val)
                (string-append
                 (if (proc-obj-primitive? val)
                     "#<primitive "
                     "#<procedure ")
                 (proc-obj-name val)
                 ">"))
               ((lbl-obj? val)
                (string-append (format-gvm-lbl (lbl-obj-lbl val) '())
                               "->"
                               (format-gvm-lbl (lbl-obj-new-lbl val) '(new))))
               (else
                (object->string val)))))
    (if (or (not quote?)
            (proc-obj? val)
            (lbl-obj? val)
            (number? val)
            (boolean? val)
            (char? val)
            (string? val)
            (void-object? val))
        str
        (string-append "'" str))))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define (make-debug-info-state)
  (vector #f              ;; debug-info?
          (queue-empty)   ;; first-class-label-queue
          (queue-empty))) ;; var-descr-queue

(define (debug-info-generate debug-info-state get-id sharing-table)

  (define (assign-ids i lst)
    (if (null? lst)
      '()
      (cons (list->vect (cons (get-id i) (car lst)))
            (assign-ids (+ i 1) (cdr lst)))))

  (debug-info-compact-using-sharing
   sharing-table
   (if (vector-ref debug-info-state 0) ;; debug-info?
       (vector (list->vect
                (assign-ids
                 0
                 (queue->list
                  (vector-ref debug-info-state 1)))) ;; first-class-label-queue
               (list->vect
                (queue->list
                 (vector-ref debug-info-state 2)))) ;; var-descr-queue
       #f)))

(define (debug-info-compact-using-sharing sharing-table obj)

  (define (compact obj)
    (if (or (string? obj)
            (pair? obj)
            (box-object? obj)
            (vector-object? obj))
        (let ((x (table-ref sharing-table obj #f)))
          (or x
              (cond ((string? obj)
                     (table-set! sharing-table obj obj)
                     obj)
                    ((pair? obj)
                     (let ((p (cons #f #f)))
                       (table-set! sharing-table obj p)
                       (set-car! p (compact (car obj)))
                       (set-cdr! p (compact (cdr obj)))
                       p))
                    ((box-object? obj)
                     (let ((b (box-object #f)))
                       (table-set! sharing-table obj b)
                       (set-box-object! b (compact (unbox-object obj)))
                       b))
                    (else
                     (let* ((len (vector-length obj))
                            (v (make-vector len)))
                       (table-set! sharing-table obj v)
                       (let loop ((i (- len 1)))
                         (if (< i 0)
                             v
                             (begin
                               (vector-set! v i (compact (vector-ref obj i)))
                               (loop (- i 1))))))))))
        obj))

  (compact obj))

(define (debug-info-add! debug-info-state node slots frame)

  (define first-class-label-queue (vector-ref debug-info-state 1))
  (define var-descr-queue (vector-ref debug-info-state 2))

  (define (add-var-descr! descr)

    (define (index x lst)
      (let loop ((lst lst) (i 0))
        (cond ((not (pair? lst))    #f)
              ((equal? (car lst) x) i)
              (else                 (loop (cdr lst) (+ i 1))))))

    (let ((n (index descr (queue->list var-descr-queue))))
      (if n
          n
          (let ((m (length (queue->list var-descr-queue))))
            (queue-put! var-descr-queue descr)
            m))))

  (define (encode slot)
    (let ((v (car slot))
          (i (cdr slot)))
      (+ (* i 32768)
         (if (pair? v)
           (* (add-var-descr! (map encode v)) 2)
           (+ (* (add-var-descr! (var-name v)) 2)
              (if (var-boxed? v) 1 0))))))

  (define (closure-env-slot closure-vars stack-slots)
    (let loop ((i 1) (lst1 closure-vars) (lst2 '()))
      (if (null? lst1)
        lst2
        (let ((x (car lst1)))
          (if (not (frame-live? x frame))
            (loop (+ i 1)
                  (cdr lst1)
                  lst2)
            (let ((y (assq (var-name x) stack-slots)))
              (if (and y (not (eq? x (cadr y))))
                (begin
                  (if (< (var-lexical-level (cadr y))
                         (var-lexical-level x))
                      (let ()
                        (##namespace ("" pp));****************
                        (pprint (list
                             'closure-vars: (map var-name closure-vars)
                             'stack-slots: (map car stack-slots)
                             'source: (source->expression (node-source node))
                             ))
                        (compiler-internal-error
                         "debug-info-add!, variable conflict")))
                  (loop (+ i 1)
                        (cdr lst1)
                        lst2))
                (loop (+ i 1)
                      (cdr lst1)
                      (cons (cons x i) lst2)))))))))

  (define (accessible-slots)
    (let loop1 ((i 1)
                (lst1 slots)
                (lst2 '())
                (closure-env #f)
                (closure-env-index #f))
      (if (pair? lst1)
        (let* ((var (car lst1))
               (x (frame-live? var frame)))
          (cond ((pair? x) ; closure environment?
                 (if (or (not closure-env) (eq? var closure-env))
                   (loop1 (+ i 1)
                          (cdr lst1)
                          lst2
                          var
                          i)
                   (compiler-internal-error
                    "debug-info-add!, multiple closure environments")))
                ((or (not x) (var-temp? x)) ; not live or temporary var
                 (loop1 (+ i 1)
                        (cdr lst1)
                        lst2
                        closure-env
                        closure-env-index))
                (else
                 (let* ((name (var-name x))
                        (y (assq name lst2)))
                   (if (and y (not (eq? x (cadr y))))
                     (let ((level-x (var-lexical-level x))
                           (level-y (var-lexical-level (cadr y))))
                       (cond ((< level-x level-y)
                              (loop1 (+ i 1)
                                     (cdr lst1)
                                     lst2
                                     closure-env
                                     closure-env-index))
                             ((< level-y level-x)
                              (loop1 (+ i 1)
                                     (cdr lst1)
                                     (cons (cons name (cons x i)) (remq y lst2))
                                     closure-env
                                     closure-env-index))
                             (else
                              ; Two different live variables have the same
                              ; name and lexical level, both variables will
                              ; be kept in the debugging information
                              ; descriptor even though in the actual program
                              ; only one of the two variables is in scope.
                              ; "flatten" causes this condition to happen.
                              ; TODO: take variable scopes into account.
                              (loop1 (+ i 1)
                                     (cdr lst1)
                                     (cons (cons name (cons x i)) lst2)
                                     closure-env
                                     closure-env-index))))
                     (loop1 (+ i 1)
                            (cdr lst1)
                            (cons (cons name (cons x i)) lst2)
                            closure-env
                            closure-env-index))))))
        (let* ((x
                (if closure-env
                  (closure-env-slot (frame-live? closure-env frame) lst2)
                  '()))
               (accessible-stack-slots
                (map cdr lst2)))
          (if (null? x)
            accessible-stack-slots
            (cons (cons x closure-env-index)
                  accessible-stack-slots))))))

  (let* ((env
          (and node (node-env node)))
         (label-descr
          (cons (if (and env
                         (debug? env)
                         (or (debug-location? env)
                             (debug-source? env)))
                    (let ((src (node-source node)))
                      (vector-set! debug-info-state 0 #t) ;; debug-info? = #t
                      (if (debug-location? env)
                          (if (debug-source? env)
                              src
                              (source-locat src))
                          (source->expression src)))
                    #f)
                (if (and env
                         (or (and (debug? env)
                                  (debug-environments? env))
                             (environment-map? env)))
                    (begin
                      (vector-set! debug-info-state 0 #t) ;; debug-info? = #t
                      (map encode (accessible-slots)))
                    '()))))

    (queue-put! first-class-label-queue label-descr)

    label-descr))

;;; - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

(define (virtual.begin!) ; initialize module
  (set! *opnd-table* '#())
  (set! *opnd-table-alloc* 0)
  '())

(define (virtual.end!) ; finalize module
  (set! *opnd-table* '())
  '())

;;;----------------------------------------------------------------------------
;;
;; GVM interpret
;; -----------------------------------------

;; Branch counters

(define (mark-exit-jump state)
  (instr-comment-add! (InterpreterState-current-instruction state) 'exit-jump #t))

(define (increment-branch-counter state target-bbs target-bb)
  (let* ((branch-instr
          (InterpreterState-current-instruction state))
         (table1
          (get-branch-counters branch-instr))
         (table2
          (or (table-ref table1 target-bbs #f)
              (let ((t (make-table)))
                (table-set! table1 target-bbs t)
                t)))
         (count
          (+ 1 (table-ref table2 (bb-lbl-num target-bb) 0)))
         (ctx
          (InterpreterState-ctx state)))
    (if (> count (vector-ref ctx 1))
        (vector-set! ctx 1 count))
    (table-set! table2 (bb-lbl-num target-bb) count)))

(define (get-branch-counters branch-instr)
  (or (instr-comment-get branch-instr 'branch-counter)
      (let ((t (make-table 'test: eq?)))
        (instr-comment-add! branch-instr 'branch-counter t)
        t)))

;; HELPERS
(define (get-total-number-of-instructions module-procs)
  (define count 0)
  (for-each
    (lambda (proc)
      (bbs-for-each-bb
        (lambda (bb)
          (set! count (+ count
                        1 ;; branch
                        (if (eq? (label-kind (bb-label-instr bb)) 'entry) 1 0) ;; only entry require computation
                        (length (bb-non-branch-instrs bb)))))
        (proc-obj-code proc)))
    module-procs)
  count)

(define (get-label-parameters-info nargs closed?)
    (pcontext-map ((target-label-info target) nargs closed?)))

(define (get-jump-parameters-info nargs)
  (pcontext-map ((target-jump-info target) nargs)))

(define (get-args-loc parameters-info)
  (let ((nargs (apply max 0 (filter number? (map car parameters-info))))) ;; params start at 1
    (map (lambda (i) (cdr (assq i parameters-info))) (iota nargs 1))))

(define (get-closure-loc params-info)
  (cdr (assq 'closure-env params-info)))

(define (gvm-proc-obj-primitive? obj)
    (and (proc-obj? obj) (proc-obj-primitive? obj) (not (proc-obj-code obj))))

;; NEW INTERPRET

(define (get-expected-type-at-register types reg)
  (let* ((type-locs (vector-ref types 0))
         (n-registers (vector-ref type-locs 0)))
    (if (< reg n-registers)
        (vector-ref types (+ (* reg 2) (+ locenv-start-regs 1)))
        (error "the following register is not live but is being checked" reg))))

(define (get-expected-type-at-frame types slot)
    (let* ((type-locs (vector-ref types 0))
           (n-registers (vector-ref type-locs 0))
           (n-slots (vector-ref type-locs 1)))
  (if (<= slot n-slots)
      (vector-ref types (+ (* (- slot 1) 2) (+ locenv-start-regs (* 2 n-registers) 1)))
      (error "the following frame slot is not live but is being checked" slot))))

(define (get-expected-type-at types loc)
  (cond
    ((reg? loc) 
      (get-expected-type-at-register types (reg-num loc)))
    ((stk? loc)
      (get-expected-type-at-frame types (stk-num loc)))
    (else (error "cannot get expected type from" loc))))

(define (instr-for-each-type instr proc)
  (let ((types (gvm-instr-types instr)))
    (if types ;; nothing to do if no types, happens when version limit is at 0
        (let* ((type-locs (vector-ref types 0))
               (n-registers (vector-ref type-locs 0))
               (n-slots (vector-ref type-locs 1))
               (n-free (vector-ref type-locs 2))
               (frame (gvm-instr-frame instr))
               (regs (frame-regs frame))
               (slots (frame-slots frame)))
          (for-each
            (lambda (reg index)
              (if (frame-live? (list-ref regs reg) frame)
                  (proc (make-reg reg) (vector-ref types index))))
            (iota n-registers)
            (iota n-registers (+ locenv-start-regs 1) 2))

          (for-each
            (lambda (slot index)
              (if (frame-live? (list-ref slots (- n-slots slot)) frame)
                  (proc (make-stk slot) (vector-ref types index))))
            (iota n-slots 1)
            (iota n-slots (+ locenv-start-regs (* 2 n-registers) 1) 2))))))

(define (interpret-procedure? x)
  (or (proc-obj? x)
      (Closure? x)
      (and (Label? x)
            (eq? (bb-label-kind (lbl-num->bb (Label-id x) (Label-bbs x)))
                'entry))))

(define (interpret-vector? x) (and (vector? x) (not (proc-obj? x))))

(define (assert-types state instr)
  (define assert? (InterpreterState-assert-types? state))
  (define tctx (make-tctx))
  (define rte (InterpreterState-rte state))
  (define bb (InterpreterState-bb state))
  (define (is-value? x) (lambda (y) (eq? x y)))

  (define bits-to-checker
    (list
      (cons type-false-bit     (is-value? #f))
      (cons type-true-bit      (is-value? #t))
      (cons type-null-bit      null?)
      (cons type-void-bit      ##void-constant?)
      (cons type-eof-bit       eof-object?)
      (cons type-absent-bit    absent-object?)
      (cons type-bignum-bit    ##bignum?)
      (cons type-ratnum-bit    ##ratnum?)
      (cons type-flonum-bit    flonum?)
      (cons type-cpxnum-bit    ##cpxnum?)
      (cons type-char-bit      char?)
      (cons type-symbol-bit    symbol?)
      (cons type-keyword-bit   keyword?)
      (cons type-string-bit    string?)
      (cons type-procedure-bit interpret-procedure?)
      (cons type-vector-bit    interpret-vector?)
      (cons type-u8vector-bit  u8vector?)
      (cons type-s8vector-bit  s8vector?)
      (cons type-u16vector-bit u16vector?)
      (cons type-s16vector-bit s16vector?)
      (cons type-u32vector-bit u32vector?)
      (cons type-s32vector-bit s32vector?)
      (cons type-u64vector-bit u64vector?)
      (cons type-s64vector-bit s64vector?)
      (cons type-f32vector-bit f32vector?)
      (cons type-f64vector-bit f64vector?)
      (cons type-pair-bit      pair?)
      (cons type-box-bit       box?)
      (cons type-return-bit    has-type-return?)))

    ;; Gather length relations between objects in rte
    (define (generic-length obj)
      (cond
        ((vector? obj) (vector-length obj))
        ((string? obj) (string-length obj))
        ((u8vector? obj) (u8vector-length obj))
        (else #f)))
    (define length-table (make-table))
    (define (length-table-set! id len) (table-set! length-table id len))
    (define (length-table-ref id) (table-ref length-table id #f))

    (define (register-lengths)
      (instr-for-each-type
        instr
        (lambda (loc expected-type)
          (let* ((value (InterpreterState-ref state loc safe: #f))
                 (maybe-length (generic-length value))
                 (length-range (type-motley-length-range (type-motley-force tctx expected-type)))
                 (lo (type-fixnum-range-lo length-range))
                 (hi (type-fixnum-range-hi length-range)))
            (if (and
                  maybe-length
                  (length-bound? lo)
                  (length-bound? hi)
                  (length-bound-same-object? lo hi))
              (length-table-set! (length-bound-object lo) maybe-length))))))

  (define (typecheck throw-error value expected-type)
    (define (typecheck-generic)
      (define motley-mutable-bits (type-motley-mut-bitset expected-type))
      (define motley-non-mutable-bits (type-motley-not-mut-bitset expected-type))

      (define (allowed-mutable? bit) (not (zero? (bitwise-and bit motley-mutable-bits))))
      (define (allowed-non-mutable? bit) (not (zero? (bitwise-and bit motley-non-mutable-bits))))

      (define (allowed? bit value)
        (or
          (and (allowed-mutable? bit) (mutable? value))
          (and (allowed-non-mutable? bit) (not (mutable? value)))))

      (define (mutable? x) (and (not (has-type-return? x)) (##mem-allocated? x) (##mutable? x)))

      (let loop ((bit-checker-pair bits-to-checker))
        (if (null? bit-checker-pair)
            (or (fixnum? value) (allowed? type-other-bit value))
            (let ((bit (caar bit-checker-pair))
                  (checker (cdar bit-checker-pair)))
              (if (checker value)
                (allowed? bit value)
                (loop (cdr bit-checker-pair)))))))

    (define (typecheck-fixnum)
      (let* ((fixnum-range (type-motley-fixnum-range expected-type))
             (lo (type-fixnum-range-lo fixnum-range))
             (hi (type-fixnum-range-hi fixnum-range)))

        (define (actual-length-compare comp value length-bound)
          (let* ((object (length-bound-object length-bound))
                 (offset (length-bound-offset length-bound))
                 (actual-length (length-table-ref object)))
            (or (not actual-length) ;; object unknown
                (comp value (+ actual-length offset)))))

        (define (actual-length<= value length-bound)
          (actual-length-compare <= value length-bound))

        (define (actual-length>= value length-bound)
          (actual-length-compare >= value length-bound))

        (define (over-lo? value)
          (cond
           ((length-bound? lo) (actual-length>= value lo))
           ((fixnum? lo) (>= value lo))
           (else #t))) ;; ignore other cases

        (define (below-hi? value)
          (cond
           ((length-bound? hi) (actual-length<= value hi))
           ((fixnum? hi) (<= value hi))
           (else #t))) ;; ignore other cases

        (or (not (fixnum? value)) (and (over-lo? value) (below-hi? value)))))

    (when (not (and (typecheck-fixnum) (typecheck-generic)))
        (throw-error)))

  (define (check-return-labels)
    (let* ((frame (gvm-instr-frame instr))
           (regs (frame-regs frame))
           (slots (frame-slots frame)))
      (for-each
        (lambda (r var)
          (when (frame-live? var frame)
                (let ((value (InterpreterState-ref state (make-reg r))))
                  (if (and (eq? var ret-var)
                           (not (has-type-return? value)))
                    (throw-error (make-reg r) value "label")))))
        (iota (length regs))
        regs)
      
      (for-each
        (lambda (i var)
          (when (frame-live? var frame)
                (let ((value (InterpreterState-ref state (make-stk i))))
                  (if (and (eq? var ret-var)
                           (not (has-type-return? value)))
                    (throw-error (make-stk i) value "label")))))
        (iota (length slots) 1)
        (reverse slots))))

  (define (throw-error slot-num value expected)
    (define slot-name
      (cond ((reg? slot-num) (string-append "reg[" (number->string (reg-num slot-num)) "]"))
            ((stk? slot-num) (string-append "frame[" (number->string (stk-num slot-num)) "]"))
            (else slot-num)))
    (InterpreterState-raise-error state
                                  "GVM type error:"
                                  slot-name
                                  "has value"
                                  (gvm-interpreter-obj->string state value)
                                  "but expected type"
                                  expected))

  (when assert?
    ;(check-return-labels)
    (register-lengths)
    (instr-for-each-type
      instr
      (lambda (loc expected-type)
        (let ((value (InterpreterState-ref state loc safe: #f))
              (expected-type (type-motley-force tctx expected-type)))
          (if (not (eq? value empty-stack-slot))
            (typecheck
              (lambda () (throw-error loc value expected-type))
              value
              expected-type)))))))

(define backend-nb-args-in-registers 3) ;; TODO: get from backend
(define backend-return-label-location (reg-num 0))
(define backend-closure-location (make-reg 4))
(define backend-return-result-location (make-reg 1))
(define (nb-args-on-stack nb-args) (max 0 (- nb-args backend-nb-args-in-registers)))
(define (nb-args-in-registers nb-args) (- nb-args (nb-args-on-stack nb-args)))

(define (gvm-interpret gvm-interpret-ctx)
  ;; comment/uncomment to stop execution or not when an error happens in the GVM interpreter
  (define (with-exception-catcher _ f) (f))

  (with-exception-catcher
    (lambda (e) (display-exception e))
    (lambda ()
      (pprint '***GVM-Interpreter)
      (let ((state (init-interpreter-state gvm-interpret-ctx)))
        (InterpreterState-execution-loop state)
        (InterpreterState-primitive-counter-trace state)
        (InterpreterState-bb-execution-count-trace state gvm-interpret-ctx)))))

(define (InterpreterState-execution-loop state)
  (let loop ()
    (when (not (InterpreterState-done? state))
      (InterpreterState-debug-log state)
      (InterpreterState-step state)
      (loop))))

(define-type SpecialReturnAddress)
(define exit-return-address (make-SpecialReturnAddress))

(define empty-stack-slot (gensym 'empty-stack-slot))

(define-type InterpreterState
  ;; execution state
  (rte unprintable:)
  (procedures unprintable:)
  (bbs unprintable:)
  (bb unprintable:)
  instr-index
  done?
  ;; traces
  debug-state
  debug-tag
  debug-shift-left
  debug-shift-right
  debug-predicate
  assert-types?
  (primitive-counter unprintable:)
  (bbs-names unprintable:)
  (bb-execution-count unprintable:)
  ctx)

(define (InterpreterState-stack state) (RTE-stack (InterpreterState-rte state)))

(define (init-interpreter-state gvm-interpret-ctx)
  (define (add-global-primitive rte name)
    (define prim-proc-obj
      (make-proc-obj ;; I don't know what these do, but they are not used anyway
        (symbol->string name)
        #f
        #t ;; is a primitive
        #f
        #f
        #t
        #f
        #f
        '()
        '(#f)))
    (RTE-global-set! rte name prim-proc-obj))

  (let* ((module-procs (vector-ref gvm-interpret-ctx 0))
         (main-proc (car module-procs))
         (main-bbs (proc-obj-code main-proc))
         (entry-lbl-num (bbs-entry-lbl-num main-bbs))
         (state
          (make-InterpreterState
            (init-RTE)                               ;; rte
            module-procs                             ;; all procedures in program
            main-bbs                                 ;; bbs
            (lbl-num->bb entry-lbl-num main-bbs)     ;; bb
            0                                        ;; instr index
            #f                                       ;; done?
            #f                                       ;; debug-state
            #f                                       ;; debug-tag
            0                                        ;; debug-shift-left
            0                                        ;; debug-shift-right
            #f                                       ;; debug-predicate
            #f                                       ;; assert-types?
            (make-table)                             ;; primitive counter
            (make-table test: eq? weak-keys: #t)     ;; bbs-names
            (make-table test: eq?)                   ;; bb-execution-count
            gvm-interpret-ctx))                      ;; ctx
         (rte (InterpreterState-rte state)))
    ;; connect RTE to the state
    (RTE-state-set! rte state)
    ;; read name of each bbs from global proc objects
    (for-each (lambda (proc) (InterpreterState-register-bbs-name! state proc)) module-procs)
    ;; add sentinel that acts as program exit return address
    (RTE-registers-set! rte 0 exit-return-address)
    ;; Add some primitive to the global environment
    ;; When executed these will be looked up by name in the jumpable primitive table
    ;; or with eval
    (add-global-primitive rte '##gvm-interpreter-debug)
    (add-global-primitive rte '##fixnum->string)
    (add-global-primitive rte 'command-line)

    (InterpreterState-increment-bb-execution-count! state)
  
    state))

(define (InterpreterState-raise-error state . messages)
  (define (display-error s) (display s (current-error-port)))

  (let* ((bbs (InterpreterState-bbs state))
         (bb (InterpreterState-bb state))
         (bbs-name (or (InterpreterState-get-bbs-name state bbs) "?"))
         (bb-num (bb-lbl-num bb)))
    (display-error "Gambint Error in BBS ")
    (display-error bbs-name)
    (display-error " - basic block #")
    (display-error bb-num)
    (display-error "\n  ")
    (let* ((instr (InterpreterState-current-instruction state))
           (node (instr-comment-get instr 'node))
           (src (node-source node))
           (loc (and src (source-locat src)))
           (filename
            (if (and loc (string? (vector-ref loc 0)))
                (vector-ref loc 0)
                "<no filename>"))
           (line
              (if (and loc (string? (vector-ref loc 0)))
                  (+ (**filepos-line (vector-ref loc 1)) 1)
                  0)))
      (display-error "in ")
      (display-error filename)
      (display-error "@")
      (display-error line)
      (display-error "\n"))
    (display-error "\nBasic Block:\n")
    (set! show-frame? #t)
    (write-bb bb '() (current-error-port))
    (display-error "\n")
    (display-error "\nInterpreter state:\n")
    (InterpreterState-##gvm-interpreter-debug state #t)
    (InterpreterState-debug-log state)
    (for-each (lambda (s) (display-error " ") (display-error s)) messages)
    (display-error "\n")
    (error 1)))

(define (InterpreterState-increment-bb-execution-count! state)
  (define bbs (InterpreterState-bbs state))
  (define bb (InterpreterState-bb state))
  (define bb-execution-count (InterpreterState-bb-execution-count state))
  (define bbs-count
    (begin
      (if (not (table-ref bb-execution-count bbs #f))
        (table-set! bb-execution-count bbs (make-table test: eq?)))
      (table-ref bb-execution-count bbs)))

  (table-set! bbs-count bb (+ (table-ref bbs-count bb 0) 1)))

(define (InterpreterState-get-bb-execution-count state bbs bb)
  (define bb-execution-count (InterpreterState-bb-execution-count state))
  (define bbs-count (table-ref bb-execution-count bbs #f))
  (if (not bbs-count) 0 (table-ref bbs-count bb 0)))

(define (InterpreterState-instr-index-increment! state last-instr)
  ;; increment index if instruction is not a jump
  ;; jump instruction reset index to 0 instead
  (or (memq (gvm-instr-kind last-instr) '(jump ifjump))
      (InterpreterState-instr-index-set! state (+ (InterpreterState-instr-index state) 1))))

(define (InterpreterState-bb-execution-count-trace state gvm-interpret-ctx)
  ;;(define (with-output-to-file _ f) (f))
  (define-type BBUsage
    (bbs unprintable:)
    orig-lbl-num
    (specialized-blocks unprintable:))

  (define (json . rest)
    (define (keyword->key k) (object->string (keyword->string k)))
    (define (value->string v)
      (cond
        ((string? v) v)
        ((number? v) (number->string v))
        ((list? v) (list->json v))
        ((table? v) (table->json v))
        (else (error "json - unsupported datatype" v))))
    (define (list->json l)
      (string-append
        "["
          (string-concatenate (map value->string l) ", ")
        "]"))
    (define (table->json t)
      (define (to-keyword x)
        (cond
          ((string? x) (string->keyword x))
          ((number? x) (to-keyword (number->string x)))
          (else (error "json - unsupported key type" x))))
      (apply
        json
        (let loop ((key-value (table->list t)))
          (cons (to-keyword key) (cons (value->string value) (loop (cdr key-value)))))))

    (call-with-output-string
      (lambda (port)
        (define (output . rest) (apply println port: port rest))
        (output "{")
        (let loop ((rest rest))
          (when (pair? rest)
            (if (or (not (keyword? (car rest))) (null? (cdr rest))) (error "json expected key-value pair, got" rest))
            (output (keyword->key (car rest)) ":" (value->string (cadr rest)) (if (null? (cddr rest)) "" ","))
            (loop (cddr rest))))
        (output "}"))))

  (define specialized-blocks '())

  (define (collect-specialized-bb bb bbs)
    (set! specialized-blocks
      (cons
        (json
          id: (bb-lbl-num bb)
          origin: (or (instr-comment-get (bb-label-instr bb) 'orig-lbl) (error "no orig-lbl" bb))
          bbs: (object->string (InterpreterState-get-bbs-name state bbs))
          source: (object->string (object->string (source->expression (node-source (instr-comment-get (bb-label-instr bb) 'node)))))
          usage: (InterpreterState-get-bb-execution-count state bbs bb)
          context: (object->string (format-concatenate (format-gvm-instr-frame (bb-label-instr bb) '()))))
        specialized-blocks)))

  (for-each
    (lambda (module-proc)
      (let ((bbs (proc-obj-code module-proc)))
        (bbs-for-each-bb (lambda (bb) (collect-specialized-bb bb bbs)) bbs)))
    (vector-ref gvm-interpret-ctx 0))

  (let ((content (json specialized-cfg: specialized-blocks)))
    (with-output-to-file "visual-sbbv.json" (lambda () (display content)))))

(define (InterpreterState-register-bbs-name! state proc)
  (table-set! (InterpreterState-bbs-names state) (proc-obj-code proc) (proc-obj-name proc)))

(define (InterpreterState-get-bbs-name state bbs)
  (table-ref (InterpreterState-bbs-names state) bbs #f))

(define (InterpreterState-primitive-counter-increment state name)
  (let ((table (InterpreterState-primitive-counter state)))
    (table-set! table name (+ 1 (table-ref table name 0)))))

(define (InterpreterState-primitive-counter-trace state)
  (pprint '***primitive-call-counter)
  (table-for-each (lambda a (pprint a)) (InterpreterState-primitive-counter state))
  (pprint (list 'total-gvm-instructions (get-total-number-of-instructions (InterpreterState-procedures state)))))

(define (InterpreterState-current-instruction state)
  (let* ((bb (InterpreterState-bb state))
         (instructions (bb-non-branch-instrs bb))
         (instr-index (InterpreterState-instr-index state)))
    (cond
      ((< instr-index (length instructions)) (list-ref instructions instr-index))
      (else (bb-branch-instr bb)))))

(define (InterpreterState-step state)
  (let* ((instr (InterpreterState-current-instruction state)))
    (InterpreterState-execute-instr state instr)
    (InterpreterState-instr-index-increment! state instr)))

(define (InterpreterState-execute-instr state instr)
  (case (gvm-instr-kind instr)
      ((apply)
        (InterpreterState-execute-apply state instr)
        (assert-types state instr))
      ((copy)
        (InterpreterState-execute-copy state instr)
        (assert-types state instr))
      ((close)
        (InterpreterState-execute-close state instr)
        (assert-types state instr))
      ((ifjump)
        (InterpreterState-primitive-counter-increment state "#gvm:ifjump")
        (InterpreterState-execute-ifjump state instr))
      ((jump)
        (InterpreterState-primitive-counter-increment
          state
          (if (jump-safe? instr) "#gvm:jump/safe" "#gvm:jump"))
        (InterpreterState-execute-jump state instr))
      (else
        (InterpreterState-raise-error state "unknown instruction" (gvm-instr-kind instr)))))

(define (InterpreterState-execute-copy state instr)
  (let* ((rte (InterpreterState-rte state))
         (opnd (copy-opnd instr))
         (value (if opnd (InterpreterState-ref state opnd) empty-stack-slot)) ;; #f opnd means allocation of a slot
         (target (copy-loc instr)))
    (RTE-set! rte target value)))

(define (make-Interpreter-custom-inlinable-primitives)
  (define t (make-table test: eq?))

  (define (add! name p)
    (table-set! t name p))

  (add!
    '##first-argument
    (lambda (first . rest) (if (null? rest) first (car rest)))) ;; hack for bbv benchmarks


  (add! '##procedure? interpret-procedure?)

  (add! '##vector? interpret-vector?)

  t)

(define Interpreter-custom-inlinable-primitives (make-Interpreter-custom-inlinable-primitives))

(define (InterpreterState-apply-inlinable-primitive state name args)
  (define (try-eval sexp) (with-exception-handler (lambda (exc) #f) (lambda () (eval sexp))))
  (define sym-name (string->symbol name))

  (let ((prim (or (table-ref Interpreter-custom-inlinable-primitives sym-name #f)
                  (try-eval sym-name))))
    (if (not prim) (InterpreterState-raise-error state "unknown primitive" name))
    (InterpreterState-primitive-counter-increment state sym-name)
    (apply prim args)))

(define (InterpreterState-execute-apply state instr)
  (let* ((rte (InterpreterState-rte state))
         (prim (apply-prim instr))
         (opnds (apply-opnds instr))
         (loc (apply-loc instr))
         (result (InterpreterState-apply-inlinable-primitive
                   state
                   (proc-obj-name prim)
                   (map (lambda (opnd) (RTE-ref rte opnd)) opnds))))
    (if loc (RTE-set! rte loc result))))

(define (InterpreterState-execute-close state instr)
  (let* ((rte (InterpreterState-rte state))
         (bbs (InterpreterState-bbs state))
         (parms (close-parms instr))
         (closures (map (lambda (_) (make-Closure #f)) parms)))

    (for-each
      (lambda (p c) (RTE-set! rte (closure-parms-loc p) c))
      parms closures)

    (for-each
      (lambda (p c)
        (let* ((opnds (closure-parms-opnds p))
               (slots (list->vector
                (cons (make-Label bbs (closure-parms-lbl p))
                      (map (lambda (opnd) (RTE-ref rte opnd)) opnds)))))
        (Closure-slots-set! c slots)))
      parms closures)))

(define (InterpreterState-get-args-positions state nargs exit-fs)
  (let* ((nargs-stk (nb-args-on-stack nargs))
         (nargs-reg (nb-args-in-registers nargs))
         (bb (InterpreterState-bb state)))
    (append
      (map make-stk (iota nargs-stk (- exit-fs nargs-stk -1)))
      (map make-reg (iota nargs-reg 1)))))

(define (InterpreterState-jumpable-primitive? state name)
  (let* ((rte (InterpreterState-rte state))
         (jumpable-primitives-table (RTE-jumpable-primitives rte)))
    (table-ref jumpable-primitives-table name #f)))

(define (InterpreterState-jump state target nargs exit-fs ret-label)
  (let ((stack (InterpreterState-stack state)))
    (cond
      ((eq? target exit-return-address)
        (mark-exit-jump state)
        (InterpreterState-done?-set! state #t))
      ((Label? target)
        (InterpreterState-call-goto
          state
          (Label-bbs target)
          (Label-id target)
          exit-fs
          nargs
          ret-label))
      ((Closure? target)
        (let ((clo-lbl (Closure-ref target 0)))
          (InterpreterState-closure-call-goto
            state
            (Label-bbs clo-lbl)
            (Label-id clo-lbl)
            exit-fs
            nargs
            ret-label
            target)))
      ((gvm-proc-obj-primitive? target)
        (let* ((name (proc-obj-name target))
               (jumpable (InterpreterState-jumpable-primitive? state name)))
          (if exit-fs (Stack-frame-exit! stack exit-fs))
          (if jumpable
            (jumpable state nargs (or ret-label (InterpreterState-ref state backend-return-label-location)))
            (let ((args (InterpreterState-pop-args! state nargs)))
              (InterpreterState-set! state backend-return-result-location
                                    (InterpreterState-apply-inlinable-primitive state name args))
              ;; if a return label is provided use it otherwise it was a tail-call and the return
              ;; location is in r0
              (let ((ret (or ret-label (InterpreterState-ref state backend-return-label-location))))
                (InterpreterState-goto state (Label-bbs ret) (Label-id ret) #f))))))
      ((proc-obj? target)
        (let ((target-bbs (proc-obj-code target)))
          (InterpreterState-call-goto
            state
            target-bbs
            (bbs-entry-lbl-num target-bbs)
            exit-fs
            nargs
            ret-label)))
      (else
        (InterpreterState-raise-error
          state
          "wrong transition"
          (gvm-interpreter-obj->string state target))))))

(define (InterpreterState-execute-jump state instr)
  (let* ((opnd (jump-opnd instr))
         (bbs (InterpreterState-bbs state))
         (ret (jump-ret instr))
         (ret-label (and ret (make-Label bbs ret)))
         (nargs (jump-nb-args instr))
         (target (InterpreterState-ref state opnd))
         (exit-fs (bb-exit-frame-size (InterpreterState-bb state))))
    (InterpreterState-jump state target nargs exit-fs ret-label)))

(define (InterpreterState-align-args! state args nparams keys opts rest? clo)
  (define rte (InterpreterState-rte state))
  (define stack (RTE-stack rte))
  (define empty (gensym 'empty))
  (define remaining-args (list-copy args))
  (define actual-params (make-vector nparams empty))
  (define n-opts-arguments (length opts))
  (define n-keys-arguments (if keys (length keys) 0))
  (define n-positional-args (- nparams
                              n-opts-arguments
                              n-keys-arguments
                              (if rest? 1 0)))

  (define n-stored 0)
  (define (store a)
    (if (= n-stored (vector-length actual-params)) (InterpreterState-raise-error state "wrong number of arguments"))
    (vector-set! actual-params n-stored a)
    (set! n-stored (+ n-stored 1)))

  (define (peek) (if (null? remaining-args) empty (car remaining-args)))
  (define (peek2)
    (cond
      ((null? remaining-args) empty)
      ((null? (cdr remaining-args)) empty)
      (else (cadr remaining-args))))
  (define (pop)
    (let ((v (peek)))
      (set! remaining-args (cdr remaining-args))
      v))
  (define (consume) (store (pop)))
  (define (empty?) (eq? (peek) empty))
  (define (empty2?) (eq? (peek2) empty))

  ;; positional arguments
  (let loop ()
    (if (< n-stored n-positional-args)
        (begin
          (if (empty?) (InterpreterState-raise-error state "missing argument") (consume))
          (loop))))

  ;; optional arguments
  (for-each
    (lambda (opt) (if (empty?) (store (RTE-ref rte opt)) (consume)))
    opts)

  ;; key arguments
  (if keys
    (let ((keyargs
            (let loop ()
              (if (and (keyword? (peek)) (not (empty2?)))
                (let ((key (pop)) (value (pop)))
                  (if (assq key keys)
                      (cons (cons key value) (loop))
                      (InterpreterState-raise-error state "unknown keyword argument")))
                '()))))
      (for-each
        (lambda (pair)
          (let* ((key (car pair))
                 (value (cdr pair))
                 (provided (assq key keyargs)))
            (if provided (store (cdr provided)) (store (RTE-ref rte value)))))
        keys)))

  ;; store rest
  (cond
    (rest?
      (store remaining-args))
    ((not (null? remaining-args))
      (InterpreterState-raise-error state "wrong number of arguments")))

  ;; write args on stack/regs
  (InterpreterState-push-args! state (vector->list actual-params))
  (if clo (InterpreterState-set! state backend-closure-location clo)))

(define (InterpreterState-push-args! state params)
  (let ((nparams (length params))
        (stack (InterpreterState-stack state)))
    (let loop ((i (nb-args-on-stack nparams))
               (params params))
      (if (> i 0)    
          (begin
            (Stack-push! stack (car params))
            (loop (- i 1) (cdr params)))
          (for-each
            (lambda (r arg) (InterpreterState-set! state (make-reg r) arg))
            (iota (nb-args-in-registers nparams) 1)
            params)))))


(define (InterpreterState-goto state bbs lbl exit-fs)
  (InterpreterState-closure-call-goto state bbs lbl exit-fs #f #f #f))

(define (InterpreterState-call-goto state bbs lbl exit-fs nargs ret)
  (InterpreterState-closure-call-goto state bbs lbl exit-fs nargs ret #f))

(define (InterpreterState-closure-call-goto state bbs lbl exit-fs nargs ret clo)
  (let* ((rte (InterpreterState-rte state))
         (stack (RTE-stack rte))
         (bb (lbl-num->bb lbl bbs))
         (label-instr (bb-label-instr bb))
         (entry-fs (bb-entry-frame-size bb)))
    (increment-branch-counter state bbs bb)
    (if exit-fs (Stack-frame-exit! stack exit-fs))
    (if (eq? (label-kind label-instr) 'entry)
        (let ((args (InterpreterState-pop-args! state nargs)))
          (InterpreterState-align-args!
            state
            args
            (label-entry-nb-parms label-instr)
            (label-entry-keys label-instr)
            (label-entry-opts label-instr)
            (label-entry-rest? label-instr)
            clo)
          (Stack-frame-enter! stack entry-fs))
        (Stack-frame-enter! stack entry-fs))
    (if ret (RTE-set! rte backend-return-label-location ret))
    (InterpreterState-bbs-set! state bbs)
    (InterpreterState-bb-set! state bb)
    (InterpreterState-increment-bb-execution-count! state)
    (InterpreterState-instr-index-set! state 0)))

(define (InterpreterState-execute-ifjump state instr)
  (let* ((test (ifjump-test instr))
         (opnds (ifjump-opnds instr))
         (args (map (lambda (opnd) (InterpreterState-ref state opnd)) opnds))
         (bbs (InterpreterState-bbs state))
         (bb (InterpreterState-bb state))
         (fs (bb-exit-frame-size bb)))
    (cond
      ((not (gvm-proc-obj-primitive? test))
        (InterpreterState-raise-error state "test is not a primitive"))
      ((InterpreterState-apply-inlinable-primitive state (proc-obj-name test) args)
        (InterpreterState-goto state bbs (ifjump-true instr) fs))
      (else
        (InterpreterState-goto state bbs (ifjump-false instr) fs)))))

(define short-string-max-length 80)

(define (string->short-string s)
  (define add-break?
    (and (> (string-length s) 0)
         (char=? (string-ref s (- (string-length s) 1)) #\newline)))

  (if (> (string-length s) short-string-max-length)
            (string-append (substring s 0 short-string-max-length) (if add-break? "...\n" "..."))
            s))

(define (gvm-interpreter-obj->string state o)
  ;; use display with output port to handle cyclic structures
  (define (obj->string-safe obj)
    (call-with-output-string
      (lambda (p)
        (output-port-readtable-set!
          p
          (readtable-max-write-length-set (output-port-readtable p) (- short-string-max-length 10)))
        (write obj p))))

  (define (tag t . names)
    (let ((elements
            (append
              (list "<<" t)
              (map (lambda (n) (string-append " " (obj->string-safe n))) names)
              '(">>"))))
    (string-concatenate elements)))

  (string->short-string
    (cond
      ((proc-obj? o)
        (tag "procedure" (proc-obj-name o)))
      ((Label? o)
        (let* ((lbl-bbs (Label-bbs o))
              (name (InterpreterState-get-bbs-name state lbl-bbs)))
          (tag "label"
              (or name "?")
              (string-append "#" (number->string (Label-id o))))))
      ((Closure? o)
        (let* ((clo-lbl (Closure-ref o 0))
              (clo-bbs (Label-bbs clo-lbl))
              (name (InterpreterState-get-bbs-name state clo-bbs)))
          (tag "closure" (or name "?"))))
      ((eq? o empty-stack-slot)
        ".")
      ((symbol? o)
        (string-append "'" (symbol->string o)))
      (else
        (obj->string-safe o)))))

(define (InterpreterState-debug-on! state)
  (InterpreterState-debug-state-set! state #t))

(define (InterpreterState-debug-off! state)
  (InterpreterState-debug-tag-set! state #f)
  (InterpreterState-debug-shift-left-set! state 0)
  (InterpreterState-debug-shift-right-set! state 0)
  (InterpreterState-debug-predicate-set! state #f)
  (InterpreterState-debug-state-set! state #f))

(define (InterpreterState-debug-count! state count)
  (InterpreterState-debug-state-set! state count))

(define (InterpreterState-debug? state)
  (let* ((debug-state (InterpreterState-debug-state state))
         (debug-predicate (InterpreterState-debug-predicate state))
         (predicate? (lambda () (or (not debug-predicate) (debug-predicate state)))))
    (and debug-state
         (cond
          ((number? debug-state)
            (cond
              ((<= debug-state 0) (InterpreterState-debug-off! state) #f)
              ((predicate?) (InterpreterState-debug-state-set! state (- debug-state 1)) #t)
              (else #f)))
          (else (predicate?))))))

(define (InterpreterState-debug-log state #!key (force #f))
  (when (or force (InterpreterState-debug? state))
    (let* ((rte (InterpreterState-rte state))
           (stack (RTE-stack rte))
           (registers (RTE-registers rte))
           (bb (InterpreterState-bb state))
           (entry-fs (bb-entry-frame-size bb))
           (exit-fs (bb-exit-frame-size bb))
           (shift-left (InterpreterState-debug-shift-left state))
           (shift-right (InterpreterState-debug-shift-right state))
           (instr (InterpreterState-current-instruction state))
           (nargs (if (eq? (gvm-instr-kind instr) 'jump)
                      (or (jump-nb-args instr) 0)
                      0))
           (bbs (InterpreterState-bbs state))
           (bbs-name (InterpreterState-get-bbs-name state bbs))
           (debug-tag (InterpreterState-debug-tag state)))
      (if debug-tag (println "[Debug tag: " debug-tag "]"))
      (println "In " (or bbs-name "?") " - basic block #" (bb-lbl-num bb))
      (println "  Registers:")
      (for-each
        (lambda (i)
          (print "    " i)
          (print ": ")
          (println (gvm-interpreter-obj->string state (stretchable-vector-ref registers i))))
        (iota (stretchable-vector-length registers)))
      (println "  Frame:")
      (let* ((fp (Stack-frame-pointer stack))
             (sp (Stack-stack-pointer stack))
             (start (max 0 (- fp shift-left)))
             (end (+ sp shift-right 1)))
        (for-each
          (lambda (i)
            (define pre (cond ((= i sp) " sp ")
                              ((= i fp) " fp ")
                              (else     "    ")))
            (print pre i ": " )
            (println (gvm-interpreter-obj->string state (Stack-ref stack i))))
          (iota (- end start) start)))
      (println "  Instruction:")
      (print "    ")
      (let ((port (open-output-string)))
        (write-gvm-instr (InterpreterState-current-instruction state) '() port)
        (display (string->short-string (get-output-string port))))
      (println)
      (println "---"))))

(define (InterpreterState-ref state target #!key (safe #t))
  (let ((value (RTE-ref (InterpreterState-rte state) target safe: safe)))
    (if (and safe (eq? value empty-stack-slot))
        (InterpreterState-raise-error state "reading empty slot")
        value)))

(define (InterpreterState-set! state target value)
  (RTE-set! (InterpreterState-rte state) target value))

(define (InterpreterState-pop-args! state nargs)
  (let ((rte (InterpreterState-rte state))
        (stack (InterpreterState-stack state)))
    (let loop ((i (nb-args-on-stack nargs))
               (args (map
                       (lambda (i) (InterpreterState-ref state (make-reg i)))
                       (iota (nb-args-in-registers nargs) 1))))
      (if (> i 0)
          (loop (- i 1) (cons (Stack-pop! stack) args))
          args))))

(define-type RTE
  ;; run time environment
  (registers unprintable:)
  (stack unprintable:)
  (global-env unprintable:)
  (jumpable-primitives unprintable:)
  (state unprintable:))

(define (InterpreterState-##gvm-interpreter-debug state #!optional (arg 1)
                                                        #!key (tag #f)
                                                              (shift-left 0)
                                                              (shift-right 0)
                                                              (predicate #f))
  (InterpreterState-debug-tag-set! state tag)
  (InterpreterState-debug-shift-left-set! state shift-left)
  (InterpreterState-debug-shift-right-set! state shift-right)
  (InterpreterState-debug-predicate-set! state (eval predicate))
  (cond
    ((number? arg) (InterpreterState-debug-count! state arg))
    (arg (InterpreterState-debug-on! state))
    (else (InterpreterState-debug-off! state))))

(define (add-primitive-counter-to-primitives-table! primitives-table)
  (table-for-each
    (lambda (name primitive)
      (table-set! primitives-table name
        (lambda (state . args)
          (InterpreterState-primitive-counter-increment state (string->symbol name))
          (apply primitive state args))))
    (table-copy primitives-table)))

(define (make-gvm-jumpable-primitives)
  (define primitives-table (make-table))
  (define (register! names proc)
    (define (_register! name proc) (table-set! primitives-table name proc))
    (if (string? names)
        (_register! names proc)
        (for-each (lambda (name) (_register! name proc)) names)))


  (register!
    "##gvm-interpreter-debug"
    (lambda (state nargs ret-label)
      (apply InterpreterState-##gvm-interpreter-debug
             state
            (InterpreterState-pop-args! state nargs))
      (InterpreterState-goto state (Label-bbs ret-label) (Label-id ret-label) #f)))

  (register!
    "##dead-end"
    (lambda (state . _) (InterpreterState-raise-error state "reached ##dead-end")))

  (register!
    '("##apply" "apply")
    (lambda (state nargs ret-label)
      (let* ((apply-args (InterpreterState-pop-args! state nargs))
             (procedure (car apply-args))
             (args (cdr apply-args))
             (positionals
               (let loop ((a args))
                 (if (pair? (cdr a)) (cons (car a) (loop (cdr a))) (car a)))))
        (InterpreterState-push-args! state positionals)
        (InterpreterState-jump state procedure (length positionals) #f ret-label))))

  (register!
    "command-line"
    (lambda (state nargs ret-label)
      (InterpreterState-pop-args! state nargs)
      (InterpreterState-set! state backend-return-result-location (list ""))
      (InterpreterState-jump state ret-label #f #f ret-label)))

  (add-primitive-counter-to-primitives-table! primitives-table)
  primitives-table)

(define (init-RTE)
  (make-RTE
    (make-stretchable-vector 0)       ;; registers
    (init-Stack)                      ;; stack
    (make-table)                      ;; global env
    (make-gvm-jumpable-primitives)    ;; jumpable primitive table
    #f))                              ;; state           

(define (RTE-registers-ref rte i) (stretchable-vector-ref (RTE-registers rte) i))
(define (RTE-registers-set! rte i v) (stretchable-vector-set! (RTE-registers rte) i v))
(define (RTE-frame-ref rte i) (Stack-frame-ref (RTE-stack rte) i))
(define (RTE-frame-set! rte i v) (Stack-frame-set! (RTE-stack rte) i v))
(define (RTE-global-ref rte name)
  (let* ((sentinel (gensym))
         (g (table-ref (RTE-global-env rte) name sentinel)))
    (if (eq? g sentinel) (table-ref (make-prim-proc-table) (symbol->string name)) g)))
(define (RTE-global-set! rte name v) (table-set! (RTE-global-env rte) name v))
  
(define (RTE-param-set! rte nparams i param)
  (let* ((nb-param-registers (min nparams backend-nb-args-in-registers))
         (nb-param-frames (- nparams nb-param-registers))
         (stack (RTE-stack rte)))
    (if (< i nb-param-frames)
        (Stack-set! stack (+ (Stack-stack-pointer stack) i) param)
        (RTE-registers-set! rte (- i nb-param-frames -1) param))))

(define (RTE-set! rte target value)
  (cond
    ((reg? target) (RTE-registers-set! rte (reg-num target) value))
    ((stk? target) (RTE-frame-set! rte (stk-num target) value))
    ((glo? target) (RTE-global-set! rte (glo-name target) value))
    ((clo? target) (Closure-set! (RTE-ref rte (clo-base target)) (clo-index target) value))
    (else (error "cannot write to" target))))

(define (RTE-ref rte target #!key (safe #t))
  (with-exception-catcher
    (lambda (e)
      (if (unbound-key-exception? e)
        (InterpreterState-raise-error (RTE-state rte) (unbound-key-exception-arguments e))
        (raise e)))
    (lambda ()
      (let ((result
              (cond
                ((reg? target) (RTE-registers-ref rte (reg-num target)))
                ((stk? target) (RTE-frame-ref rte (stk-num target)))
                ((glo? target) (RTE-global-ref rte (glo-name target)))
                ((clo? target) (Closure-ref (RTE-ref rte (clo-base target)) (clo-index target)))
                ((obj? target) (obj-val target))
                ((lbl? target)
                  (let ((state (RTE-state rte)))
                    (make-Label (InterpreterState-bbs state) (lbl-num target))))
                (else (error "cannot read from" target)))))
        (if (and safe (eq? result empty-stack-slot))
            (InterpreterState-raise-error (RTE-state rte) "reading empty slot")
            result)))))

(define-type Stack
  frame-pointer
  stack-pointer
  (content unprintable:))

(define (Stack-ref s i) (stretchable-vector-ref (Stack-content s) i))
(define (Stack-set! s i v) (stretchable-vector-set! (Stack-content s) i v))
(define (Stack-frame-index s i) (+ (Stack-frame-pointer s) i -1))
(define (Stack-frame-ref s i) (Stack-ref s (Stack-frame-index s i)))
(define (Stack-frame-set! s i v) (Stack-set! s (Stack-frame-index s i) v))
(define (Stack-frame-enter! s fs) (Stack-frame-pointer-set! s (- (Stack-stack-pointer s) fs)))
(define (Stack-frame-exit! s fs) (Stack-stack-pointer-set! s (+ (Stack-frame-pointer s) fs)))
(define (Stack-stack-pointer-increment! s #!optional (n 1))
  (Stack-stack-pointer-set! s (+ (Stack-stack-pointer s) n)))
(define (Stack-stack-pointer-decrement! s) (Stack-stack-pointer-increment! s -1))
(define (Stack-pop! s)
  (let* ((sp (Stack-stack-pointer s))
         (value (Stack-ref s (- sp 1))))
    (Stack-stack-pointer-decrement! s)
    value))
(define (Stack-push! s value)
  (Stack-set! s (Stack-stack-pointer s) value)
  (Stack-stack-pointer-increment! s 1))

(define (init-Stack)
  (make-Stack
    0                                             ;; frame pointer
    0                                             ;; stack pointer
    (make-stretchable-vector empty-stack-slot)))  ;; content

;; Object model

(define-type Label
  (bbs unprintable:)
  id)

(define (has-type-return? value)
  (or (Label? value) (eq? value exit-return-address)))

(define-type Closure
  (slots unprintable:)) ;; slot 0 is label so ##closure-ref works

(define (Closure-ref clo i) (vector-ref (Closure-slots clo) i))
(define (Closure-set! clo i val) (vector-set! (Closure-slots clo) i val))
