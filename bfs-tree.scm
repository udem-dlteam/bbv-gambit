(define infinity +inf.0)

(define (make-queue) (cons '() '()))
(define (queue-empty? queue) (null? (car queue)))
(define (queue-get! queue)
  (if (queue-empty? queue)
    (error "queue-get!, queue is empty")
    (let ((x (caar queue)))
      (set-car! queue (cdar queue))
      (if (queue-empty? queue) (set-cdr! queue '()))
      x)))
(define (queue-put! queue x)
  (let ((entry (cons x '())))
    (if (queue-empty? queue)
      (set-car! queue entry)
      (set-cdr! (cdr queue) entry))
    (set-cdr! queue entry)
    x))

(define (make-set) (make-table))
(define (set-add! set x) (table-set! set x #t))
(define (set-remove! set x) (table-set! set x))
(define (set-contains? set x) (table-ref set x #f))
(define (set-for-each f set) (table-for-each (lambda (k _) (f k)) set))
(define (set-search f set) (table-search (lambda (k _) (f k)) set))
(define (set->list set) (map car (table->list set)))

(define (table-ref-or-set-default! table x)
  (let ((value (table-ref table x #f)))
    (or value
        (let ((default (make-set)))
          (table-set! table x default)
          default))))

(define (make-BFSTree source)
  (vector
    source                                  ;; source
    (list->table (list (cons source 0)))    ;; ranks table
    (make-table)                            ;; parents table
    (make-table)                            ;; children table
    (make-table)                            ;; friends table
    (make-table)))                          ;; friendlies table

(define (BFSTree-source tree) (vector-ref tree 0))
(define (BFSTree-ranks tree) (vector-ref tree 1))
(define (BFSTree-parents tree) (vector-ref tree 2))
(define (BFSTree-children tree) (vector-ref tree 3))
(define (BFSTree-friends tree) (vector-ref tree 4))
(define (BFSTree-friendlies tree) (vector-ref tree 5))

;;   Parent P of X
;;   P -> X where rank(X) = rank(P) + 1
;;
;;     P
;;     |
;;     |
;;     v
;;     X

;;   Child C of X
;;   C if a child of X if X is a parent of C

;;   Friend F of X
;;   X -> F where rank(X) >= rank(F) - 1
;;
;;  F     
;;  ^     
;;  |     P
;;  |     |
;;  \     v
;;   \--- X

(define (get-rank tree x)
  (table-ref (BFSTree-ranks tree) x infinity))
(define (set-rank! tree x rank)
  (table-set! (BFSTree-ranks tree) x rank))
(define (update-rank! tree x)
  (let* ((parent (get-parent tree x))
         (parent-rank (if parent (get-rank tree parent) infinity))
         (old-rank (get-rank tree x))
         (new-rank (+ parent-rank 1)))
    (if (= new-rank old-rank) #f (begin (set-rank! tree x new-rank) #t))))

;; all access methods are written such that adding an edge will never delete
;; another edge. However, it can make a node dirty
(define (add-friend! tree node friend)
  (set-add! (table-ref-or-set-default! (BFSTree-friends tree) node) friend)
  (set-add! (table-ref-or-set-default! (BFSTree-friendlies tree) friend) node))
(define (remove-friend! tree node friend)
  (set-remove! (table-ref-or-set-default! (BFSTree-friends tree) node) friend)
  (set-remove! (table-ref-or-set-default! (BFSTree-friendlies tree) friend) node))
(define (get-parent tree x)
  (table-ref (BFSTree-parents tree) x #f))
(define (set-parent! tree child parent)
  ;; change old parent status to friend
  (let ((old-parent (get-parent tree child)))
    (when old-parent
      (add-friend! tree old-parent child)
      (remove-child! tree old-parent child)))
  ;; if new parent was a friend remove this status
  (remove-friend! tree parent child)
  ;; set parent for child
  (table-set! (BFSTree-parents tree) child parent)
  ;; add child to new parent
  (set-add! (table-ref-or-set-default! (BFSTree-children tree) parent) child))
(define (remove-parent! tree child)
  (let ((parent (get-parent tree child)))
    (if parent (remove-child! tree parent child)))
  (table-set! (BFSTree-parents tree) child))
(define (remove-child! tree parent child)
  (set-remove!
    (table-ref (BFSTree-children tree) parent)
    child))

(define (clean-edge? tree from to)
  (>= (get-rank tree from) (- (get-rank tree to) 1)))
(define (dirty-edge? tree from to)
  (not (clean-edge? tree from to)))

(define (children-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-children tree) x)))
(define (friends-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-friends tree) x)))
(define (neighbors-for-each f tree x)
  (friends-for-each f tree x)
  (children-for-each f tree x))
(define (friendlies-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-friendlies tree) x)))
    
(define (source? tree x)
  (= (BFSTree-source tree) x))
(define (parent? tree x p)
  (eq? p (get-parent tree x)))

(define (get-lowest-ranked-incident-node tree x)
  ;; favor parent in case of tie
  (let* ((best (get-parent tree x))
         (best-rank (if best (get-rank tree best) infinity)))
    (friendlies-for-each
      (lambda (f)
        (if (not (= f x)) ;; do not include self
                          ;; it is either not the best or if it is
                          ;; then it is the only incident
          (let ((rank (get-rank tree f)))
            (when (< rank best-rank)
              (set! best f)
              (set! best-rank rank)))))
      tree
      x)
    best))

(define (fix-dirty-node! tree dirty-queue node)
  (when (not (source? tree node)) ;; source is never dirty
    (let ((new-parent (get-lowest-ranked-incident-node tree node)))
      (if new-parent (set-parent! tree node new-parent))
      (when (update-rank! tree node)
        (neighbors-for-each
          (lambda (x) (queue-put! dirty-queue x))
          tree
          node)))))

(define (add-edge! tree from to)
  (cond
    ((clean-edge? tree from to) ;; adding this edge cannot lower rank
      (add-friend! tree from to))
    (else ;; forward edge may reduce the rank of some nodes
      (let ((dirty-queue (make-queue)))
        (add-friend! tree from to)
        (queue-put! dirty-queue to)
        (let loop ()
          (when (not (queue-empty? dirty-queue))
            (fix-dirty-node! tree dirty-queue (queue-get! dirty-queue))
            (loop)))))))

(define (remove-edge! tree from to)
  (cond
    ((not (parent? tree to from)) ;; edge not in BFS, can be removed safely
      (remove-friend! tree from to))
    (else
      (let ((dirty-queue (make-queue)))
        (remove-parent! tree to)
        (queue-put! dirty-queue to)
        (let loop ()
          (when (not (queue-empty? dirty-queue))
            (fix-dirty-node! tree dirty-queue (queue-get! dirty-queue))
            (loop)))))))

;; tests

(define (make-test-graph source)
  (list->table (list (cons source '()) (cons 'source source))))
(define (test-graph-add! graph from to)
  (table-set! graph from (cons to (table-ref graph from '()))))
(define (test-graph-remove! graph from to)
  (table-set! graph from (filter (lambda (x) (not (= x to))) (table-ref graph from '()))))
(define (test-graph-rank graph target)
  (let ((queue (make-queue))
        (visited '())
        (source (table-ref graph 'source)))
    (queue-put! queue (cons 0 source))
    (set! visited (cons source visited))
    (let loop ()
      (if (queue-empty? queue)
        infinity
        (let* ((rank-node (queue-get! queue))
               (rank (car rank-node))
               (node (cdr rank-node))
               (children (table-ref graph node '())))
          (if (= node target)
              rank
              (begin
                (for-each
                  (lambda (child)
                    (when (not (memq child visited))
                      (queue-put! queue (cons (+ rank 1) child))
                      (set! visited (cons child visited))))
                  children)
                (loop))))))))

(define make-graph (make-parameter #f))
(define add!       (make-parameter #f))
(define delete!    (make-parameter #f))
(define rank-of    (make-parameter #f))

(define (get-test-expected-result test . args)
  (parameterize ((make-graph make-test-graph)
                 (add! test-graph-add!)
                 (delete! test-graph-remove!)
                 (rank-of test-graph-rank))
    (apply test args)))

(define (run test . args)
  (parameterize ((make-graph make-BFSTree)
                 (add! add-edge!)
                 (delete! remove-edge!)
                 (rank-of get-rank))
    (apply test args)))

(define fuzzy-test-N 10)
(define (run-one-fuzzy-test)
  (define (make-instruction kind edge)
    (list 'lambda '(graph) (cons (list kind) (cons 'graph edge))))
  (define (lift-instruction instr)
    (caddr instr))

  (define (random-instructions n delete-sparsity)
    (if (= n 0)
      '()
      (let ((kind (if (= (random-integer delete-sparsity) 0) 'delete! 'add!))
            (edge (list (random-integer fuzzy-test-N) (random-integer fuzzy-test-N))))
        (cons (make-instruction kind edge)
              (random-instructions (- n 1) delete-sparsity)))))

  (define (test instructions)
    (define graph ((make-graph) 0))

    (for-each (lambda (instr) ((eval instr) graph)) instructions)

    (map (lambda (n) ((rank-of) graph n)) (iota fuzzy-test-N)))

  (let* ((instructions (random-instructions 25 10))
         (expected-result (get-test-expected-result test instructions))
         (result (run test instructions)))
    (or (equal? expected-result result)
        (begin
          (pp '(fuzzy-test FAILED))
          (pp 'OUTPUT:)
          (pp result)
          (pp 'EXPECTED:)
          (pp expected-result)
          (pp 'INSTRUCTIONS:)
          (for-each pp (map lift-instruction instructions))
          #f))))

(define (fuzzy-test n)
  (let loop ((i 0))
    (when (< i n)
      (if (run-one-fuzzy-test) (loop (+ i 1))))))

(define (test1)
  (define graph ((make-graph) 0))
  ((add!) graph 1 2)
  ((add!) graph 2 3)
  ((add!) graph 3 4)
  ((add!) graph 2 4)
  ((add!) graph 0 1)
  (map (lambda (n) ((rank-of) graph n)) (iota 5)))

(define (test2)
  (define graph ((make-graph) 0))
  ((add!) graph 1 2)
  ((add!) graph 2 3)
  ((add!) graph 3 4)
  ((add!) graph 4 0)
  ((add!) graph 0 1)
  (map (lambda (n) ((rank-of) graph n)) (iota 5)))

(define (test3)
  (define graph ((make-graph) 0))
  ((add!) graph 3 3)
  ((add!) graph 2 3)
  ((add!) graph 1 2)
  ((add!) graph 0 1)
  ((delete!) graph 0 1)
  (map (lambda (n) ((rank-of) graph n)) (iota 10)))

(define (run-all . tests)
  (for-each
    (lambda (test-args)
      (let* ((test (car test-args))
             (args (cdr test-args))
             (expected (apply get-test-expected-result test args))
             (result (apply run test args)))
        (if (equal? result expected)
            (pp (list test 'OK))
            (pp (list test 'FAILED)))))
    tests))

(fuzzy-test 1000)
(run-all
  (list test1)
  (list test2)
  (list test3))
