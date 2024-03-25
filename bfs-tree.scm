(define infinity +inf.0)

(define (make-queue) (cons '() '()))
(define (queue-empty? queue) (null? (car queue)))
(define (queue-get! queue)
  (let ((x (caar queue)))
    (set-car! queue (cdar queue))
    (if (queue-empty? queue) (set-cdr! queue '()))
    x))
(define (queue-put! queue x)
  (let ((entry (cons x '())))
    (if (queue-empty? queue)
      (set-car! queue entry)
      (set-cdr! (cdr queue) entry))
    (set-cdr! queue entry)
    x))
(define (queue-peek queue) (if (queue-empty? queue) #f (caar queue)))

(define (make-set) (make-table))
(define (set-add! set x) (table-set! set x #t))
(define (set-remove! set x) (table-set! set x))
(define (set-contains? set x) (table-ref set x #f))
(define (set-length set) (table-length set))
(define (set-empty? set) (= (set-length set) 0))
(define (set-for-each f set) (table-for-each (lambda (k _) (f k)) set))
(define (set-search f set) (table-search (lambda (k _) (and (f k) k)) set))
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
(define (edge-exists? tree from to)
  (or (parent? tree to from) (friend? tree from to)))

(define (children-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-children tree) x)))
(define (friends-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-friends tree) x)))
(define (neighbors-for-each f tree x)
  (friends-for-each f tree x)
  (children-for-each f tree x))
(define (friendlies-for-each f tree x)
  (set-for-each f (table-ref-or-set-default! (BFSTree-friendlies tree) x)))
(define (friendlies-search f tree x)
  (set-search f (table-ref-or-set-default! (BFSTree-friendlies tree) x)))
(define (friendlies->list tree x)
  (let ((friendlies (table-ref (BFSTree-friendlies tree) x #f)))
    (if friendlies
        (set->list friendlies)
        '())))
    
(define (source? tree x)
  (= (BFSTree-source tree) x))
(define (parent? tree x p)
  (eq? p (get-parent tree x)))
(define (friend? tree x f)
  (set-contains? (table-ref-or-set-default! (BFSTree-friends tree) x) f))

(define (add-edge! tree from to #!key onconnect)
  (define queue (make-queue))

  (define (hoist hoister node)
    (when (dirty-edge? tree hoister node)
      (set-parent! tree node hoister)
      (if (and onconnect (= (get-rank tree node) infinity)) (onconnect node))
      (update-rank! tree node)
      (neighbors-for-each
        (lambda (n)
          (queue-put! queue node)
          (queue-put! queue n))
        tree
        node)))

  (when (not (edge-exists? tree from to)) ;; no duplicate edges
    (add-friend! tree from to)
    (hoist from to)
    (do () ((queue-empty? queue))
      (hoist (queue-get! queue) (queue-get! queue)))))

(define (remove-edge! tree from to #!key ondisconnect)
  (cond
    ((not (parent? tree to from)) ;; edge not in BFS, can be removed safely
      (remove-friend! tree from to))
    (else
      (remove-parent-edge! tree to ondisconnect: ondisconnect))))

(define (remove-parent-edge! tree to #!key ondisconnect)
  (define loose-queue (make-queue))
  (define catch-queue (make-queue))
  (define loose-set (make-set))
  (define anchor-table (make-table))
  (define disconnected (make-set))

  (define (loosen! node)
    (let* ((rank (get-rank tree node))
           (bucket (table-ref anchor-table rank #f)))
      (when bucket
        (set-remove! bucket node)
        (if (set-empty? bucket) (table-set! anchor-table rank)))
      (set-add! disconnected node)
      (set-rank! tree node infinity)))
  (define (loose? node) (= (get-rank tree node) infinity))

  (define (anchor! node)
    (let* ((rank (get-rank tree node))
           (bucket (table-ref-or-set-default! anchor-table rank)))
      (set-add! bucket node)))
  (define (anchored? node)
    (let* ((rank (get-rank tree node))
           (bucket (table-ref anchor-table rank #f)))
      (and bucket (set-contains? bucket node))))

  (define (drop to)
    (define drop-queue (make-queue))

    (queue-put! drop-queue to)
    (queue-put! drop-queue (get-rank tree (get-parent tree to)))

    (remove-parent! tree to)

    (do () ((queue-empty? drop-queue))
      (let* ((node (queue-get! drop-queue))
             (parent-rank (queue-get! drop-queue))
             (adopter
               (friendlies-search
                   (lambda (f) (= (get-rank tree f) parent-rank))
                   tree
                   node)))
        (if adopter
          ;; preemptively choose a safe parent
          ;; since we are doing a BFS for possibly loose nodes, a friendly
          ;; with the same rank as parent cannot be loose
          (set-parent! tree node adopter)
          (let ((rank (get-rank tree node)))
            (loosen! node)

            ;; DFS across subtree to find loose nodes
            (children-for-each
              (lambda (child)
                (queue-put! drop-queue child)
                (queue-put! drop-queue rank))
              tree
              node)
            (friendlies-for-each
              (lambda (friendly)
                (if (not (loose? friendly)) (anchor! friendly)))
              tree
              node))))))

  (define (catch node)
    (neighbors-for-each
      (lambda (neighbor)
        (when (loose? neighbor)
          (set-parent! tree neighbor node)
          (set-remove! disconnected neighbor)
          (update-rank! tree neighbor)
          (queue-put! catch-queue neighbor)))
      tree
      node))

  (drop to)

  (let* ((cmp (lambda (x y) (< (car x) (car y))))
         (buckets (list-sort cmp (table->list anchor-table))))
    (for-each
      (lambda (bucket)
        (let ((rank (car bucket))
              (head (queue-peek catch-queue)))
          (do ((next head (queue-peek catch-queue)))
              ((or (not next) (> (get-rank tree next) rank)))
              (catch (queue-get! catch-queue))))
        (set-for-each catch (cdr bucket)))
      buckets)
    ;; all buckets caught, catch rest of the queue
    (do () ((queue-empty? catch-queue))
      (catch (queue-get! catch-queue)))
    (if ondisconnect (set-for-each ondisconnect disconnected))))

(define (redirect! tree node other #!key onconnect ondisconnect)
  ;; remove all incoming edges to node and redirect them toward other
  ;; if there is an edge from node to node itself, it is not redirected
  (let ((parent (get-parent tree node))
        (friendlies (friendlies->list tree node))) ;; ensure not to iterate and mutate friendlies simultaneously
    ;; cannot change rank since parent was equal or higher rank
    (for-each (lambda (f) (when (not (= f node)) (remove-friend! tree f node))) friendlies)
    ;; cut last edge holding the node, changes rank if connected
    (if parent (remove-parent-edge! tree node ondisconnect: ondisconnect)) 
    ;; may change rank
    (if parent (add-edge! tree parent other onconnect: onconnect))
    ;; cannot change rank since parent was equal or higher rank
    (for-each (lambda (f) (when (not (= f node)) (add-friend! tree f other))) friendlies)))

(define (connected? tree node)
  (not (= (get-rank tree node) infinity)))

;; tests

(define (make-test-graph source)
  (list->table (list (cons source '()) (cons 'source source))))
(define (test-graph-edges-for-each f graph)
  (table-for-each
    (lambda (from tos)
      (if (not (eq? from 'source)) 
          (for-each (lambda (to) (f from to)) tos))) graph))
(define (test-graph-add! graph from to)
  (table-set! graph from (cons to (table-ref graph from '()))))
(define (test-graph-remove! graph from to)
  (table-set! graph from (filter (lambda (x) (not (= x to))) (table-ref graph from '()))))
(define (test-graph-redirect! graph node other)
  (define incoming '())
  (test-graph-edges-for-each
    (lambda (from to) (if (eq? to node) (set! incoming (cons from incoming))))
    graph)
  (set! incoming (filter (lambda (f) (not (= f node))) incoming)) ;; remove self redirect
  (for-each
    (lambda (friendly) (test-graph-remove! graph friendly node))
    incoming)
  (for-each
    (lambda (friendly) (test-graph-add! graph friendly other))
    incoming))
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
(define replace!  (make-parameter #f))
(define rank-of    (make-parameter #f))

(define (get-test-expected-result test . args)
  (parameterize ((make-graph make-test-graph)
                 (add! test-graph-add!)
                 (delete! test-graph-remove!)
                 (replace! test-graph-redirect!)
                 (rank-of test-graph-rank))
    (apply test args)))

(define (run test . args)
  (parameterize ((make-graph make-BFSTree)
                 (add! add-edge!)
                 (delete! remove-edge!)
                 (replace! redirect!)
                 (rank-of get-rank))
    (apply test args)))

(define (interpret-test instructions N)
  (define graph ((make-graph) 0))
  (for-each (lambda (instr) ((eval instr) graph)) instructions)
  (map (lambda (n) ((rank-of) graph n)) (iota N)))

(define fuzzy-test-N 20)
(define (run-one-fuzzy-test #!key (debug #f))
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

  (let* ((instructions (random-instructions 40 (+ 1 (random-integer 10))))
         (_ (when debug (pp 'INSTRUCTIONS:) (for-each pp (map lift-instruction instructions))))
         (expected-result (get-test-expected-result interpret-test instructions fuzzy-test-N))
         (result (run interpret-test instructions fuzzy-test-N)))
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

(define (fuzzy-test n #!key (debug #f))
  (let loop ((i 0))
    (when (< i n)
      (if (run-one-fuzzy-test debug: debug) (loop (+ i 1))))))

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
  (map (lambda (n) ((rank-of) graph n)) (iota 4)))

(define (test4)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 1 2)
  ((add!) graph 2 1)
  ((delete!) graph 0 1)
  (map (lambda (n) ((rank-of) graph n)) (iota 6)))

(define (test5)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 1 2)
  ((add!) graph 1 3)
  ((add!) graph 2 4)
  ((add!) graph 3 5)
  ((add!) graph 5 4)
  ((add!) graph 6 4)
  ((delete!) graph 2 4)
  (map (lambda (n) ((rank-of) graph n)) (iota 7)))

(define (test6)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 1 2)
  ((add!) graph 1 3)
  ((add!) graph 2 4)
  ((add!) graph 3 5)
  ((add!) graph 4 6)
  ((add!) graph 5 4)
  ((add!) graph 6 7)
  ((delete!) graph 2 4)
  (map (lambda (n) ((rank-of) graph n)) (iota 8)))

(define (test7)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 1 2)
  ((add!) graph 2 3)
  ((add!) graph 2 3)
  ((delete!) graph 2 3)
  (map (lambda (n) ((rank-of) graph n)) (iota 4)))

(define (test8)
  (define graph ((make-graph) -1))
  ((add!) graph -1 0)
  ((add!) graph 0 1)
  ((add!) graph 1 2)
  ((add!) graph 1 2)
  ((delete!) graph 1 2)
  (map (lambda (n) ((rank-of) graph n)) (iota 4 -1)))

(define (test9)
  (define result1 #f)
  (define result2 #f)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 0 6)
  ((add!) graph 1 2)
  ((add!) graph 1 3)
  ((add!) graph 2 4)
  ((add!) graph 3 4)
  ((add!) graph 4 5)
  ((add!) graph 6 2)
  ((add!) graph 6 7)
  ((add!) graph 7 3)
  ((delete!) graph 0 1)
  (set! result1 (map (lambda (n) ((rank-of) graph n)) (iota 8)))
  ((add!) graph 0 1)
  (set! result2 (map (lambda (n) ((rank-of) graph n)) (iota 8)))
  (list result1 result2))

(define (test10)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 0 2)
  ((add!) graph 0 3)
  ((add!) graph 0 4)
  ((add!) graph 1 5)
  ((add!) graph 2 5)
  ((add!) graph 3 5)
  ((add!) graph 4 5)
  ((add!) graph 5 6)
  ((add!) graph 6 7)
  ((add!) graph 7 8)
  ((replace!) graph 5 8)
  (map (lambda (n) ((rank-of) graph n)) (iota 9)))

(define (test11)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 0 2)
  ((add!) graph 0 3)
  ((add!) graph 0 4)
  ((add!) graph 1 5)
  ((add!) graph 2 5)
  ((add!) graph 3 5)
  ((add!) graph 4 5)
  ((add!) graph 5 6)
  ((add!) graph 6 7)
  ((add!) graph 7 8)
  ((add!) graph 5 5)
  ((replace!) graph 5 8)
  (map (lambda (n) ((rank-of) graph n)) (iota 9)))

(define (test12)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 0 2)
  ((add!) graph 0 3)
  ((add!) graph 0 4)
  ((add!) graph 1 5)
  ((add!) graph 2 5)
  ((add!) graph 3 5)
  ((add!) graph 4 5)
  ((add!) graph 5 6)
  ((add!) graph 6 7)
  ((add!) graph 7 8)
  ((add!) graph 5 5)
  ((add!) graph 8 8)
  ((add!) graph 8 5)
  ((replace!) graph 5 8)
  (map (lambda (n) ((rank-of) graph n)) (iota 9)))

(define (test13)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 0 2)
  ((add!) graph 0 3)
  ((add!) graph 0 4)
  ((add!) graph 1 5)
  ((add!) graph 2 5)
  ((add!) graph 3 5)
  ((add!) graph 4 5)
  ((replace!) graph 5 6)
  (map (lambda (n) ((rank-of) graph n)) (iota 7)))

(define (test14)
  (define graph ((make-graph) 0))
  ((add!) graph 0 1)
  ((add!) graph 0 2)
  ((add!) graph 0 3)
  ((add!) graph 0 4)
  ((add!) graph 1 5)
  ((add!) graph 2 5)
  ((add!) graph 3 5)
  ((add!) graph 4 5)
  ((replace!) graph 5 0)
  (map (lambda (n) ((rank-of) graph n)) (iota 6)))

(define (run-all . tests)
  (for-each
    (lambda (test-args)
      (let* ((test (car test-args))
             (args (cdr test-args))
             (expected (apply get-test-expected-result test args))
             (result (apply run test args)))
        (if (equal? result expected)
            (pp (list test 'OK))
            (begin
              (pp (list test 'FAILED))
              (pp (list 'EXPECT: expected))
              (pp (list 'OUTPUT: result))))))
    tests))

(define (find-minimal-example init-instructions N)
  (define (lambdaify instr) (list 'lambda '(graph) instr))
  (define (delambdaify instr) (caddr instr))
  (define lambdaified (map lambdaify init-instructions))
  (let loop ((instructions lambdaified)
             (minimal lambdaified))
    (if (null? instructions)
      (let ((delambdaified (map delambdaify minimal)))
        (if (equal? delambdaified init-instructions)
          (begin
            (pp (list 'MINIMAL-EXAMPLE:))
            (for-each pp delambdaified))
          (find-minimal-example delambdaified N)))
      (let ((without (filter (lambda (i) (not (eq? i (car instructions)))) minimal)))
        (if (equal?
              (run interpret-test without N)
              (get-test-expected-result interpret-test without N))
          (loop (cdr instructions) minimal)
          (loop (cdr instructions) without))))))

(fuzzy-test 10000 debug: #f)
(run-all
  (list test1)
  (list test2)
  (list test3)
  (list test4)
  (list test5)
  (list test6)
  (list test7)
  (list test8)
  (list test9)
  (list test10)
  (list test11)
  (list test12)
  (list test13)
  (list test14))
