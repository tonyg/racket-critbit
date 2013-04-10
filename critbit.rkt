#lang typed/racket/base
;; Immutable Crit-Bit trees
;; http://cr.yp.to/critbit.html
;; https://github.com/agl/critbit/

;; TODO: clever bitmask representation of critbit position

(require racket/match)
(require racket/generator)

;; A CritBit tree is a (critbit-tree (Option Node)).
(struct: critbit-tree ([root : (Option Node)]) #:transparent)
(define-type Tree critbit-tree)

(define-type TIndex Exact-Nonnegative-Integer)

;; A Node is either
;; -- a Bytes, a leaf node
;; -- a (node NonNegativeInteger Node Node)
;;
;; INVARIANT: All descendants of a node with index i have the same
;; i-bit prefix.
;;
(struct: node ([index : TIndex] [zero : Node] [one : Node]) #:transparent)
(define-type Node (U Bytes node))

(: empty : -> Tree)
(define empty
  (let ((t (critbit-tree #f)))
    (lambda () t)))

(: empty? : Tree -> Boolean)
(define (empty? tree)
  (not (critbit-tree-root tree)))

(: contains? : Tree Bytes -> Boolean)
(define (contains? tree key)
  (define root (critbit-tree-root tree))
  (if (not root)
      #f
      (let walk ((n root))
	(match n
	  [(? bytes? leaf)
	   (infinite-bytes=? leaf key)]
	  [(node index zero one)
	   (walk (if (bit-ref key index) one zero))]))))

(: infinite-bytes-ref : Bytes TIndex -> Byte)
(define (infinite-bytes-ref bs n)
  (if (>= n (bytes-length bs))
      0 ;; treat byte-strings as followed by an infinite suffix of zeroes
      (bytes-ref bs n)))

(: infinite-bytes=? : Bytes Bytes -> Boolean)
(define (infinite-bytes=? a b)
  (define limit (max (bytes-length a) (bytes-length b)))
  (let: check ((i : TIndex 0))
    (cond
     [(= i limit) #t]
     [(= (infinite-bytes-ref a i) (infinite-bytes-ref b i)) (check (+ i 1))]
     [else #f])))

;; Bits are numbered thus:
;; |----------------|----------------|----------------|---...
;;   0 1 2 3 4 5 6 7  8 9101112131415 1617181920212223 24 ...
;;
(: bit-ref : Bytes TIndex -> Boolean)
(define (bit-ref bs n)
  (define byte-index (quotient n 8))
  (define bit-index (- 7 (remainder n 8)))
  (bitwise-bit-set? (infinite-bytes-ref bs byte-index) bit-index))

(: insert : Tree Bytes -> Tree)
(define (insert tree key)
  (: splice-key : TIndex Node -> node)
  (define (splice-key prefix-length sibling)
    (if (bit-ref key prefix-length)
	(node prefix-length sibling key)
	(node prefix-length key sibling)))
  (: walk : Node -> (U TIndex Node))
  (define (walk n)
    (match n
      [(? bytes? leaf)
       (join leaf key)]
      [(node index zero one)
       (: maybe-splice : Node (Node -> Node) -> (U TIndex Node))
       (define (maybe-splice child stitch)
	 (define new (walk child))
	 (if (exact-nonnegative-integer? new)
	     (if (< new index) new (stitch (splice-key new child)))
	     (if (eq? child new) n (stitch new))))
       (if (bit-ref key index)
	   (maybe-splice one (lambda (new) (node index zero new)))
	   (maybe-splice zero (lambda (new) (node index new one))))]))
  (: root : (Option Node))
  (define root (critbit-tree-root tree))
  (critbit-tree
   (if (not root)
       key
       (let ((new (walk root)))
	 (if (exact-nonnegative-integer? new)
	     (splice-key new root)
	     new)))))

(: join : Bytes Bytes -> (U TIndex Bytes))
(define (join leaf key)
  (define limit (max (bytes-length leaf) (bytes-length key)))
  (let: find-differing-byte ((i : TIndex 0))
    (if (= i limit)
	leaf ;; they're the same (infinite zeros on the end!) byte string
	(let ((delta (bitwise-xor (infinite-bytes-ref leaf i) (infinite-bytes-ref key i))))
	  (if (zero? delta)
	      (find-differing-byte (+ i 1))
	      (let* ((bit (- 8 (integer-length delta))) ;; 0th bit is high
		     (index (+ (* i 8) bit)))
		(if (< index 0)
		    (error 'join "Internal error: should never happen")
		    ;; ^ this is here just to satisfy TR
		    index)))))))

(: delete : Tree Bytes -> Tree)
(define (delete tree key)
  (define root (critbit-tree-root tree))
  (if (not root)
      tree
      (critbit-tree
       (let walk ((n root))
	 (match n
	   [(? bytes? leaf)
	    (if (infinite-bytes=? leaf key)
		#f
		leaf)]
	   [(node index zero one)
	    (if (bit-ref key index)
		(let ((new (walk one)))
		  (if new (node index zero new) zero))
		(let ((new (walk zero)))
		  (if new (node index new one) one)))])))))

(: seq->tree : (Sequenceof Bytes) -> Tree)
(define (seq->tree xs)
  (for/fold ([tree (empty)]) ([x xs]) (insert tree x)))

(: tree->list : Tree -> (Listof Bytes))
(define (tree->list tree)
  (define root (critbit-tree-root tree))
  (if (not root)
      '()
      (let: walk ((n : Node root) (acc : (Listof Bytes) '()))
	(match n
	  [(? bytes? leaf) (cons leaf acc)]
	  [(node _ zero one) (walk zero (walk one acc))]))))

;; (define (in-tree tree)
;;   (if (empty? tree)
;;	 '()
;;	 (in-generator
;;	  (let walk ((n (critbit-tree-root tree)))
;;	 (match n
;;	   [(? bytes? leaf) (yield leaf)]
;;	   [(node _ zero one) (begin (walk zero) (walk one))])))))

;; (require racket/trace)
;; (trace delete)

(module+ main
  (require (except-in racket empty ->))

  (: i->b : Integer -> Bytes)
  (define (i->b i) (integer->integer-bytes i 4 #t #t))

  (: b->i : Bytes -> Integer)
  (define (b->i bs) (integer-bytes->integer bs #t #t))

  (: iota : Integer -> (Listof Bytes))
  (define (iota n) (for/list: : (Listof Bytes) ([i : Integer (in-range n)]) (i->b i)))

  (: max-count : Integer)
  (define max-count 500000)

  (: repeat : (All (A) Integer (-> A) -> A))
  (define (repeat n thunk)
    (cond
     [(zero? n) (error 'repeat "Zero n")]
     [(= n 1) (time (thunk))]
     [else (time (thunk)) (repeat (- n 1) thunk)]))

  (seq->tree (list #"abc" #"abd" #"abe" #"aaa" #"zzz"))
  (seq->tree (reverse (list #"abc" #"abd" #"abe" #"aaa" #"zzz")))
  (seq->tree (list (bytes 0) (bytes 0 0 0 0)))

  (seq->tree (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor"))
  (seq->tree (reverse (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor")))
  (seq->tree (shuffle (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor")))
  (seq->tree (shuffle (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor")))
  (seq->tree (shuffle (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor")))

  (map b->i (tree->list (seq->tree (shuffle (iota 10)))))

  ;; (for ([x (in-tree (seq->tree (shuffle (iota 10))))])
  ;;   (printf "~v\n" x))

  (printf "Enumeration (baseline)\n")
  (void (repeat 3 (lambda () (for: ([i : Integer (in-range max-count)]) (i->b i)))))

  (printf "Critbit - insertion\n")
  (define full-c
    (repeat 3 (lambda ()
		(for/fold: ([t : Tree (empty)]) ([i (in-range max-count)])
		  (insert t (i->b i))))))

  (printf "Set - insertion\n")
  (define full-s
    (repeat 3 (lambda ()
		(for/fold: ([t : (Setof Bytes) (set)]) ([i (in-range max-count)])
		  (set-add t (i->b i))))))

  (printf "Critbit - removal\n")
  (void (repeat 3 (lambda ()
		    (for/fold: ([t : Tree full-c]) ([i (in-range max-count)])
		      (delete t (i->b i))))))

  (printf "Set - removal\n")
  (void (repeat 3 (lambda ()
		    (for/fold: ([t : (Setof Bytes) full-s]) ([i (in-range max-count)])
		      (set-remove t (i->b i))))))

  (printf "Critbit - positive membership\n")
  (repeat 3 (lambda ()
	      (for: ([i : Integer (in-range max-count)])
		(when (not (contains? full-c (i->b i)))
		  (error 'critbit "Membership problem")))))

  (printf "Set - positive membership\n")
  (repeat 3 (lambda ()
	      (for: ([i : Integer (in-range max-count)])
		(when (not (set-member? full-s (i->b i)))
		  (error 'set "Membership problem")))))

  (printf "Critbit - negative membership\n")
  (repeat 3 (lambda ()
	      (for: ([i : Integer (in-range max-count (* 2 max-count))])
		(when (contains? full-c (i->b i))
		  (error 'critbit "Membership problem")))))

  (printf "Set - negative membership\n")
  (repeat 3 (lambda ()
	      (for: ([i : Integer (in-range max-count (* 2 max-count))])
		(when (set-member? full-s (i->b i))
		  (error 'set "Membership problem")))))

  (map b->i (tree->list (for/fold: ([t : Tree (seq->tree (iota 10))])
			    ([k (shuffle (iota 5))])
			  (delete t k)))))
