#lang racket/base
;; Immutable Crit-Bit trees
;; http://cr.yp.to/critbit.html
;; https://github.com/agl/critbit/

;; TODO: clever bitmask representation of critbit position

(require racket/match)
(require racket/generator)

;; A CritBit tree is a (critbit-tree (Option Node)).
(struct critbit-tree (root) #:transparent)

;; A Node is either
;; -- a Bytes, a leaf node
;; -- a (node NonNegativeInteger Node Node)
;;
;; INVARIANT: All descendants of a node with index i have the same
;; i-bit prefix.
;;
(struct node (index zero one) #:transparent)

(define empty
  (let ((t (critbit-tree #f)))
    (lambda () t)))

(define (empty? tree)
  (not (critbit-tree-root tree)))

(define (contains? tree key)
  (if (empty? tree)
      #f
      (let walk ((tree tree))
	(match tree
	  [(? bytes? leaf)
	   (infinite-bytes=? leaf key)]
	  [(node index zero one)
	   (walk (if (bit-ref key index) one zero))]))))

(define (infinite-bytes-ref bs n)
  (if (>= n (bytes-length bs))
      0 ;; treat byte-strings as followed by an infinite suffix of zeroes
      (bytes-ref bs n)))

(define (infinite-bytes=? a b)
  (define limit (max (bytes-length a) (bytes-length b)))
  (let check ((i 0))
    (cond
     [(= i limit) #t]
     [(= (infinite-bytes-ref a i) (infinite-bytes-ref b i)) (check (+ i 1))]
     [else #f])))

;; Bits are numbered thus:
;; |----------------|----------------|----------------|---...
;;   0 1 2 3 4 5 6 7  8 9101112131415 1617181920212223 24 ...
;;
(define (bit-ref bs n)
  (define byte-index (quotient n 8))
  (define bit-index (- 7 (remainder n 8)))
  (bitwise-bit-set? (infinite-bytes-ref bs byte-index) bit-index))

(define (insert tree key)
  (define (splice-key prefix-length sibling)
    (if (bit-ref key prefix-length)
	(node prefix-length sibling key)
	(node prefix-length key sibling)))
  (define (walk n)
    (match n
      [(? bytes? leaf)
       (join leaf key)]
      [(node index zero one)
       (define (maybe-splice child stitch)
	 (match (walk child)
	   [(? integer? prefix-length)
	    (if (< prefix-length index) prefix-length (stitch (splice-key prefix-length child)))]
	   [new
	    (if (eq? child new)
		n
		(stitch new))]))
       (if (bit-ref key index)
	   (maybe-splice one (lambda (new) (node index zero new)))
	   (maybe-splice zero (lambda (new) (node index new one))))]))
  (critbit-tree
   (if (empty? tree)
       key
       (let ((root (critbit-tree-root tree)))
	 (match (walk root)
	   [(? integer? prefix-length) (splice-key prefix-length root)]
	   [ans ans])))))

(define (join leaf key)
  (define limit (max (bytes-length leaf) (bytes-length key)))
  (let find-differing-byte ((i 0))
    (if (= i limit)
	leaf ;; they're the same (infinite zeros on the end!) byte string
	(let ((delta (bitwise-xor (infinite-bytes-ref leaf i) (infinite-bytes-ref key i))))
	  (if (zero? delta)
	      (find-differing-byte (+ i 1))
	      (let* ((bit (- 8 (integer-length delta))) ;; 0th bit is high
		     (index (+ (* i 8) bit)))
		index))))))

(define (delete tree key)
  (if (empty? tree)
      tree
      (critbit-tree
       (let walk ((n (critbit-tree-root tree)))
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

(define (seq->tree xs)
  (for/fold ([tree (empty)]) ([x xs]) (insert tree x)))

(define (tree->list tree)
  (if (empty? tree)
      '()
      (let walk ((n (critbit-tree-root tree)) (acc '()))
	(match n
	  [(? bytes? leaf) (cons leaf acc)]
	  [(node _ zero one) (walk zero (walk one acc))]))))

(define (in-tree tree)
  (if (empty? tree)
      '()
      (in-generator
       (let walk ((n (critbit-tree-root tree)))
	 (match n
	   [(? bytes? leaf) (yield leaf)]
	   [(node _ zero one) (begin (walk zero) (walk one))])))))

;; (require racket/trace)
;; (trace delete)

(module+ main
  (require racket)

  (seq->tree (list #"abc" #"abd" #"abe" #"aaa" #"zzz"))
  (seq->tree (reverse (list #"abc" #"abd" #"abe" #"aaa" #"zzz")))
  (seq->tree (list (bytes 0) (bytes 0 0 0 0)))

  (seq->tree (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor"))
  (seq->tree (reverse (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor")))
  (seq->tree (shuffle (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor")))
  (seq->tree (shuffle (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor")))
  (seq->tree (shuffle (list #"Alice" #"Bob" #"Eve" #"Mallory" #"Trevor")))

  (define (iota n) (for/list ([i n]) (integer->integer-bytes i 4 #t #t)))
  (define (b->i bs) (integer-bytes->integer bs #t #t))

  (map b->i (tree->list (seq->tree (shuffle (iota 10)))))

  (for ([x (in-tree (seq->tree (shuffle (iota 10))))])
    (printf "~v~n" x))

  (map b->i (tree->list (for/fold ([t (seq->tree (iota 10))])
			    ([k (shuffle (iota 5))])
			  (delete t k)))))
