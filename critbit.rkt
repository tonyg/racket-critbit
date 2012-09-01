#lang racket/base
;; Crit-Bit trees
;; http://cr.yp.to/critbit.html
;; https://github.com/agl/critbit/

(struct critbit-node (common-bits zero one) #:transparent)

(define (empty)
  '())

(define (empty? tree)
  (null? tree))

(define (internal-insert bit key tree)
  (cond
   [(empty? tree)
    key]
   [(bytes? tree)
    (define-values (common-bits relationship) (relationship bit key tree))
    (case relationship
      ((lt) (critbit-node common-bits key tree))
      ((eq) tree)
      ((gt) (critbit-node common-bits tree key)))]
   [(critbit-node? tree)
    