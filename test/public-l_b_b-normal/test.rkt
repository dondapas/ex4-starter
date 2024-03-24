#lang racket

(require "../../e4.rkt")

(define term
  '(lambda (q)
     ((lambda (id) ((lambda (x) x) id))
      ((lambda (y) y) (lambda (z) z)))))

(with-output-to-file "output"
                     (lambda ()
                       (print (collect-evaluation-trace normal-order-reduce term)))
                     #:exists 'replace)
