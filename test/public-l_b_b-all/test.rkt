#lang racket

(require "../../e4.rkt")

(define term0
  '(((lambda (x) (lambda (y) ((lambda (z) (x z)) y))) (lambda (a) a)) ((lambda (b) b) (lambda (c) c))))

(with-output-to-file "output"
  (lambda ()
    (print
     (append
      '(term0-CBV)
      (collect-evaluation-trace CBV-order-reduce term0)
      '(term0-CBN)
      (collect-evaluation-trace CBN-order-reduce term0)
      '(term0-app)
      (collect-evaluation-trace applicative-order-reduce term0)
      '(term0-normal)
      (collect-evaluation-trace normal-order-reduce term0))))
  #:exists 'replace)
