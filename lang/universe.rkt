#lang rosette

(require (prefix-in $ racket))
(provide (except-out (all-defined-out) universe)
         (rename-out [make-universe universe]))


;; universe --------------------------------------------------------------------

(struct universe (atoms inverse values) #:transparent)
(define (make-universe atoms)
  (let ([inverse (for/hash ([(a i) (in-indexed atoms)]) (values (car a) i))]
	[values (for/hash ([a atoms]) (values (car a) (cadr a)))])
    (universe
     (map car atoms)
     (lambda (t) (hash-ref inverse t))
     (lambda (a) (hash-ref values a)))))
(define (universe-size universe)
  (length (universe-atoms universe)))
