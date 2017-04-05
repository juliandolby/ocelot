#lang rosette

(require "../lang/bounds.rkt" "../lang/universe.rkt"
	 "matrix.rkt" "helpers.rkt"
         (only-in "../lang/ast.rkt" relation-arity)
         (prefix-in $ racket))
(provide (all-defined-out))

; An interpretation is a universe and an association list of (relation, matrix)
; pairs
(struct interpretation (universe entries) #:transparent)

; receives an ast/node/relation and an uninterpreted bound

; Create an interpretation of the given bounds
(define (instantiate-bounds bounds)
  (define U (bounds-universe bounds))
  (interpretation
    U
    (for/list ([bnd (bounds-entries bounds)])
      (define rel (bound-relation bnd))
      (define size (expt (universe-size U) (relation-arity rel)))
      (define mat
        (cond [(equal? (bound-lower bnd) (bound-upper bnd))
               (define members ($map (curry tuple->idx U) (bound-upper bnd)))
               (matrix (for/list ([i size]) (set-member? members i)))]
              [else
               (define lower ($map (curry tuple->idx U) (bound-lower bnd)))
               (define upper ($map (curry tuple->idx U) (bound-upper bnd)))
               (matrix (for/list ([i size])
                           (cond [(set-member? lower i) #t]
                                 [(set-member? upper i) (define-symbolic* r boolean?) r]
                                 [else #f])))]))
      (cons rel mat))))

(define (interpretation-union . interps)
  (define U (interpretation-universe (first interps)))
  (interpretation U (for*/list ([i interps][e (interpretation-entries i)]) e)))

(define (interpretation->relations interp [model #f])
  (match-define (interpretation U entries) interp)
  (for/hash ([pair entries])
    (match-define (cons rel mat) pair)
    (define contents (matrix-entries mat))
    (define arity (matrix-arity U contents))
    (values rel (for/list ([(x i) (in-indexed contents)] #:when x)
			  (map (lambda (x)
				 (if (and model (symbolic? x))
				     (evaluate x model)
				     x))
			       (idx->tuple U arity i))))))
