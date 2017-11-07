(require "sparql-sketch.rkt")

(define-symbolic* i1 i2 i3 i4 i5 i6 i7 integer?)

(define sintegers (list i1 i2 i3 i4 i5 i6 i7))

; comparison operators
(define (comp-eq i) (= i i2))
(define (comp-le i) (<= i i3))
(define (comp-l i) (< i i4))
(define (comp-ge i) (>= i i5))
(define (comp-g i) (> i i6))
(define (comp-uneq i) (not (= i i7)))

;create simple numeric expression
(define (numeric pred v)
(and (string? v) (pred (string-length v))))

(define (strlen s)
(apply-predicate (lambda (v) (if (string? v) (string-length v) -1)) s))

(define (assert-max svalues max) (map (lambda (i) (assert (<= i (+ max 1)))) svalues))

(define (litlen-max model) (apply max (map (lambda (t) (string-length (car t)))
                                  (hash-ref (interpretation->relations (evaluate ib model) model) literals))))

(define (printeval model svalues) (println (map (lambda (i) (evaluate i model)) svalues)))

(define (iop i) (and ([choose > = <] i i1) (< 0 i1)))

(define (strlen-comp s) (and (string? s) ([choose comp-eq comp-le comp-l comp-ge comp-g] (string-length s))))

(define (strlen-comp-union s) (and (string? s)
                                   (or ([choose comp-eq comp-le comp-l comp-ge comp-g] (string-length s))
                                   ([choose comp-eq comp-le comp-l comp-ge comp-g] (string-length s)))))

(define-syntax ppx
  (syntax-rules ()
    ((_ (pred) from to)
     (triple from pred to))
    ((_ (pred1 pred2 ...) from to)
     (let ((s (gensym)))
       (some ([s entities])
	     (and
	      (triple from pred1 s)
	      (ppx (pred2 ...) s to)))))))


;and/or are considered to be binary currently
(define-synthax (filter-it i depth)
#:base (numeric [choose comp-eq comp-le comp-l comp-ge comp-g comp-uneq] i)
#:else (choose
        (numeric [choose comp-eq comp-le comp-l comp-ge comp-g comp-uneq] i)
        (and (filter-it i (- depth 1)) (filter-it i (- depth 1)))
        (or (filter-it i (- depth 1)) (filter-it i (- depth 1)))))
     
; The body of filter-bounded is a hole to be filled with an
; expression of depth (up to) 1 from the filter grammar.
(define (boundedfilter i)
  (filter-it i 1))

(define (andf x y) (and x y))

(define (orf x y) (or x y))

(define (bound x)
([choose andf orf]
 ([choose < = >] x (?? integer?))
 ([choose < = >] x (?? integer?))))

(define uri5-rel (hash-ref atom-relations 'uri5))

(define (is-true-prefix x y) (and (not (equal? x y)) (string-prefix? y x)))

;and/or are considered to be binary currently
(define-synthax (strfilter-it s1 s2 depth)
#:base ([choose is-true-prefix equal?] s1 s2)
#:else (choose
      ([choose is-true-prefix equal?] s1 s2)
      (and (strfilter-it s1 s2 (- depth 1)) (strfilter-it s1 s2 (- depth 1)))
      (or (strfilter-it s1 s2 (- depth 1)) (strfilter-it s1 s2 (- depth 1)))))


(define (boundedstrfilter s1 s2)
(strfilter-it s1 s2 1))

(define-symbolic* l string?)
(assert (member l all-atoms))

;(define (choose-atom s p v)
;  ([choose* s p v l 'uri1 'uri2 'uri3 'uri4 'uri5 'uri6 'uri7 'uri8 'uri9]))

(define-syntax optional2
(syntax-rules ()
  ((_ (v1 ...) x)
   (let* ((null-rel (hash-ref atom-relations 'Null)))
      (or x
              (and 
               (and (in v1 null-rel) ...)
               (no  [(v1 atoms) ...]
                   x)))))))

(define-synthax (joins s p v depth)
#:base (triple [choose s p v] [choose s p v] [choose s p v])
#:else (choose
        (triple [choose s p v] [choose s p v] [choose s p v])
        (and (joins s p v (- depth 1)) (joins s p v (- depth 1)))
        (and (joins s p v (- depth 1))
             (apply-predicate (lambda (x) (and (string? x) (bound (string-length x)))) [choose s p v]))))

(define-synthax (joins2 s v depth)
  #:base (triple s _ v)
  #:else
  (choose (triple s _ v)
          (some ([x atoms])
                (and
                 (triple s _ x)
                 (triple x _ v)))))

(define-synthax (joins3 s v depth)
  #:base (triple s _ v)
  #:else
  (choose (triple s _ v)
          (some ([x atoms])
                (optional (s)
                 (triple x _ v)
                 (triple s _ x)))))

(define-synthax (joins4 s v depth)
  #:base (triple s _ v)
  #:else
  (choose (triple s _ v)
          (some ([x atoms])
                (and
                 (joins4 s x (- depth 1))
                 (joins4 x v (- depth 1))))
          (some ([x atoms])
                (optional (s)
                 (joins4 x v (- depth 1))
                 (joins4 s x (- depth 1))))))
