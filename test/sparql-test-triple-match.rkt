#lang rosette

(define _ '_)

(current-bitwidth #f)

(define all-subjects '(x))
(define all-properties '(p))
(define all-objects '(v1 v2))

(define all-entities (append all-subjects all-objects (list 'Null)))
(define all-atoms (append all-entities all-properties))

(require ocelot)
(require rosette/lib/synthax)
(require rosette/lib/angelic)
(require ocelot/engine/symmetry)

(define U (universe all-atoms))

(define data-01 (declare-relation 3 "data-01"))

(define data-01-bound
(make-exact-bound
 data-01
 '((x p v1)
   (x p v2))))

(define triples (declare-relation 3 "triples"))
(define triples-bound
  (make-exact-bound triples ;= data-01-bound, currently data-01-bound is not used 
 '((x p v1)
   (x p v2))))

;assume order of bindings is according to variable occurrence in the query

(define result-tp-01 (declare-relation 2 "result-tp-01"))

(define result-tp-01-bound
  (make-exact-bound
   result-tp-01
   '((p v1)
     (p v2))))

(define result-tp-02 (declare-relation 2 "result-tp-02"))

(define result-tp-02-bound
  (make-exact-bound
   result-tp-02
   '((x v1)
     (x v2))))



;(define no-triples (declare-relation 3 "NoTriples"))
;
;(define no-triples-bound
;(make-exact-bound
; no-triples
; '((uri2 uri5 "Jonathon")
;   (uri3 uri5 "Allison"))))

(define subjects (declare-relation 1 "subjects"))

(define subjects-bound (make-exact-bound subjects (map list all-subjects)))

(define properties (declare-relation 1 "properties"))

(define properties-bound (make-exact-bound properties (map list all-properties)))

(define objects (declare-relation 1 "objects"))

(define objects-bound (make-exact-bound objects (map list all-objects)))

(define entities (declare-relation 1 "entities"))

(define entities-bound (make-exact-bound entities (map list all-entities)))

(define atoms (declare-relation 1 "atoms"))

(define atoms-bound (make-exact-bound atoms (map list all-atoms)))

(define atom-relations (make-hash (map (lambda (a) (cons a (declare-relation 1 a))) all-atoms)))

(define atom-bounds (hash-map atom-relations (lambda (k v) (make-exact-bound v (list (list k))))))

(define (is-atom? a)
(hash-has-key? atom-relations a))

(define limits (bounds U (append atom-bounds (list subjects-bound properties-bound objects-bound entities-bound ;no-triples-bound
                                              atoms-bound triples-bound
                                              data-01-bound
                                              result-tp-01-bound result-tp-02-bound))))

(define ib (instantiate-bounds limits))

;;

(define null-rel (hash-ref atom-relations 'Null))

;;

(define (solve-it x)
 (begin
   (solver-clear (current-solver))
   (solver-assert (current-solver) (list x))
   (solver-check (current-solver))))

;;

(define-syntax test
  (syntax-rules ()
    ((_ (test-name model-name) formula body ...)
     (define test-name
       (time
        (let* ((f (interpret* formula ib))
               (ff (and f (generate-sbp f limits)))
               (model-name (solve-it ff)))
          (println #'test-name)
          body
          ...
          (interpretation->relations (evaluate ib model-name) model-name)))))))

;;

(define (triple s p v)
(if (or (is-atom? s) (eq? s _))
    (let ((rel (if (eq? s _) entities (hash-ref atom-relations s))))
      (some ([x rel])
            (triple x p v)))
    (if (or (is-atom? p) (eq? p _))
        (let ((rel (if (eq? p _) entities (hash-ref atom-relations p))))
          (some ([x rel])
                (triple s x v)))
        (if (or (is-atom? v) (eq? v _))
            (let ((rel (if (eq? v _) atoms (hash-ref atom-relations v))))
              (some ([x rel])
                    (triple s p x)))
            (in (-> s p v) triples)))))

;;

(define-synthax (joins4 a1 a2 depth)
  #:base (triple [choose 'x 'p 'v1 'v2 a1 a2 _] [choose 'x 'p 'v1 'v2 a1 a2 _] [choose 'x 'p 'v1 'v2 a1 a2 _]) 
  #:else
  (choose (triple [choose 'x 'p 'v1 'v2 a1 a2 _] [choose 'x 'p 'v1 'v2 a1 a2 _] [choose 'x 'p 'v1 'v2 a1 a2 _])
          (some ([x atoms])
                (and
                 (triple _ a1 x)
                 (triple x _ a2)))))


(define-synthax (joins5 a1 a2 depth)
  #:base (triple _ a1 a2)
  #:else
  (choose (triple [choose 'x 'p 'v1 'v2 'x  a1 a2 _] a1 a2) 
          (some ([x atoms])
                (and
                 (triple _ a1 x)
                 (triple x _ a2)))))

;;

(test (dawg-triple-pattern-001 m) 
            (= result-tp-01
               (set ([p properties] [o objects]) 
                    (joins4 p o 2)))
    (print-forms m))

(test (dawg-triple-pattern-001-v2 m) 
            (= result-tp-01
               (set ([p properties] [o objects]) 
                    (joins5 p o 2)))
    (print-forms m))

(test (dawg-triple-pattern-002 m) 
            (= result-tp-02
               (set ([s subjects] [o objects]) 
                    (joins4 s o 2)))
    (print-forms m))
