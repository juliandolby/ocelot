#lang rosette

(define (symbolic? x) 
  (or (union? x) (term? x)))

(define (stringish? s)
  (string? s))

(define (stringish=? a b)
  (equal? a b))

(define (stringish-prefix? a b)
  (string-prefix? a b))

(provide (all-defined-out))
