#lang racket
(require "../utils/utils.rkt"
         (rep type-rep prop-rep)
         (types subtype)
         (only-in (infer infer) intersect)
         racket/match)

(provide pairwise-intersect)

(define (pairwise-intersect/arr s t)
  (match* (s t)
    [((arr: s-dom s-rng s-rest #f s-kws)
      (arr: t-dom t-rng t-rest #f t-kws))
     #:when (= (length s-kws) (length t-kws))
     (make-arr (map pairwise-intersect s-dom t-dom)
               (pairwise-intersect s-rng t-rng)
               (and s-rest t-rest
                    (pairwise-intersect s-rest t-rest))
               #f
               (map pairwise-intersect/kw s-kws t-kws))]
    [(_ _)
     (raise-arguments-error
      'pairwise-intersect/arr
      "pairwise-interescting unsupported for drest/different length kws"
      "s" s
      "t" t)]))

(define (pairwise-intersect/kw s t)
  (match* (s t)
    [((Keyword: ks ts rs) (Keyword: kt tt rt))
     #:when (and (eq? kt ks)
                 (or rt (not rs)))
     (make-Keyword ks (pairwise-intersect ts tt) rs)]
    [(_ _)
     (raise-arguments-error
      'pairwise-intersect/kw
      "keywords must match"
      "s" s
      "t" t)]))

(define (pairwise-intersect/prop-set ps qs)
  (match* (ps qs)
    [((PropSet: p+ p-) (PropSet: q+ q-))
     (make-PropSet (pairwise-intersect/prop p+ q+)
                   (pairwise-intersect/prop p- q-))]))

(define (pairwise-intersect/prop p1 p2)
  (match* (p1 p2)
    [(p p) p]
    [(p (TrueProp:)) p]
    [((TrueProp:) p) p]
    [((TypeProp: o s) (TypeProp: o t))
     (make-TypeProp o (pairwise-intersect s t))]
    [((NotTypeProp: o s) (NotTypeProp: o t))
     (make-NotTypeProp o (pairwise-intersect s t))]
    [(_ _)
     (raise-arguments-error
      'pairwise-intersect/prop
      "cannot merge props"
      "p1" p1
      "p2" p2)]))

;; pairwise-interesct : Type Type -> Type
;; Computes a lower bound of the two types w.r.t. the "precision order." The
;; precision order is like the subtype order except that it does not account for
;; variance. Effectively, this amounts to a fold over the two types in a uniform
;; way. For base types (and, as a default, for unimplemented cases) this
;; computes the intersection of the two types.
(define (pairwise-intersect s t)
  (match* (s t)
    [((Univ:) u) u]
    [(u (Univ:)) u]
    [((Function: arr1s) (Function: arr2s))
     (make-Function (map pairwise-intersect/arr arr1s arr2s))]
    [((Result: ss pset-s o) (Result: ts pset-t o))
     (make-Result (pairwise-intersect ss ts)
                  (pairwise-intersect/prop-set pset-s pset-t)
                  o)]
    [((Values: rs) (Values: rt))
     (make-Values (map pairwise-intersect rs rt))]
    [((ValuesDots: s-rs s-dty dbound) (ValuesDots: t-rs t-dty dbound))
     (make-ValuesDots (map pairwise-intersect s-rs t-rs)
                      (pairwise-intersect s-dty t-dty)
                      dbound)]
    ;; because we always want to return the poly type, regardless of it being on
    ;; the left or the right, i don't think we can use match*/no-order
    ;; XXX: intersect always returns the mono type. why is that? is it ok that
    ;; pairwise-intersect returns the poly type?
    [((Poly: vs b) _)
     #:when (or (subtype s t) (subtype t s))
     s]
    [(_ (Poly: vs b))
     #:when (or (subtype t s) (subtype s t))
     t]
    [(_ _)
     (intersect s t)]))