#lang racket/unit
(require racket/match
         racket/dict
         racket/list
         racket/pretty
         racket/sequence
         racket/function
         syntax/id-table
         syntax/parse
         "../utils/utils.rkt"
         (env global-env type-alias-helper type-env-structs lexical-env)
         (types subtype abbrev tc-result match-expanders union numeric-tower)
         (only-in (infer infer)
                  meet join)
         (utils tc-utils contract-utils)
         (rep type-rep filter-rep)
         (private syntax-properties)
         "signatures.rkt"
         (for-syntax racket/base))

(import tc-expr^)
(export check-contract^)

;; TODO: Use this for check-contract, too. Something like:
;; (-Con (get-core-type t))
(define (get-core-type ty)
  (define coercible-simple-value-types
    (Un -Null -Symbol -Boolean -Keyword -Char -Bytes -String -Number))
  (match ty
    [(PredicateFilter: (FilterSet: (TypeFilter: t _) fs-))
     #:when (subtype ty (-> Univ Univ))
     t]
    [(Con*: t _) t]
    ;; TODO: These should all be interpreted as FlatCon, but we have no control
    ;; over that via get-core-type. Need to restructure the code to accomodate
    ;; that.
    [_
     #:when (subtype ty coercible-simple-value-types)
     ty]
    ;; Because the type of these isn't the core type needed for the contract,
    ;; they need to be handled differently than coercible-simple-value-types
    [(== -Regexp) -String]
    [(== -Byte-Regexp) -Bytes]
    ;; See explanation in filter->contract
    ;[(Function: (list (arr: t (== -Boolean) _ _ _))) t]
    [_ (Un)]))

;; trawl-for-doms/rng : syntax predicate predicate -> (listof syntax)
;; Finds syntax/subforms for which is-dom/rng? returns a non-#f value. Does not
;; recur into arrow subforms, according to is-arrow? since those must still be
;; typechecked. Do not call with an arrow that is also a domain/range, that will
;; infinite loop.
(define (trawl-for-doms/rng form is-dom/rng? is-arrow?)
  #;(pretty-print (syntax->datum form))
  (syntax-parse form
    [_
     #:when (is-dom/rng? form)
     (list form)]
    [(forms ...)
     (define-values (arrows non-arrows)
       (for/fold ([arrows '()]
                  [non-arrows '()])
                 ([form (in-list (syntax->list #'(forms ...)))])
         (syntax-parse form
           [_
            ;; we only want arrows that match the predicate; e.g. when looking
            ;; for the rng we have to make sure we don't grab a dom
            #:when (and (is-arrow? form) (is-dom/rng? form))
            (values (cons form arrows) non-arrows)]
           [_
            #:when (is-arrow? form)
            (values arrows non-arrows)]
           [_ (values arrows (cons form non-arrows))])))
     (for/fold ([doms/rng arrows])
               ([non-arrow (in-list non-arrows)])
       (append doms/rng (trawl-for-doms/rng non-arrow is-dom/rng? is-arrow?)))]
    [_ '()]))

;; tc-arrow-contract : syntax -> (Con t)
(define (tc-arrow-contract form)
  (define arrow-subforms (or (syntax->list form) (list)))
  (when (empty? arrow-subforms)
    (int-err "no subforms for given -> contract form ~a" form))
  (define is-arrow? (syntax-parser [:ctc:arrow^ #t] [_ #f]))
  (define doms
    (append*
     (map
      (λ (form) (trawl-for-doms/rng form ctc:arrow-dom-property is-arrow?))
      arrow-subforms)))
  (define sorted-doms (sort doms < #:key ctc:arrow-dom-property))
  (define is-rng? (syntax-parser [:ctc:arrow-rng^ #t] [_ #f]))
  (define rng*
    (append* (map
              (λ (form) (trawl-for-doms/rng form is-rng? is-arrow?))
              arrow-subforms)))
  (when (not (= 1 (length rng*)))
    (int-err "got more than one rng when typechecking -> contract"))
  (define rng (first rng*))

  (define-values (in-doms out-doms)
    (for/lists (ins outs)
               ([dom (in-list sorted-doms)])
      (define dom-ty (coerce-to-con (tc-expr/t dom)))
      (values (Con*-in-ty dom-ty) (Con*-out-ty dom-ty))))
  (define rng-ty (coerce-to-con (tc-expr/t rng)))
  (ret (-Con (->* out-doms (Con*-in-ty rng-ty))
             (->* in-doms (Con*-out-ty rng-ty)))))

;; tc-arrow-i-contract : syntax -> (Con t)
(define (tc-arrow-i-contract form)
  (define arrow-subforms (or (syntax->list form) (list)))
  (when (empty? arrow-subforms)
    (int-err "no subforms for given ->i form ~a" form))
  (define is-arrow-i? (syntax-parser [:ctc:arrow-i^ #t] [_ #f]))
  (define expanded-ctcs
    (remove-duplicates
     (append*
      (map
       (λ (form) (trawl-for-doms/rng form ctc:arrow-i-dom-property is-arrow-i?))
       arrow-subforms))
     free-identifier=?
     #:key (lambda (ctc) (dom-info-id (ctc:arrow-i-dom-property ctc)))))
  (define dom-infos (map ctc:arrow-i-dom-property expanded-ctcs))

  ;; (list (list id dep ...) ...)
  (define dep-map (for/list ([info (in-list dom-infos)])
                    (define id (dom-info-id info))
                    (define deps (or (dom-info-deps info) (list)))
                    (cons id deps)))
  (define topo-sorted-dom-ids
    (reverse (flatten (find-strongly-connected-type-aliases dep-map))))

  (define dom-expanded-ctcs-by-id
    (for/hash ([ctc expanded-ctcs])
      (define info (ctc:arrow-i-dom-property ctc))
      (values (dom-info-id info) ctc)))

  (define dom-surface-deps-by-id
    (for/hash ([info dom-infos])
      (values (dom-info-id info) (or (dom-info-deps info) (list)))))

  (define-values (doms-checked-env dom-ctc-tys-by-id)
    (for/fold ([env (lexical-env)]
               [ctc-tys (hash)])
              ([dom-id (in-list topo-sorted-dom-ids)])
      (define surface-deps (hash-ref dom-surface-deps-by-id dom-id))
      (define ctc* (hash-ref dom-expanded-ctcs-by-id dom-id))
      (define-values (expanded-deps ctc)
        (syntax-parse ctc*
          ;; ctc is transformed to (begin deps ... ctc) by ->i in contract-prims
          [(_ deps ... ctc)
           (values #'(deps ...) #'ctc)]))
      (define-values (expansion-ids tys)
        (for/lists (ids tys)
                   ([surface-dep (in-list surface-deps)]
                    [expanded-dep (in-syntax expanded-deps)])
          (values expanded-dep (lookup env surface-dep void))))
      (define env* (extend/values env expansion-ids tys))
      (define ctc-ty (with-lexical-env env* (coerce-to-con (tc-expr/t ctc))))
      (values
       (extend env* dom-id (Con*-out-ty ctc-ty))
       (hash-set ctc-tys dom-id ctc-ty))))
  (define possible-rngs
    (append*
      (map
       (λ (form) (trawl-for-doms/rng form ctc:arrow-i-rng-property is-arrow-i?))
       arrow-subforms)))
  (when (zero? (length possible-rngs))
    (int-err "no range contract found when typechecking ->i expansion"))
  (define rng-ctc* (first possible-rngs))
  (define-values (expanded-rng-deps rng-ctc)
    (syntax-parse rng-ctc*
      [(_ deps ... rng-ctc)
       (values #'(deps ...) #'rng-ctc)]))
  (define rng-info (ctc:arrow-i-rng-property rng-ctc*))
  (define surface-rng-deps (rng-info-deps rng-info))
  (define-values (rng-ids rng-tys) (for/lists (ids tys)
                                              ([surface-rng-dep (in-syntax surface-rng-deps)]
                                               [expanded-rng-dep (in-syntax expanded-rng-deps)])
                                     (values expanded-rng-dep (lookup doms-checked-env surface-rng-dep void))))
  (define final-env* (extend/values doms-checked-env rng-ids rng-tys))
  (define rng-id (rng-info-id rng-info))
  (define rng-ctc-ty (with-lexical-env final-env* (coerce-to-con (tc-expr/t rng-ctc))))
  ;; assuming the result passes the range check, its dependents can use it at
  ;; the contract's out type
  (define final-env (extend final-env* rng-id (Con*-out-ty rng-ctc-ty)))

  (define-values (kw-dom-infos plain-dom-infos)
    (partition (lambda (info) (keyword? (dom-info-type info))) dom-infos))
  (define-values (mandatory-plain-dom-infos optional-plain-dom-infos)
    (partition dom-info-mandatory? plain-dom-infos))
  (define sorted-mandatory-plain-dom-infos (sort mandatory-plain-dom-infos < #:key dom-info-type))
  (define sorted-optional-plain-dom-infos (sort optional-plain-dom-infos < #:key dom-info-type))
  (define sorted-kw-dom-infos (sort kw-dom-infos keyword<? #:key dom-info-type))
  (with-lexical-env final-env
    (define opt-count (length optional-plain-dom-infos))
    (define-values (in-arrs out-arrs)
      (for/lists (ins outs)
                 ([vararg-slice-length (in-range (add1 opt-count))])
        (define opts (take sorted-optional-plain-dom-infos vararg-slice-length))
        (define doms (append sorted-mandatory-plain-dom-infos opts))
        (define (dom-ty d) (hash-ref dom-ctc-tys-by-id (dom-info-id d)))
        (define (kw Con*in/out-ty kw-info)
          (define kw (dom-info-type kw-info))
          (define ty (hash-ref dom-ctc-tys-by-id (dom-info-id kw-info)))
          (make-Keyword kw (Con*in/out-ty ty) (dom-info-mandatory? kw-info)))
        (values
         (make-arr* (map (compose Con*-out-ty dom-ty) doms)
                    (Con*-in-ty rng-ctc-ty)
                    #:rest #f
                    #:kws (map (curry kw Con*-out-ty) sorted-kw-dom-infos))
         (make-arr* (map (compose Con*-in-ty dom-ty) doms)
                    (Con*-out-ty rng-ctc-ty)
                    #:rest #f
                    #:kws (map (curry kw Con*-in-ty) sorted-kw-dom-infos)))))
    (ret (-Con (make-Function in-arrs) (make-Function out-arrs)))))

;; trawl-for-subs : syntax -> (list syntax)
;; Don't call with a dont-recur? that is also is-sub?
(define (trawl-for-subs form dont-recur? is-sub?)
  (syntax-parse form
    [_
     #:when (is-sub? form)
     (list form)]
    [(forms ...)
     (for/fold ([subs '()])
               ([form (in-list (syntax->list #'(forms ...)))])
       (syntax-parse form
         [_
          #:when (and (dont-recur? form)
                      (is-sub? form))
          (cons form subs)]
         [_ (append subs (trawl-for-subs form dont-recur? is-sub?))]))]
    [_ '()]))

;; tc-and/c : syntax -> (Con t)
(define (tc-and/c form)
  (define subs (sort (trawl-for-subs (ctc:and/c-sub-property form #f)
                                      (syntax-parser [:ctc:and/c^ #t]
                                                     [_ #f])
                                      ctc:and/c-sub-property)
                      <
                      #:key ctc:and/c-sub-property))
  (define subs-tys (map (compose coerce-to-con tc-expr/t) subs))
  (define-values (in-ty out-ty)
    (if (empty? subs-tys)
        (values Univ Univ)
        (for/fold ([in-ty (Con*-in-ty (first subs-tys))]
                   [out-ty (Con*-out-ty (first subs-tys))])
                  ([ty (in-list (rest subs-tys))])
          (define next-in-ty (Con*-in-ty ty))
          (unless (subtype out-ty next-in-ty)
            (tc-error/fields
             "preceding contract's output type does not match the next input type"
             #:delayed? #f
             "previous output type" out-ty
             "next input type" next-in-ty))
          (values in-ty (meet out-ty (Con*-out-ty ty))))))
  (ret (-Con in-ty out-ty)))

;; tc-or/c : syntax -> (Con t)
(define (tc-or/c form)
  (define subs (sort (trawl-for-subs (ctc:or/c-sub-property form #f)
                                     (syntax-parser [:ctc:or/c^ #t]
                                                    [_ #f])
                                     ctc:or/c-sub-property)
                     <
                     #:key ctc:or/c-sub-property))
  (define-values (in-ty out-ty)
    (for/fold ([in-ty Univ]
               [out-ty (Un)])
              ([sub (in-list subs)])
      (define con-ty (coerce-to-con (tc-expr/t sub)))
      (values
       ;; XXX: simply taking the meet might not work for higher-order contracts,
       ;; even if it did turn arrows into a case->. so, there may need to be
       ;; some extra work to support higher-order contracts in or/c
       (meet in-ty (Con*-in-ty con-ty))
       (join out-ty (Con*-out-ty con-ty)))))
  (ret (-Con in-ty out-ty)))

;; tc-list/c : syntax -> (Con t)
(define (tc-list/c form)
  (define subs (sort (trawl-for-subs (ctc:list/c-sub-property form #f)
                                     (syntax-parser [:ctc:list/c^ #t]
                                                    [_ #f])
                                     ctc:list/c-sub-property)
                     <
                     #:key ctc:list/c-sub-property))
  (define-values (in-tys out-tys)
    (for/lists (ins outs)
               ([sub (in-list subs)])
      (define con-ty (coerce-to-con (tc-expr/t sub)))
      (values (Con*-in-ty con-ty) (Con*-out-ty con-ty))))
  (ret (match* (in-tys out-tys)
         [((list) (list))
          (-Con Univ (-lst*))]
         [((list _ _ ...) (list _ _ ...))
          (-Con (apply -lst* in-tys) (apply -lst* out-tys))])))

(define (coerce-to-con ty)
  (define coercible-simple-value-types
    (Un -Null -Symbol -Boolean -Keyword -Char -Bytes -String -Number))
  [match ty
    [(Con*: t _) ty]
    [(ConFn*: in-ty out-ty)
     (-FlatCon in-ty out-ty)]
    [_
     #:when (subtype ty coercible-simple-value-types)
     (-FlatCon Univ ty)]
    ;; Because the type of these isn't the core type needed for the contract,
    ;; they need to be handled differently than coercible-simple-value-types
    [(== -Regexp) (-FlatCon Univ -String)]
    [(== -Byte-Regexp) (-FlatCon Univ -Bytes)]
    ;; TODO: replace this with an error
    [_ (tc-error/fields "could not coerce to a contract type"
                        #:delayed? #t
                        "type" ty)]])

;; check-contract : identifier syntax -> [void]
(define (check-contract defn-id ctc)
  (match-define (Con*: in-ty _) (coerce-to-con (tc-expr/t ctc)))
  (unless (subtype in-ty (lookup-type defn-id))
    (tc-error/fields "contract is incompatible with type"
                     #:delayed? #t
                     "type" (lookup-type defn-id)
                     "contract type" (coerce-to-con (tc-expr/t ctc)))))
