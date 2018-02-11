#lang scribble/manual

@begin[(require "../utils.rkt" scribble/example racket/sandbox racket/require
                (for-label (only-meta-in 0 typed/racket)
                           (only-in racket/contract flat-contract?)))]
@(define the-top-eval (make-base-eval))
@(the-top-eval '(require (except-in typed/racket #%module-begin)))

@(define-syntax-rule (ex . args)
   (examples #:eval the-top-eval . args))

@title{Typed Contracts}

@defmodule[typed/racket/contract]

Typed Racket supports contract programming using the
@racketmodname[racket/contract] library. This section covers the
contract-specific features of the type system as well as the functionality
currently supported in Typed Racket.

@section{Types}

@defform[#:kind "type"
         (Contract [in type] [out type])]{
  A contract can only be attached to values that satisfy its @racket[in] type,
  just like how a function can only be applied to arguments that satisfy its
  domain type. Attaching a contract with output type @racket[out] to a value
  with type @racket[t] either raises blame or results in a value with a more
  precise type.

  The result's type is a lower-bound of @racket[out] and @racket[t] with respect
  to the precision order, which is like the subtype order. It differs in that it
  lacks contravariance in negative positions such as function domains.

  @racket[Contract] is the most general type for contracts.
}

@defform[#:kind "type"
         (FlatContract [in type] [out type])]{
  This type is like @racket[Contract] but corresponds to @tech{flat contracts}. All
  @racket[FlatCon] contracts have a corresponding @racket[Contract] type. For
  example, a @racket[(FlatContract Real Real)] is also a @racket[(Contract Real Real)].

  A contract with @racket[FlatCon] type can be used as a function having domain
  type @racket[in].

  Ordinary Racket @tech[#:key "contracts"]{values coercible to a contract}, such
  as integers, do not have this type. Coercing such values of type @racket[T] to
  a contract, as Racket's contract attachment forms automatically do, produces a
  value of type @racket[(FlatContract Any T)].
}

@section{Data-structure Contracts}

@deftogether[(@defproc[(flat-named-contract [name Any]
                                            [c (FlatContract a b)])
                       (FlatContract a b)]
              @defthing[any/c (FlatContract Any Any)]
              @defthing[none/c (FlatContract Any Any)]
              @defproc[(not/c [c (FlatContract a b)])
                       (FlatContract a b)]
              @defproc*[([(=/c [n Natural]) (FlatContract Any Natural)]
                         [(=/c [z Integer]) (FlatContract Any Integer)]
                         [(=/c [r Real]) (FlatContract Any Real)])]
              @defproc[(</c [r Real]) (FlatContract Any Real)]
              @defproc[(>/c [r Real]) (FlatContract Any Real)]
              @defproc[(<=/c [r Real]) (FlatContract Any Real)]
              @defproc[(>=/c [r Real]) (FlatContract Any Real)]
              @defproc[(between/c [lo Real] [hi Real]) (FlatContract Any Real)]
              @defproc[(real-in [lo Real] [hi Real]) (FlatContract Any Real)]
              @defproc*[([(integer-in [lo Positive-Integer] [hi Integer])
                          (FlatContract Any Positive-Integer)]
                         [(integer-in [lo Natural] [hi Integer])
                          (FlatContract Any Natural)]
                         [(integer-in [lo Integer] [hi Integer])
                          (FlatContract Any Integer)])]
              @defthing[natural-number/c (FlatContract Any Natural)]
              @defproc[(string-len/c [len Real])
                       (FlatContract Any String)]
              @defthing[false/c (Contract Any False)]
              @defthing[printable/c (FlatContract Any Any)]
              @defproc[(listof [c (Contract a b)])
                       (Contract (Listof a) (Listof b))]
              @defproc[(non-empty-listof [c (Contract a b)])
                       (Contract (Listof a) (Pairof b (Listof b)))]
              @defproc[(list*of [c (Contract a b)])
                       (Contract (Rec x (Pairof a (U a x)))
                            (Rec x (Pairof b (U b x))))]
              @defproc[(cons/c [car-c (Contract a b)]
                               [cdr-c (Contract c d)])
                       (Contract Any (Pairof b d))]
              @defproc[(syntax/c [c (FlatContract a b)])
                       (FlatContract (Syntaxof a) (Syntaxof b))]
              @defproc*[([(parameter/c [c (Contract a b)])
                          (Contract (Parameter b) (Parameter b))]
                         [(parameter/c [in-c (Contract a b)]
                                       [out-c (Contract c d)])
                          (Contract (Parameter b d) (Parameter b d))])]
              @defproc[(symbols [sym Symbol] ...+)
                       (Contract Any Symbol)])]{
  These forms are typed versions of those found in Racket. They are otherwise
  the same.
}

@section{Function Contracts}

Typed Racket supports two of Racket's function contract forms: @racket[->/c], a
renamed version of the contract library's function combinator, and @racket[->i].
The grammar for each form is the same in Typed Racket as it is in Racket.

For @racket[->/c], the ellipsis form is unsupported in Typed Racket.
Additionally, both forms do not support the @racket[any] range.

@section{Attaching Contracts to Values}

Typed Racket supports two of Racket's contract attachment forms:
@racket[contract-out] for attaching contracts to values that flow between server
and client modules, in addition to the primitive contract attachment form
@racket[contract] for directly attaching a contract to a value. Of course,
@racket[provide/contract] is also supported.

@; XXX: I wish I knew how to use the typechecker to get the input type. Also,
@; is talking about the value's type before the contract's type the correct
@; order? or should it be reversed?

Currently, attaching a contract to a value requires the value's type to be a
subtype of the contract's input type. The example below uses
@racket[contract-out] to attach a function contract with input type @racket[(->
Integer Real)] to a function with type @racket[(-> Integer Integer)]. Because
the latter is a subtype of the former, this program is well-typed.

@ex[(module game typed/racket
      (provide
       (contract-out
        [number-game (->/c even? positive?)]))
      (: number-game (-> Integer Integer))
      (define (number-game x)
        (+ 2 x)))
    (require 'game)
    (number-game 6)]

If attaching a contract to a value does not satisfy this requirement, as in the
following example, the typechecker rejects the program.

@ex[(eval:error (contract odd? "11" 'pos 'neg))]

Providing better error messages for Typed Racket's support of the contract
library is a work in progress.

@section{Limitations}

@itemlist[
  @item{Contract types do not have any contract compilation/runtime enforcement.}
  @item{Racket's built-in combinators for vectors, boxes, hashes are unsupported.}
  @item{Values that pass @racket[flat-contract?] are not necessarily members of
        the @racket[FlatContract] type: members of that type can be used in function
        position, but @racket[flat-contract?] returns true for non-predicates.}]
