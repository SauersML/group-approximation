---
rg: 2
id: lifted-thompson-t-shadow-residual-is-full
kind: claim
title: "Every operator-norm asymptotic representation of T-bar kills the central translation in normalized Hilbert-Schmidt norm (the shadow residual of T-bar is everything)"
distinct_from:
  lifted-thompson-t-is-not-mf: that asks every corona map of T-bar to kill z in operator norm; this asks only for normalized-HS triviality of z. It is implied by that claim, and by T-bar being non-hyperlinear.
  thompson-t-has-full-mf-radical: that is the non-MF statement for the quotient T; this one implies it (item 3 of lifted-thompson-t-shadow-residual-dichotomy), and it is also implied by non-hyperlinearity of T-bar.
  lifted-thompson-t-shadow-residual-dichotomy: that proves S(T-bar) is 1 or T-bar; this is the open assertion that it is T-bar.
---

**OPEN.**  Notation as in `lifted-thompson-t-shadow-residual-dichotomy`.
Claim:

```text
S(T̄) = R_(infinity->2)(T̄) = T̄.
```

## Equivalent forms

By items 1 and 2 of `lifted-thompson-t-shadow-residual-dichotomy`, and item 3
of `hs-invisible-corona-maps-are-full-trace-paddings`, the following are
equivalent:
- `S(T̄) = T̄`;
- `z in S(T̄)`;
- `S(T̄) != 1`;
- every corona homomorphism of `T̄` is a full-trace padding of a trace-null
  remainder.

It implies that no corona homomorphism of `T̄` has a gapped commutant corner
(item 2(b)).  The converse is not claimed.

## Where it sits

```text
T̄ not MF           ==>  this claim  ==>  T not MF
T̄ not hyperlinear  ==>  this claim
```

The converse of the second arrow is not claimed.  A hyperlinear model of
`T̄` gives HS-asymptotic representations.  `S` is tested only against
operator-norm asymptotic representations, so such a model does not by
itself put `z` outside `S(T̄)`.

## How it fails

- It fails if `T` is MF (item 2(a)).
- It fails if `T̄` is hyperlinear.
- It fails if one corona homomorphism of `T̄` has a gapped commutant corner.

## Role

This is the tracial conjunct (A) of the route
`lifted-thompson-t-not-mf-via-gapped-corners`.  Any entropy, measure or
character argument can reach at most this claim.  See the target's
`## Attempts`.
