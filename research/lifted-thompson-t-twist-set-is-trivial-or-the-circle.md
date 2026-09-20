---
rg: 2
id: lifted-thompson-t-twist-set-is-trivial-or-the-circle
kind: claim
title: The scalar twists and the spectral values of the central translation of T-bar each form either the trivial group or the whole circle; T is MF exactly when one scalar twist other than 1 occurs, and T-bar is MF exactly when one spectral value other than 1 occurs
distinct_from:
  central-eigencorners-die-over-full-radical-quotients: that shows an exact eigencorner is fixed when T is full; this uses its item 1 only for P = 1 and proves the converse realisation (T MF gives every scalar twist), the closed-subgroup structure of both sets, and the all-or-nothing dichotomy.
  lifted-thompson-t-mf-radical-dichotomy: that decides the radical of T-bar as a subgroup (1 or everything); this decides the set of values of the central translation, scalar and spectral, and ties the scalar set to T rather than to T-bar.
  maslov-ce-parameter-set-is-a-closed-subgroup: that is a closed-subgroup statement for the CE parameter set of Deligne covers; this is the corona twist set of the lifted Thompson group, where the extra dilation and rotation-centralizer structure forces the set to be all or nothing.
---

**ESTABLISHED (written proof; not Lean-verified).**  Proof route:
`lifted-thompson-t-twist-set-is-trivial-or-the-circle-proof`.

Notation is that of `central-eigencorners-die-over-full-radical-quotients`.
`T̄` is the lift of Thompson's `T` to the line, `z` is the central
translation `x -> x + 1` and `T̄/<z> = T`.  A *corona representation* is a
homomorphism `rho : T̄ -> U(Q)` into a norm matrix corona
`Q = prod_n M_(k_n) / (+)_n M_(k_n)`.  Put

```text
Sigma = { mu in S^1 : some corona representation sigma has sigma(z) = mu 1 }   (scalar twists)
S     = union over corona representations rho of sp(rho(z))                   (spectral values)
```

Then `Sigma ⊆ S`, and:

1. **(Closed subgroups.)**  `Sigma` and `S` are closed subgroups of `S^1`.
2. **(Scalar dichotomy.)**  `Sigma = {1}` or `Sigma = S^1`.  Moreover
   `Sigma = S^1` if and only if `T` is MF, and `Sigma = {1}` if and only if
   `T` has full MF radical.  In particular, **`T` is MF as soon as one corona
   representation of `T̄` sends `z` to a scalar `mu != 1`**.  This holds for
   any single `mu`, for example `mu = -1` or an irrational rotation
   `e^(2 pi i theta)`.  Conversely, if `T` is MF then every
   `mu in S^1` is realised.
3. **(Spectral dichotomy.)**  `S = {1}` or `S = S^1`.  Moreover `S = S^1`
   if and only if `T̄` is MF.  In particular, if a single corona
   representation moves `z`, then every `mu in S^1` lies in the spectrum of
   `rho(z)` for some corona representation `rho`.

## What this changes

The three statements on the table are now statements about two subsets of
the circle, and each subset can only be trivial or everything:

```text
lifted-thompson-t-is-not-mf      <=>  S     = {1}
thompson-t-has-full-mf-radical   <=>  Sigma = {1}
lifted-thompson-t-mf-descends-to-t  <=>  ( S = S^1  =>  Sigma = S^1 )
```

- The flagship hole is therefore
  `thompson-t-has-full-mf-radical` together with the implication "spectral
  twist gives scalar twist".  That implication is
  `lifted-thompson-t-mf-descends-to-t` (route
  `lifted-thompson-t-not-mf-via-mf-descent`).  By item 2 it needs only one
  scalar twist in one representation, not an eigencorner in every
  representation as (EC) of
  `lifted-thompson-t-centre-has-commutant-eigencorners` asks.
- An MF model of `T` may now be looked for as a *twisted* model of `T̄`.  That
  is an asymptotic representation of `T̄` in which `z` goes to any fixed
  scalar `mu != 1`, for example `mu = -1`.  No representation of `T` itself
  needs to be written down.  The twist value is free.  Irrational twists are
  allowed, and they have no finite-quotient counterpart.
- The mechanism for "one twist gives all twists" is the dilation
  `lambda(g)(x) = g(2x)/2`.  It sends `z` to a `2^j`-th root of `z` that is
  central in the image of `lambda^j`.  The finite spectrum of that root then
  splits off an exact eigencorner.  This is the one place where the dilation,
  recorded as unused structure in
  `lifted-thompson-t-centre-has-commutant-eigencorners`, does real work.
