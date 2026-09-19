---
rg: 2
id: affine-s3-active-idempotent-toeplitz-envelope
kind: claim
title: The affine S3 active carrier is a central Toeplitz defect with a faithful infinite model
distinct_from:
  affine-s3-endpoint-permutes-active-atoms: that proves the finite affine action and its equal-rank consequence; this installs the invariant active sum as the defect of a one-sided inverse.
  schur-idempotent-is-an-injective-toeplitz-defect: that treats the forbidden central sum of a generic predicate packet; this specializes the construction to the three-atom active carrier and computes its affine Wedderburn corner.
  finite-affine-head-cannot-retain-old-commutant-density: that disproves tensor-independent retention of the affine commutant; this couples the same affine carrier intrinsically to the infinite coefficient algebra.
---

Let `C_aff=D semidirect S_3` and let `A` be the sum of the three active
marked atoms from `affine-s3-endpoint-permutes-active-atoms`.  Choose a
finite splitting field `k` of characteristic `p>=5` for `C_aff`.  Then

```text
A in Z(k[C_aff]),             0 != A != 1,                 (ATE1)
A k[C_aff] ~= M_3(k) direct_sum M_3(k).                   (ATE2)
```

Indeed the affine `S_3` fixes the forbidden character and acts transitively
on the other three marked characters, so their sum is invariant and hence
central.  The little group of one active character is `C_2`; its two
characters induce the two three-dimensional active irreducibles, which gives
`(ATE2)`.

Define

```text
R_aff=k[C_aff]*_k k<x,y>/(yx=1, 1-xy=A).                  (ATE3)
```

The packet algebra embeds in `R_aff`.  In particular `A` remains nonzero and
there is a faithful exact infinite-dimensional model with `A` alive.  Every
map from `R_aff` to a directly finite ring kills `A`.  The trivial character
of `C_aff` kills `A`, so the Toeplitz formula

```text
sigma(a)=xay+epsilon(a)A                                  (ATE4)
```

is a proper injective unital endomorphism of `R_aff`.

Consequently, for

```text
Gamma_aff=EL_5(R_aff),
H_aff=<Gamma_aff,t | t g t^-1=sigma(g)>,
w_aff=x_12(A),                                             (ATE5)
```

the base embeds in the ascending HNN extension, `w_aff!=1`, and every exact
finite-dimensional unitary representation of `H_aff` kills `w_aff`.

This construction survives the countermodel in
`finite-affine-head-cannot-retain-old-commutant-density`: it does not ask the
finite `S_3` head to retain a tensor-independent commutant.  Instead the
active projection itself is the non-surjectivity defect of the coefficient
compressor.  The remaining issue is purely asymptotic: whether a tracial
matrix-ultraproduct representation can keep the root `x_12(A)` alive.
