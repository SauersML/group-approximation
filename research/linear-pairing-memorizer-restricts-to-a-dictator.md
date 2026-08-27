---
rg: 2
id: linear-pairing-memorizer-restricts-to-a-dictator
kind: claim
title: A bounded homogeneous function of degree 2r+1 can be an exact dictator on an affine-pair subcube while every ambient influence tends to zero
invalidates:
  - glue-lemma-via-ambient-influence-transfer
distinct_from:
  affine-memorizers-are-cross-direction-orthogonal: that is about the joint behaviour of the memorizers for different directions and is proved by a mod-4 orbit argument; this is the single-direction construction and its four exact properties.
  memorizer-superposition-has-large-sup-norm: that is a lower bound on the sup norm of superpositions, limiting what the family can refute; this is the construction of one memorizer and what it kills.
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  Let `Omega = F_2^k`, `N = |Omega|`, fix `b != 0`, let
`P_b` be the partition of `Omega` into the affine pairs `{u, u+b}`, put
`C_b = {0, b}`, let `r >= 1` be **odd** and `M = binom(N/2 - 1, r)`.  Define

```text
B_{b,r}(X) = X_0 * (1/M) * sum_{A subset P_b \ {C_b}, |A| = r}
                              prod_{{u,u+b} in A} X_u X_{u+b}.
```

Then, exactly:

```text
|B_{b,r}(X)| <= 1                       for every X in {-1,1}^Omega,   (M1)
B_{b,r} is homogeneous of degree 2r+1,                                 (M2)
B_{b,r}|_{D_b} = X_0,                                                  (M3)
||B_{b,r}||_2^2 = 1/M = Theta_r(N^{-r}).                               (M4)
```

Here `D_b = {X : X_x = X_{x+b} for all x}` and `X_0` denotes the quotient
coordinate indexed by the coset `C_b`.

Three consequences, each of which closes a natural line of attack on
`affine-orientation-glue-lemma`.

**Influence transfer fails, with no dimension-free constant.**  Total
influence of `B_{b,r}` is `(2r+1)/M = Theta_r(N^{-r})`, while its
restriction to `D_b` is a dictator, of total influence 1.  So no inequality

```text
Inf( f|_{D_b} ) <= C * Inf( f ),   C independent of k,
```

can hold, and the failure is already at fixed degree `2r+1` and for `f`
bounded by 1.

**Noise does not damp it.**  By `(M2)` every monomial has the same degree,
so `T_rho B_{b,r} = rho^(2r+1) B_{b,r}` exactly.  Setting `g = T_rho f` with
`f = B_{b,r}` gives `g|_{D_b} = rho^(2r+1) X_0`, so the coset `C_b` is
`(d, delta)`-heavy for every `d >= 1` with `delta = rho^(2*(2r+1))`, a
constant independent of `k`.  Boundedness, low degree and noise smoothing
*together* still permit one direction to be memorized.

**There is no ambient influential coordinate to find.**  Coordinate `0`
carries ambient influence `Inf_0(B_{b,r}) = 1/M -> 0`, and by symmetry so
does every other coordinate.  So the escape clause of the glue lemma ("unless
`f` already has a bounded number of large ambient low-degree influences")
is not satisfied here: a decoder looking for ambient influential
coordinates finds none, yet the restricted dictator is fully present.  The
glue lemma itself survives -- with a single direction, `Q = {0}` is a
bounded hitting set -- but the route through ambient influence does not.

The proof is `linear-pairing-memorizer-dictator-proof`.
