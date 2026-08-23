---
rg: 2
id: gauge-optimized-induced-energy-target
kind: claim
title: Gauge-optimized induced energy is the corrected relative two-dimensional target
distinct_from:
  induced-rounding-needs-rms-section-fillings: that freezes the supplied exact core and is refuted by a small r-character twist; this minimizes over nearby exact core coordinates before constructing the induced section.
  authenticated-core-union-basin-is-relative-liftability: that gives the qualitative ultraproduct lifting endpoint; this states one finite-dimensional quadratic functional sufficient for it and checks that the known frozen-core counterfamily is absorbed at the correct scale.
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that retracts after one exact endpoint type has been selected; this is a proposed energy estimate for selecting a nearby core and producing the almost-invariant induced range.
  gauge-optimized-target-has-uniform-congruence-tangent-gap: that proves the first-order version of the optimized estimate at every congruence endpoint while leaving its nonlinear HS integration open.
---

Use the square-free endpoint coordinates

```text
<x,r,t | x^2, (xr)^2, (xt)^3,
         rtr^(-1)=t^4, (xt^2r)^3, t^N>.               (GOI1)
```

Fix a dimension `d`.  Let `C_N(d)` be the variety of exact `B_N`-cores
`c=(R_c,T_c)` satisfying

```text
R_c T_c R_c^(-1)=T_c^4,       T_c^N=1.                (GOI2)
```

For an involution `X` and an exact supplied core `b=(R,T)`, put

```text
E_end(X,b)=||(XR)^2-1||_2^2+||(XT)^3-1||_2^2
            +||(XT^2R)^3-1||_2^2.                    (GOI3)
```

For `c in C_N(d)`, form the hybrid tuple `U_c=(X,R_c,T_c)`.  Evaluate a
chosen Schreier section for `A_N/B_N` on this hybrid tuple and let
`D_(U_c,c)(q,a)` be its induced-coordinate edge defect, exactly as in
`induced-rounding-needs-rms-section-fillings`.  Define

```text
G_N(X,b)=inf_(c in C_N(d)) {
  ||R-R_c||_2^2+||T-T_c||_2^2
  +max_a (1/|A_N/B_N|) sum_q ||D_(U_c,c)(q,a)||_2^2 }.
                                                               (GOI4)
```

The corrected relative two-dimensional estimate would be

```text
G_N(X,b) <= C E_end(X,b)                               (GOI5)
```

with `C` independent of `N`, `d`, and the exact supplied core.  The assertion
that this estimate holds is the separate open claim
`uniform-gauge-optimized-induced-energy`.  If `(GOI5)`
holds for the dyadic one-power quotients (allowing the already established
flexible rank convention), then the induced-projection argument gives the
quadratic padding and square-root displacement required by
`bs14-flexible-cross-packet-boundary-reconciliation`.

This claim records the proved reduction and the correct functional; it does
**not** assert `(GOI5)`.

## Why the reduction is sufficient

Choose `c` within an arbitrarily small error of the infimum in `(GOI4)`.
The first two terms pay the movement from the supplied exact core to the
hybrid core.  Apply the isometry `(ISR1)` from
`induced-rms-section-rounding-proof` to `U_c`.  The last term in `(GOI4)`
is exactly the square of its generator-intertwining defect.  The uniform
Cayley gap, conditional expectation, and spectral cutting in
`(ISR3)--(ISR6)` produce an invariant projection with

```text
relative rank error = O(G_N(X,b)),
generator displacement = O(sqrt(G_N(X,b))).           (GOI6)
```

The exact compression of the induced representation is an endpoint whose
core differs from `(R,T)` by at most the first two terms of `(GOI4)` and
whose endpoint generator differs from `X` by `(GOI6)`.  Under `(GOI5)` this
is precisely energy-paid flexible repair.

## The cyclic counterfamily is removed, rather than hidden

Let `rho` be an exact endpoint at level `N=4^K-1`, let
`zeta=exp(2 pi i/K)`, and take the frozen-core countertuple

```text
X=rho(x),       R=zeta rho(r),       T=rho(t).         (GOI7)
```

Its supplied core is exact, while

```text
E_end(X,(R,T))
 =|zeta^2-1|^2+|zeta^3-1|^2.                          (GOI8)
```

In `(GOI4)` choose the untwisted exact core
`c=(rho(r),rho(t))`.  The hybrid tuple is the exact endpoint, so every
section edge defect vanishes, and

```text
G_N(X,(R,T)) <= |zeta-1|^2 <= E_end(X,(R,T)).          (GOI9)
```

Thus the family which makes the raw fixed-core edge energy stay bounded
below is paid at its true `O(K^(-2))` energy scale after core optimization.
By
`dyadic-congruence-core-abelianization-classifies-small-gauges`, this also
removes every asymptotically small **scalar** character direction on the
congruence core.  Higher-dimensional exact-core motions remain the
load-bearing part of `(GOI5)`.

## Firewall

Minimizing only over scalar characters is insufficient: exact BS packets
have slow multiplicity-commutant modes.  Conversely, minimizing over the
full exact-core variety is not a cosmetic weakening.  It is forced by the
flexible endpoint notion and by the explicit refutation of frozen-core
`(IRF8)`.  Any future Hodge or square-function proof must therefore be a
coercive estimate **transverse to `C_N(d)`**, with the tangent exact-core
directions quotiented out before the Cayley spectral gap is applied.

There is no further moving-level obstruction at the derivative: the
uniform quotient gap is established in
`gauge-optimized-target-has-uniform-congruence-tangent-gap`.  The unresolved
content of `(GOI5)` is therefore nonlinear HS integration, including
operator-large small-rank motions and changes of torsion multiplicity.
