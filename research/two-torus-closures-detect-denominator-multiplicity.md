---
rg: 2
id: two-torus-closures-detect-denominator-multiplicity
kind: claim
title: Two rank-one torus closures exactly detect denominator multiplicity
artifacts:
  - research/two-torus-denominator-multiplicity-proof.md
distinct_from:
  closed-a2-dyadic-packet-saturates-the-sl3-actor: that proves abstractly that four integral simple roots and the denominator element generate the full arithmetic actor; this gives one explicit fixed unbalanced identity and computes exactly what it does to a commuting denominator multiplicity twist.
  balanced-denominator-transport-is-ucp-neutral: that constructs a twist invisible to every denominator-balanced relation; this supplies the first explicit unbalanced arithmetic word which sees the twist with no loss.
  one-britton-moment-forces-uniform-actor-noncorrectability: that detects distance from every exact actor using a central letter and a trace moment; this is a deterministic ordinary-word identity detecting the pure denominator-multiplicity component itself.
---

Fix `p`, put `x_ij(a)=I+aE_ij` in `SL_3(Z[1/p])`, and set

```text
h=diag(p,1,p^(-1)),
w_ij(a)=x_ij(a)x_ji(-a^(-1))x_ij(a).                    (TTC1)
```

Define the two balanced words

```text
D_12=x_12(p) h x_21(-1) h^(-1) x_12(p) w_12(1)^(-1),
D_23=x_23(p) h x_32(-1) h^(-1) x_23(p) w_23(1)^(-1).   (TTC2)
```

Then

```text
D_12=diag(p,p^(-1),1),
D_23=diag(1,p,p^(-1)),
D_12 D_23=h.                                            (TTC3)
```

Consequently

```text
R_tor=h^(-1)D_12D_23=1                                 (TTC4)
```

is an explicit arithmetic relation of total `h`-exponent `-1`.

It detects the exact multiplicity escape left invisible by balanced
denominator transport.  Let `rho:Gamma->U(K)` be any finite-dimensional
representation and `V in U(M)`.  On `M tensor K` assign

```text
X_g=I_M tensor rho(g)       (g in Lambda),
H=V tensor rho(h).                                      (TTC5)
```

Every balanced denominator-conjugacy word cancels `V`, but

```text
ev_(X,H)(R_tor)=V^(-1) tensor I_K,
||ev_(X,H)(R_tor)-I||_2=||V-I||_2.                      (TTC6)
```

Thus one fixed ordinary relation charges a pure denominator multiplicity
twist with sharp constant one.  In particular the twist used by
`balanced-denominator-transport-is-ucp-neutral` is excluded by `(TTC4)`
with defect `sqrt(2-sqrt(2))`.

The scope is exact: `(TTC6)` handles the product-normal-form actor sector
`(TTC5)`.  The surviving matrix-range problem concerns arbitrary approximate
arithmetic actor outliers, for which one still has to extract or control such
a multiplicity coordinate before `(TTC6)` can charge the separator.
