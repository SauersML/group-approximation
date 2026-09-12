---
rg: 2
id: whitehead-assembly-cokernel-proof
kind: route
title: Atiyah-Hirzebruch in degree one plus Bass-Heller-Swan on the circle
target: whitehead-is-degree-one-assembly-cokernel
requires: []
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

## Why sufficient

`BG` is connected, so `BG_+ ~ S^0 v BG` stably and

    H_1(BG; K(Z)) = K_1(Z) (+) H~_1(BG; K(Z)).

For the reduced summand run `E^2_{p,q} = H~_p(BG; K_q(Z))`.  `Z` is regular,
so `K_q(Z) = 0` for `q < 0` and `K_0(Z) = Z`.  In reduced total degree one
`p >= 1`, leaving only `E^2_{1,0} = H~_1(BG; Z) = G_ab`.  Nothing touches it:
an incoming `d_r` starts at `(1+r, 1-r)` with coefficients `K_{1-r}(Z) = 0`
for `r >= 2`, and an outgoing `d_r` lands in negative `p`.  So

    H_1(BG; K(Z)) = C_2 (+) G_ab,      C_2 = K_1(Z) = {+-1}.

Identify the assembly on each summand.  On `K_1(Z)` it is induced by the
scalar inclusion `Z -> ZG`, sending the nontrivial element to `[-1]`.  For
`g` in `G`, the corresponding class of `G_ab = H_1(BG; Z)` is represented by
`S^1 = BZ -> BG` classifying `1 |-> g`; by naturality it suffices to compute
for `G = Z`, where Bass--Heller--Swan for `Z[t,t^-1]` sends the circle's
`K_0(Z)`-generator to the Laurent unit `t`.  Hence `g |-> [g]`.

Therefore `im(A_1^G) = <[-1], [g] : g in G> = <[+-g]>`, whose cokernel in
`K_1(ZG)` is the defining quotient of `Wh(G)`.

## Provenance

Folklore; this is the trivial-family case of the standard assembly picture
and no novelty is claimed.  Written out because the graph needs the
identification of the *image* with the trivial units, which is the only step
with content, and because the computation of the source is what turns the
conjecture into a statement about a specific finite list of generators.
Full text in audit Section A.
