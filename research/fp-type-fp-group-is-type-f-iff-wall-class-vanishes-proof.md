---
rg: 2
id: fp-type-fp-group-is-type-f-iff-wall-class-vanishes-proof
kind: route
title: "Proof of the Wall-class criterion for type F"
target: fp-type-fp-group-is-type-f-iff-wall-class-vanishes
requires: []
---

Standard facts (S3) and (S4) are those of
`g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof`.

*Independence of the resolution.* For two finite projective resolutions `P_*`,
`P'_*` of `Z`, the generalized Schanuel lemma gives
`P_0 ⊕ P'_1 ⊕ P_2 ⊕ ⋯ ≅ P'_0 ⊕ P_1 ⊕ P'_2 ⊕ ⋯` (finite sums), so the alternating
sums agree in `K_0(ZG)`.

*(1) ⇒ (2).* The cellular chain complex of the universal cover of a finite
`K(G,1)` is a finite free resolution of `Z`.

*(2) ⇒ (3).* For a finite free resolution every term has class in `Z·[ZG]`.

*(3) ⇒ (2).* If `σ(G) = 0` then `Σ (−1)^i [P_i] ∈ Z·[ZG]`, and (S3) gives a finite
free resolution.

*(2) ⇒ (1).* `G` is finitely presented, so (S4) applies. Sketch of (S4): start
from a finite presentation 2-complex `X_2`; for `k ≥ 2`, `π_k(X_k) = H_k(X̃_k)` is the
kernel of the top boundary map of a partial free resolution and is finitely
generated because `G` is of type `FP_∞`, so finitely many `(k+1)`-cells kill it.
At `k = n = max(3, cd G)` the kernel is projective, and its class is `±σ(G)` modulo
`Z·[ZG]`, hence stably free. Wedging finitely many `n`-spheres makes it free, and
attaching `(n+1)`-cells along a basis gives a finite complex whose universal
cover is contractible by Hurewicz and Whitehead.

*Relation to Wall's obstruction.* A finitely presented group of type FP has a
finitely dominated `K(G,1)` (Wall 1965), and its finiteness obstruction is the
Euler class of the cellular chain complex of the universal cover, which is
chain equivalent to `P_*`; so it equals `σ(G)` up to the sign convention.

Unreviewed as of 2026-09-13: owed to z-verify-topology.
