---
rg: 2
id: artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring
kind: claim
title: "An Artin group on four vertices whose dead character admits no nonzero dead-edge ring, so the ring obstruction cannot prove the Sigma^1-conjecture in general"
---

Let `K` be the complete graph on `u1, u2, v1, v2` with labels
`l(u1u2) = l(v1v2) = 2`, `l(u1v1) = l(u2v1) = l(u2v2) = 4`, `l(u1v2) = 6`, and let
`χ(u1) = χ(u2) = 1`, `χ(v1) = χ(v2) = -1`.

1. Every vertex is living, `Liv_0^χ = K` is connected, the four cross edges are
   dead, and `Liv^χ = {u1–u2} ⊔ {v1–v2}` is disconnected.
2. The label-2 edges are not dead, so the only vertex partition whose cross edges are
   all dead is `{u1, u2} | {v1, v2}`.
3. If `R` is a ring, `ρ : A_K -> R^×`, and the four dead-edge sums vanish, then `R = 0`.
   Write `x̄ = ρ(x)`. From `1 + ū1 v̄1 = 0 = 1 + ū2 v̄1`, cancelling the unit `v̄1` gives
   `ū1 = ū2`. Then `ū1 v̄2 = ū2 v̄2 = -1`, and
   `1 + ū1 v̄2 + (ū1 v̄2)^2 = 1 - 1 + 1 = 1` must vanish.

So the hypothesis of `artin-sigma1-dead-edge-ring-obstruction` never holds for
`(A_K, χ)`. Neither do finite abelian twists (Escartín-Ferrer, Theorem 4.4).
`A_K` has circuit rank 3, halves 2 and 3 across the cut, is not balanced and not
coherent. It is outside families 1–4 and 6–11 of
`artin-sigma1-conjecture-known-families`; family 5, Almeida–Kochloukova's
4-vertex complete graphs "with major restrictions on the labels", was not checked.
Whether `[χ] ∈ Σ^1(A_K)` is the open test case
`artin-k4-mixed-dead-character-is-outside-sigma1`.
