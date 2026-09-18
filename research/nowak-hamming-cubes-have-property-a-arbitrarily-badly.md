---
rg: 2
id: nowak-hamming-cubes-have-property-a-arbitrarily-badly
kind: claim
title: "Nowak: Hamming cubes need unbounded support radius for property A witnesses, so any metric space retracting 1-Lipschitz onto cubes of every dimension fails property A"
distinct_from:
  decidable-graphical-non-exact-groups-exist: that concerns Osajda's finitely generated groups (bounded geometry) without property A, one with isometric expanders and one acting properly on a CAT(0) cube complex; this imports Nowak's locally finite but unbounded-geometry spaces of Hamming cubes, which fail property A only through unbounded dimension.
---

**ESTABLISHED (citation)** through `nowak-hamming-cubes-have-property-a-arbitrarily-badly-citation`.

Let `Q_n = {0,1}^n = (Z/2)^n` with the Hamming (`ℓ^1`) metric. For a discrete metric space `X` and
`R, ε > 0`, let `diam^A_X(R,ε)` be the least `S` such that there is `ξ : X → ℓ^1(X)` with `‖ξ_x‖_1 = 1`,
`‖ξ_x − ξ_y‖_1 < ε` whenever `d(x,y) ≤ R`, and `supp ξ_x ⊆ B̄(x,S)`. It is `∞` if no such `S` exists.

1. **(Nowak, Thm 3.3 and 4.3.)** For every `0 < ε < 2`, `diam^A_{Q_n}(1,ε) → ∞` as `n → ∞`.
2. **(Yu's A gives finite diameters, no bounded geometry needed.)** If `X` has Yu's property A, then
   `diam^A_X(R,ε) < ∞` for all `R, ε > 0`, and the witness `ξ` can be taken nonnegative.

Item 1 is Theorem 7.4.4 (Nowak's 4.3) for `G = Z/2`, combined with Theorem 7.4.3 (Nowak's 3.3) applied to the
amenable group `Z_2^n`. Item 2 is Willett's Proposition 7.4.2(1) together with the proof of Theorem 1.2.4
(1) ⇒ (2), which does not use bounded geometry.

**Use downstream.** Let `Y` be a metric space that contains isometric copies `Q_n ⊆ Y` for infinitely many `n`,
each with a 1-Lipschitz retraction `π_n : Y → Q_n`. Then `Y` fails property A.

- Push a nonnegative witness forward: `η_q = (π_n)_* ξ_q`. This keeps norm 1 and does not increase the
  variation.
- Supports stay in `π_n(B̄(q,S)) ⊆ B̄(q,S) ∩ Q_n`.
- So `diam^A_{Q_n}(R,ε) ≤ diam^A_Y(R,ε)` for every such `n`, which contradicts item 1.

This is Nowak's argument for the disjoint union `⊔ Q_n`, with retractions replacing the disjoint union.
