---
rg: 2
id: rigid-seed-constructions-pass-the-separability-test
kind: claim
title: Wall-chamber distance seeds have no two modifications of one point more than r_0 + 2 apart, because orientations along a nested wall chain switch once; the test is preserved by products, so surface, median and product seeds pass, relative-seed and Kurosh gluings pass on audit, and building seeds show no separable freedom
requires:
  - cross-layer-separable-modifications-kill-quantum-rigidity
  - wall-chamber-distance-sfts-are-quantum-rigid
distinct_from:
  wall-chamber-distance-sfts-are-quantum-rigid: that proves quantum rigidity by nested chains of projections; item 1 here is its classical shadow, the necessary condition proved directly on points.
  cross-layer-separable-modifications-kill-quantum-rigidity: that is the test; this runs it on the rigid-seed constructions behind CARRIER.
---

**ESTABLISHED** for items 1 and 2 (lane bh-free-09, 2026-09-18; elementary, not reviewed; no priority
claimed). Items 3 and 4 are an **audit**.

*Passing at scale `D`* means that no point has two modifications whose difference sets are more than
`2D` apart. By item 3 of `cross-layer-separable-modifications-kill-quantum-rigidity`, a `D`-rigid SFT
passes at scale `D`.

## Theorem

1. **Wall seeds.** Let `Y_R` be the distance-gradient SFT of `wall-chamber-distance-sfts-are-quantum-rigid`,
   with `R >= 2r_0 + 2`. Any two modifications of one point have difference sets within distance
   `r_0 + 2`. So `Y_R` passes at every scale `D` with `2D >= r_0 + 2`. This covers closed surface
   groups, every group acting simply transitively on the vertices of a CAT(0) cube complex (RAAGs,
   RACGs, `Z^n`, `F_n`), and their products.
2. **Products.** If `Y_i` passes over `A_i` (`i = 1, 2`), then `Y_1 ⊠ Y_2` passes over `A_1 × A_2`.
   A modification changing factor `i` differs on `Δ_i × A_j`. Two such sets for the same factor are as
   far apart as the `Δ_i`, and sets for different factors cross.
3. **Gluings (audit).**
   - *Relative-seed gluing* (`relative-seeds-glue-graphs-of-groups-into-class-c`) and induction preserve
     passing. A glued point has a unique sink coset or a unique end. Every modification either moves the
     sink along a path through the old sink coset, moves the end along a tail of the old ray, or changes
     the seedless configuration inside the sink coset. The first two kinds share the old sink or a tail;
     the third reduces to the vertex seed itself.
   - *Kurosh tower seeds* (`kurosh-relative-seeds-and-the-b1-digit-splitting`, §§1–3). Hence they pass
     whenever their vertex seeds do, since they are built only from gluing, products (P) and
     conjugation (Cj).
4. **Building seeds (audit, not a proof).** These are the `Ã₂` phase seed
   (`a2-lattices-carry-finite-type-seeds`, `a2-lattice-phase-seeds-are-quantum-rigid`) and the `C̃₂`
   seed (`c2-building-lattices-carry-finite-type-seeds`). No separable pair was found.
   - *The computation.* In the apartment model (corners `Z²`, `ℓ¹` metric), the boundary fields are
     `±x_1 ± x_2` and `±x_1 + |x_2 − c|` (and their transposes). A distance-gradient field has no local
     maximum (source), so every modification of a boundary field creates or moves a sink, or moves an
     offset `c`.
   - *What the modifications look like.* They flip edges only in half-planes on the side of the
     field's point at infinity: `{x_2 > c}` or `{x_1 > c'}` for `−x_1 − x_2`. Offset moves flip a strip
     bordered by the old row `c`.
   - *Why that is safe.* Same-side half-planes always meet, and strips share row `c`.
   - *The general principle.* **A boundary field's freedom points toward its own limit point.**
   - *Where to look for a failure.* The building configurations not visible in one apartment: the
     wall-stratum fields toward a vertex `ξ` at infinity, when a modification changes `ξ` to a vertex
     whose wall line shares the opposite ray with the old one. These are the same "two walls of
     opposite types" configurations that the `Ã₂` node leaves open for gluing.

## Proof of item 1

- **Points are wall orientations.** In every point, the dual edges of a wall are oriented alike. By
  (W1), opposite orientations in one face are a non-occurring pattern, and the dual edges are connected
  through faces. So a point is an orientation of `𝒲`, and a modification flips a nonempty set `𝒮` of
  walls. Its difference set contains the carrier of each flipped wall and lies in the union of those
  carriers.
- **Easy cases.** Let `x_1, x_2` flip `𝒮_1, 𝒮_2`, and pick `W_i ∈ 𝒮_i`. If `W_1 = W_2`, or the walls
  cross, or their dual edges are within `r_0`, the difference sets are within `r_0`.
- **Chain orientations switch once.** Otherwise, take the nested chain `V_0 = W_1, …, V_n = W_2` of
  Step 3 of `wall-chamber-distance-sfts-are-quantum-rigid`. Write `s_i = +` when `V_i` points to the side
  containing `W_2`, and `−` otherwise. "`s_i = −`, `s_(i+1) = +`" is a non-occurring pattern visible in
  one `R`-ball, so in every point `s` has the form `+^k −^(n+1−k)`.
- **Where two points differ on the chain.** Two such sequences with switches `k, k'` differ exactly on
  the interval `[min(k, k'), max(k, k'))`.
- **The flipped chain walls are intervals.** Let `k` be the switch of `x`. The flipped chain indices
  `I_1 ∋ 0` and `I_2 ∋ n` are then intervals with an endpoint at `k`, giving three cases.
  - *`1 <= k <= n`.* `I_1 = [0, k)` and `I_2 ∋ k`. So `V_(k−1) ∈ 𝒮_1` and `V_k ∈ 𝒮_2` are consecutive,
    and their carriers are within `r_0` by (W3).
  - *`k = n + 1`.* `I_1 = [0, n] ∋ n`, so `V_n` is flipped by both.
  - *`k = 0`.* `I_2 = [0, n] ∋ 0`, so `V_0` is flipped by both.
- **Conclusion.** In every case the difference sets are within `r_0 + 2`. `∎`

## Lesson for general BH

- **Separable freedom never appears in the rigid-seed constructions behind CARRIER.**
  - *In distance-gradient (horofunction) seeds* every freedom of a point is a sink moving toward that
    point's limit, so any two freedoms share a tail or a switch.
  - *Gluings* inherit this through their unique sink or end.
  - *Products* inherit it because slabs cross.
- **The one structural risk left.** It sits where a boundary field can be changed in two opposite
  directions at infinity. The candidates are the building wall strata with lines of opposite type, and
  that is the configuration to settle before claiming rigidity of the `Ã₂` or `C̃₂` seeds.
