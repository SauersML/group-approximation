---
rg: 2
id: forced-descent-seeds-pass-the-separability-test
kind: claim
title: In a seed SFT with forced outward labels and one-step diamonds (the Ã₂, phase and C̃_n building seeds), every point has a cofinal descending ray, and any other point differs from it on a tail of that ray; so these seeds and all their subshifts pass the separability test at every scale, including the opposite-type wall-stratum configuration, and quantum rigidity reduces to one covering statement
---

## Proposed dependency record (not an accepted route)

The following rejected claim-level metadata is preserved verbatim as a
proposed dependency record. It is not a compiled route, does not establish
this claim, and requires individual mathematical review before any route
is accepted. The historical mathematical prose below is unchanged.

```yaml
requires:
  - a2-lattices-carry-finite-type-seeds
  - cn-building-lattices-carry-locally-forced-seeds
  - rigid-seed-constructions-pass-the-separability-test
  - cross-layer-separable-modifications-kill-quantum-rigidity
```

**ESTABLISHED** (lane proof, bh-invent-13, 2026-09-19; elementary; not reviewed): Theorems A and B.
**OPEN:** the covering statement (COV) of §3, which implies quantum rigidity here.

## 1. Descent structures

`Y` is a subshift over the vertex set `V` of a locally finite graph with a free cocompact `Γ`-action. A
*descent structure* assigns to every `η ∈ Y` a relation `→_η` on adjacent vertices, read off the label at the
source, such that:
- **(D0) Potential.** There is `f_η : V → Z` with `f_η(w') = f_η(w) − 1` whenever `w →_η w'`. In particular `→_η` has
  no directed cycles. Write `U_η(w)` for the set of descendants and `Out_η(z) = {w : z ∈ U_η(w)}`.
- **(D1) Forcing.** For every `z`, the set `Out_η(z)` and the restriction `η|_{Out_η(z)}` are functions of `η(z)`.
  They are the same for every `η ∈ Y` with that label at `z`.
- **(D2) Diamonds.**
  - If `x → a` and `x → b` with `a ≠ b`, there is `u` with `a → u` and `b → u`.
  - Adjacent `w, w'` have a common descendant at depth `≤ 2` below each.
  - A vertex has no descendant only if its label is the seed letter `*`.
- **(D3) Seed.** A point with `*` at `o` is the only point of `Y` with that value at `o`.

**Instances.**
- The `Ã₂` seed `Y_Γ` and its phase seeds `Y_Γ^(N)`: `a2-lattices-carry-finite-type-seeds`, Steps 1–4 and 7.
- Every `C̃_n` seed (`n ≥ 2`): `cn-building-lattices-carry-locally-forced-seeds` (items 1–3, Descents). There all of
  `St(S)` descends in one step to `g''`.

In both, `→` means "inward neighbour". (D0) holds because the points are limits of normalized distance functions
(S3), and `d(·,o)` drops by exactly 1 along inward steps (Step 0 tables).

## 2. Theorem A: freedom points toward the point's own limit

Let `η ∈ Y` contain no `*`.
1. **Cofinal rays.** There is an infinite path `R = (x_0 → x_1 → …)` with `⋃_k Out_η(x_k) = V`.
2. **Tails.** Every `η' ∈ Y` with `η' ≠ η` differs from `η` at all but finitely many `x_k`.
3. **Separability.** Any two modifications `η_1, η_2 ≠ η` have intersecting difference sets. Points with a `*`
   also have that property, because by (D3) every modification differs at the seed site. So `Y`, and every subshift
   of `Y` (in particular the perfect boundary `∂Y`), passes the separability test of
   `cross-layer-separable-modifications-kill-quantum-rigidity` at every scale.

**Proof.**
- **Part 1.**
  - *Transitivity.* `Out(x) ⊆ Out(y)` whenever `y ∈ U(x)`, by transitivity of descent.
  - *Construction.* Take any `z_0`, and balls `B_1 ⊆ B_2 ⊆ …` about `z_0` with union `V`, where `B_{j+1}` is chosen
    after `z_j` and contains it. Given `z_j`, choose a common descendant `c` of `B_{j+1}`.
    - It exists by (D2): adjacent pairs have common descendants, and one-step diamonds make descendants of one
      vertex confluent. So finite connected sets have common descendants (the Step 4 argument of the parents).
    - Let `z_{j+1}` be `c` if `c ≠ z_j`, and otherwise a proper descendant of `c`, which exists because there is
      no `*`.
  - *The ray.* Join `z_j` to `z_{j+1}` by a descending path. By (D0) the concatenation `R` is an infinite simple path,
    and `Out(z_{j+1}) ⊇ B_{j+1}`.
- **Part 2.** Let `A = {k : η'(x_k) = η(x_k)}`.
  - If `k ∈ A`, then (D1) gives `η' = η` on `Out_η(x_k)`, and that set contains every `x_j` with `j ≤ k`. So `A` is an
    initial segment.
  - If `A` were infinite, `η'` would equal `η` on `⋃_k Out(x_k) = V`.
- **Part 3.** Both difference sets contain a tail of the same ray `R`. Modifications inside a subshift are
  modifications in `Y`. ∎

**The flagged configuration** (`rigid-seed-constructions-pass-the-separability-test`, item 4).
- Take a wall-stratum field toward a vertex `ξ` at infinity, and a modification toward `ξ'`, where the wall line
  of `ξ'` shares the opposite ray.
- That modification agrees with the field upstream, on the shared ray side, and differs downstream.
- So its difference set contains a tail of the field's cofinal ray, which runs down the sink ray toward `ξ`. So
  does the difference set of every other modification.
- The configuration is therefore harmless. The audit's principle, "a boundary field's freedom points toward its own
  limit point", is Theorem A.2. No stratum description is needed: (D1) and (D2) suffice.
- For `Ã₂` this is also proved by bh-free-09, stratum by stratum (2a9cd8317, revised
  `a2-phase-seed-passes-the-separability-test`; strata in `a2-seed-boundary-is-chambers-and-panel-tree-pointers`,
  7d0b8309d). Theorem A is an independent, strata-free proof. It covers every `C̃_n` seed directly, without the
  direction lemma and rank induction that a stratum proof would need there.

## 3. Theorem B: the quantum shadow, and what rigidity still needs

Fix a `D`-family `(E_a(v))` for `Y` (Q1–Q3 of `fp-v-times-subshift-full-groups-force-quantum-rigidity`), with `D ≥ 2`.
For a label `a` at `z` and `w ∈ Out_a(z)`, write `F_a(w)` for the forced label at `w`.

1. **Domination.** `E_a(z) ≤ E_{F_a(w)}(w)` for every `w ∈ Out_a(z)`, i.e. `E_a(z)E_F(w) = E_F(w)E_a(z) = E_a(z)`.
2. **Local annihilation.** Let `N = [E_b(q), E_{b'}(q')]`. If `q, q' ∈ Out_a(z)`, then `N E_a(z) = 0 = E_a(z) N`.
3. **Uniform depth.** If `d(q,q') = L`, every point of `Y` has a common descendant `z` of `q` and `q'` with
   `d(q,z) ≤ 4L + 2`.

**Proof.**
- **1.** Let `v'` be outward from `v` under the label `a`, and `c ≠ F_a(v')`.
  - No point of `Y` has `a` at `v` and `c` at `v'` (D1). So every `D`-pattern extending that pair is missing.
  - Summing (Q3) over the extensions, whose letters commute by (Q2), gives `E_a(v)E_c(v') = 0 = E_c(v')E_a(v)`.
  - Hence `E_a(v) ≤ E_{F}(v')`. Chain this along an outward path from `z` to `w`; `≤` is transitive.
- **2.** By 1, `E_b(q)E_a(z) = [b = F_a(q)] E_a(z)`, and the same holds at `q'` and on the other side. Both products
  in `N E_a(z)` therefore equal `[b = F_a(q)][b' = F_a(q')] E_a(z)`.
- **3.**
  - Let `q = w_0, …, w_L = q'` be a path. Let `c_j` be a common descendant of `w_{j−1}, w_j` at depth `≤ 2` (D2).
  - One-step diamonds tile descending paths of lengths `m` and `n` from one vertex, giving a common descendant at
    depth `≤ m + n`.
  - So the common descendant `z_j` of `w_0, …, w_j` can be taken at depth `δ_j` below `w_j`, with `δ_{j+1} ≤ δ_j + 3`.
  - Then `d(q, z_L) ≤ f(q) − f(z_L) ≤ L + δ_L ≤ 4L + 2`. ∎

**The reduction.**
- By B.2, `N` vanishes on the span of the ranges of the *admissible* idempotents `E_a(z)`, those with
  `q, q' ∈ Out_a(z)` and `z ∈ B_{4L+2}(q)`. By B.3 every classical point sees one of them.
- So `Y` is `D`-quantum rigid as soon as the following holds:

  > **(COV)** For all `q, q'`, the ranges of the admissible `E_a(z)` span the representation space.
- (COV) is automatic when all the admissible `z` lie in one `D`-ball. The event "no admissible `z`" is then a
  missing pattern. But that case only covers pairs already handled by (Q2).
- For far pairs, (COV) must be built from a chain of commuting covers. The window-chain lemma of
  `hyperbolic-groups-lie-in-the-rigid-compactification-class` is the model, with "`q ∈ Out(c_i)`" as the event.
  - In flats, drop events along a general geodesic have flat stretches, and (K2) fails there.
  - In the `C̃_n` apartment, genuine distance functions are exactly V-shaped along the diagonal lines, with step
    `e ∈ {±½}^n` (`2‖·‖_∞` is `|s − s_0| + c` there). This is the candidate backbone for the chains. Whether that
    persists in the building, when the origin is not in an apartment with the line, is the first thing to check.

## Lesson for general BH

- For forced seeds, separable freedom is impossible for a structural reason. Outward labels are forced, so agreement
  at one vertex propagates to everything upstream of it. Confluence gives every point a cofinal descending ray, and
  so any two changes of a point must both reach down that ray's tail.
- This settles the separability audit for all `Ã₂` and `C̃_n` building seeds, and the opposite-type wall
  configuration in particular, with no stratum-by-stratum analysis.
- The quantum shadow is equally clean. A label at `z` dominates every forced letter upstream, so it annihilates the
  commutator of any two upstream letters.
- Quantum rigidity of these Kazhdan seeds therefore follows from one covering statement, (COV). It must be proved
  across flats, where the hyperbolic drop chains lose (K2). Diagonal (special-vertex) lines, along which distance is
  V-shaped, are the natural rails.
