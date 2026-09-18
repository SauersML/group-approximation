---
rg: 2
id: quantum-rigid-sfts-over-products-have-a-single-free-branch
kind: claim
title: Over a product with a multi-ended factor, a quantum rigid SFT is determined by any thick slab except on one branch, so it is a near-deterministic spacetime of that factor acting on a fibre shift
distinct_from:
  minimal-sfts-with-a-finite-modification-are-not-quantum-rigid: that forbids finitely supported modifications of minimal shifts over any group; this constrains infinite modifications across the slabs of a product with a multi-ended factor, with no minimality hypothesis.
  v-times-golden-silver-wang-product-full-group-is-not-fp: that exhibits two independent faults in one uncoupled product; this proves that across every slab of a multi-ended factor all faults except those in a single branch are forbidden.
  decidable-groups-embed-in-fp-groups-with-minimal-free-sft: that is the existence premise P1 over envelopes Λ = Λ_0 × H; this is a necessary structure theorem for the rigidity crux over such envelopes.
artifacts:
  - research/artifacts/gq-bh-bh-g2-obstruct-kill-attempt.md
---

**ESTABLISHED (lane proof, elementary, unreviewed; no priority claimed).** A consequence of the
far-modification Lemma of `minimal-sfts-with-a-finite-modification-are-not-quantum-rigid`.

## Setting

Let `Λ = Λ_0 × H` with `Λ_0` and `H` finitely generated. Take the word metric for `S_0 ∪ S_H`, so
`d((λ,h),(λ',h')) >= d_H(h,h')`. Let `X ⊆ A^Λ` be an SFT with forbidden patterns in `B_r`, and let
`D >= r`.

Let `S ⊆ H` be finite such that `H \ S` has components `C_1, …, C_m` with `m >= 2`. Fix `w >= 2D`.
- The *deep branches* are `C_i^w = {h ∈ C_i : d_H(h, S) > w}`.
- The *slab* is `M = Λ_0 × N_w(S)`.

Then `H = N_w(S) ⊔ C_1^w ⊔ … ⊔ C_m^w`, and `d(C_i^w, C_j^w) >= 2w + 2 > 2D` for `i != j`, because
every path between them crosses `S`.

## Theorem

If `X` is `D`-quantum rigid over some field, then every pattern `s` on `M` that occurs in `X` has an
index `i(s)` such that all extensions of `s` in `X` coincide outside `Λ_0 × C_(i(s))^w`.

*Proof.*
1. **Splitting off one branch.** Let `y, y' ∈ X` extend `s`. Let `y_i` be `y'` on `Λ_0 × C_i^w` and
   `y` elsewhere.
   - An `r`-ball meeting `Λ_0 × C_i^w` lies in `Λ_0 × (C_i ∪ N_w(S))`, because `w >= 2r`.
   - On `Λ_0 × (C_i \ C_i^w) ⊆ M` we have `y = y' = s`, so on such a ball `y_i = y'`.
   - Every other `r`-ball reads `y`. So `y_i ∈ X`.
2. **Two branches are impossible.** If `Δ(y, y')` met two deep branches `i != j`, then `y_i` and
   `y_j` would be modifications of `y` supported in `Λ_0 × C_i^w` and `Λ_0 × C_j^w`. These are at
   distance `> 2D`, so the far-modification Lemma refutes rigidity.
3. **All extensions share the branch.** If `y'` and `y''` differ from `y` in different single deep
   branches, the same Lemma applies with base `y`. ∎

## Corollaries

- **(a) `H = Z` (envelopes `Λ_0 × Z`, and `Z^2`).** Take `S = {0}`. Every slab state on
  `Λ_0 × [-w, w]` has a unique extension to the upper half or a unique extension to the lower half.
  - For `Z^2` this holds across every lattice line, since `Z^2 ≅ Z × Z` in any basis.
  - So rigid `Z^2`-SFTs are one-sidedly deterministic across every lattice-line band. This is the
    permutive picture, and it explains why the known rigid shifts, Ledrappier's and the
    permutive-triangle ones (`permutive-triangle-sfts-are-quantum-rigid`), are cellular-automaton
    spacetimes.
- **(b) `H` virtually free and non-elementary (`F_2`, `PSL_2(Z)`).** Take `S` to be any finite
  subtree. Among the many deep branches, at most one can vary once the slab is fixed.
- **(c) Two multi-ended factors (`F_2 × F_2`).** Apply the theorem in each factor, or directly to the
  cross `(Λ_1 × N_w(S_2)) ∪ (N_w(S_1) × Λ_2)`. Its complement splits into quadrants
  `C_i × C'_j` that are pairwise at distance `> 2D`, and extensions of a cross state vary on at most
  one quadrant.
- **(d) Tight slabs give a spacetime structure.** Suppose every occurring `M`-state has a unique
  extension.
  - Restriction `x ↦ x|M` is then a conjugacy of the `Λ_0`-action onto a `Λ_0`-subshift
    `Y ⊆ (A^(N_w(S)))^(Λ_0)`.
  - Each `h ∈ H` acts by `x|M ↦ (h^(-1).x)|M`. This is a continuous bijection commuting with
    `Λ_0`, hence an automorphism `ψ_h` of `Y`.
  - So `X` is the spacetime of `H` acting by automorphisms on the fibre shift `Y`.
  - If `X` is free, `Y` is a free, that is strongly aperiodic, `Λ_0`-subshift. Moreover
    `σ_λ ∘ ψ_h` has no fixed point for `(λ, h) != 1`. All aperiodicity is carried by the fibre.
- **(e) Where more rigidity could come from (heuristic, not proved).** In the tight case, the
  operators of a quantum family at `(λ, h)` are ball-local polynomials in the fibre operators. Their
  spread grows with `|h|`.
  - Commutation at every `h` therefore couples fibre operators at `Λ_0`-distance up to about `|h|`.
  - For non-amenable `H` there are exponentially many such couplings.
  - This propagation of commutation along the automorphisms `ψ_h` is the only mechanism, beyond
    rigidity of `Y` itself, by which the `H` factor can create rigidity. Its `Z` case is permutive
    propagation.

## Lesson for general BH

Take the master route's recommended non-amenable envelopes `Λ_0 × F_2`, or `Λ_0 × Z^2`, and
`F_2 × F_2`.
- **What rigidity forces.** First-order rigidity alone forces the multi-ended direction to be almost
  deterministic. Off one branch per slab, a rigid free SFT is the spacetime of that factor acting by
  automorphisms on a `Λ_0`-shift. In the tight case, that shift must carry all the aperiodicity.
- **What this rules out.** Taking a product with `F_2` for compression does not by itself create a
  rigid free SFT. The free factor can only transport rigidity from the fibre, or propagate it through
  expansive automorphisms.
- **Where to start.** Designers of the crux object over such `Λ` should begin with an `F_2`-action by
  automorphisms on a strongly aperiodic `Λ_0`-subshift whose spacetime is of finite type. The aim is
  commutation propagating along the automorphisms, which is the non-amenable analogue of Ledrappier
  and permutive triangles.
- **What still escapes the theorem.** Uncoupled products with independent faults are excluded: this
  generalizes the golden–silver lesson. Coupled hierarchies that change the free branch from slab to
  slab are not.
