---
rg: 2
id: free-products-with-z-carry-minimal-topfree-effective-subshifts
kind: claim
title: For every nontrivial finitely generated group A with solvable word problem, A * Z carries a minimal topologically free effectively closed subshift with no premise at all, so (D) is not needed on the topologically free route and (★𝒞) is exactly a rigid finite-type cover of this subshift
distinct_from:
  free-products-with-z-inherit-m2-from-decidable-free-subshifts: that needs premise (D) on A and yields a FREE minimal subshift of A * Z; this needs nothing and yields a TOPOLOGICALLY FREE one, which is all that master-route-needs-only-topological-freeness consumes.
  tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts: that glues rigid SFT compactifications into rigid SFTs; this runs the same gluing on the one-point compactification, which is effectively closed but not of finite type, and compares the two.
  strongly-proximal-geometries-are-disjoint-from-measured-inputs: its geometry B over Z/2*Z/2*Z/2 is the case of the tree gluing with finite vertex groups; with an infinite vertex group A the gluing carries the input itself.
---

**ESTABLISHED** (lane proof, bh-g2-buildings, 2026-09-18; not reviewed; no priority claimed. The
space is the Bowditch boundary of `A * Z` relative to `A`, an identification that is recalled and
not used. What is new is the observation about the premises.)

## Theorem

Let `A` be a nontrivial finitely generated group with solvable word problem, and let `Λ = A * Z`.
- Let `O_A ⊆ {0,1}^A` be the configurations with at most one `1`, with seed "`1` at the origin". When
  `A` is infinite, `O_A` is the one-point compactification of `A`.
- Let `X_B` be the subshift over `Λ` given by rules R1 and R3 of
  `tree-gluing-turns-rigid-sft-compactifications-into-rigid-sfts`, with `O_A` on the `A`-pieces and
  `C_Z` on the `t`-lines.

Then:
1. `X_B` is nonempty, minimal and topologically free;
2. `X_B` is effectively closed, and its language is decidable;
3. `X_B` has no `Λ`-invariant probability measure.

*Proof.*
- **Parts 1 (minimality and topological freeness).** Steps A, B and C of the tree-gluing proof use only
  two things: (C1) the seed cylinder is a single point with trivial stabilizer, and (C2) the space is
  the orbit closure of that point. They do not use finite type or rigidity. For `O_A`, (C1) holds
  with `y_* = δ_1`. (C2) holds because `δ_g -> 0` as `g -> ∞` when `A` is infinite. If `A` is finite,
  use the finite orbit `{δ_g}` instead.
- **Part 2 (effectivity).**
  - The forbidden patterns are: two `1`s in one `A`-piece, the `C_Z` pairs, and the R3 patterns at
    each element.
  - These are recursively enumerable, because pieces and balls are computable from the word problem
    of `A` via normal forms in `A * Z`.
  - A minimal effectively closed subshift has decidable language, as recorded in
    `decidable-groups-carry-free-subshifts-with-decidable-language` (Known instances).
- **Part 3 (no invariant measure).** Let `g` be hyperbolic on the tree `T`, with ends `ζ_±`.
  - For every `x ≠ ζ_−`, `g^n x -> ζ_+`. The out-path of `x` eventually agrees with an arbitrarily
    long segment of `g`'s axis toward `ζ_+`, and cylinders are determined by finitely many exits
    (Step B there).
  - So an invariant `μ` would be supported on `{ζ_+, ζ_−}`.
  - A second hyperbolic element with disjoint fixed ends then forces `μ = 0`. `∎`

## Consequences

**(a) Premise (D) is not needed on the topologically free route.**
- `master-route-needs-only-topological-freeness` shows that both master routes consume only
  topological freeness, plus torsion-free isotropy on the ring side.
- At the effectively closed level, the existence gate asks for a minimal topologically free
  effectively closed subshift on an fp overgroup of the input. Take the Clapham envelope `Λ_1` of the
  input (`clapham-fp-embedding-preserves-word-problem`). Then `X_B` on `Λ_1 * Z` is such a subshift,
  for every input, with no hypothesis.
- So `decidable-groups-carry-free-subshifts-with-decidable-language` and the universal-point premises
  are needed only for FREENESS. That is a condition the topologically free routes do not consume.

**(b) The E1′ chain without (D).**
- Take `Λ = (Λ_1 * Z)²` with input `X_B ⊠ X_B`, each coordinate constant along the other factor.
  This input is minimal, topologically free and effectively closed.
- **(MSS′)**: Barbieri–Sablik–Salo's `Q:minimal`, restricted to topologically free inputs. It is still
  a special case of the printed question that
  `nonamenable-products-have-minimal-sft-extensions-of-free-inputs` records. If it holds, it gives a
  minimal SFT `Z -> X_B ⊠ X_B`.
- `Z` is topologically free. A factor map between minimal systems is semi-open: finitely many
  translates of a closed `Ū` cover the space, so by Baire the image `π(Ū)` has interior. Hence an open
  set of points fixed by `g` in `Z` would map onto a set with interior fixed by `g` downstairs.
- So E1′ follows from (MSS′) alone. (D) and the universal point are no longer needed, and so is the
  step (D) ⇒ (M2).

**(c) What (★𝒞) is.**
- A rigid SFT compactification `(Y, π)` of `A` has the seed-indicator block code `Y -> O_A`. This
  code is onto and injective over each `δ_g`. The gluing is functorial, so it induces a factor map
  `X(Y) -> X_B` from the rigid SFT of the tree-gluing theorem onto `X_B`.
- That map is injective except over the sink points at `A`-pieces, where the fibre is `∂Y`.
- So (★𝒞) (`decidable-groups-embed-in-rigid-sft-compactification-groups`) says: the premise-free
  input `X_B` has a quantum-rigid, almost one-to-one SFT cover of tree-glued shape. It does this on
  `A * Z` itself, with no squaring. So it gives the conclusion of (MSS′) and gate E2 in one step.

**(d) Relation to the measured premise (M2μ).**
- The disjointness lemma of `strongly-proximal-geometries-are-disjoint-from-measured-inputs` needs an
  input with an invariant measure. `X_B` has none (Part 3), so that lemma cannot be applied with
  `X_B` as the input.
- Its geometry `B` over `W_3 = Z/2 * Z/2 * Z/2` is the tree gluing of finite vertex groups.
- So the two routes split the jobs differently:
  - (M2μ): the geometry and the measured input are separate factors, made jointly minimal by
    disjointness;
  - here: the geometry *is* the input carrier, since `A` sits in a vertex group, and minimality comes
    from the tree.
- Neither premise implies the other as far as this lane can see: (M2μ) asks for an invariant
  measure, and `X_B` has none.

## Lesson for general BH

On the topologically free route the existence side has no effectivity content left.
- Every decidable group lies in an fp group with a minimal, topologically free, effectively closed
  subshift: glue one-point compactifications along the free product with `Z`.
- What remains is FINITE TYPE: (MSS′) on squares, or (★𝒞) on `A * Z` directly. And, for E2, RIGIDITY.
  (★𝒞) is exactly "the one-point compactification has a rigid finite-type cover that is injective
  over the seed".
- Lanes working on (D), universal points or recurrence schemes are working on freeness, which the
  topologically free routes do not need.
