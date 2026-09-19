---
rg: 2
id: thompson-f-second-test-function-costs-more-than-any-tower
kind: claim
title: In Thompson's F, the coarse Reiter radius, which equals the two-test-function fine Ramsey radius up to bounded towers, is not bounded by any bounded tower around the one-test-function fine Ramsey radius (SFG)
distinct_from:
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is ¬AMP, the one-function radius ψ against the set radius R; this is CR against ψ. Both imply RGAP₁, and RGAP₁ is exactly their disjunction.
  thompson-f-ramsey-radius-single-gap-below-reiter-radius: that is RGAP₁, CR against R; this is the stronger statement with R replaced by ψ ≥ R.
  ramsey-functions-are-pairwise-reiter-radii: that defines PGAP_c at a fixed threshold c; this is the vanishing-threshold form, CR against PR_{2/t}(t), and it implies PGAP_1.
  thompson-f-ramsey-radii-in-the-elementary-degree-order: that is the established bookkeeping; this is the open gap it isolates.
---

**OPEN.** Notation is as in `thompson-f-ramsey-radii-in-the-elementary-degree-order`: `ψ(t) = R̃_{F,S}(t, 1/t)`,
the fine Ramsey radius with one test function, and `CR` the coarse Reiter radius, with `S = {x_0, x_1}`.

**Statement (SFG).** For every integer `E ≥ 0` there is an integer `M ≥ 1` with

`CR(M) > exp_E(ψ(exp_E(M)))`.

**Equivalent forms**, all by `thompson-f-ramsey-radii-in-the-elementary-degree-order`:
- *Two functions against one.* `ψ_2 ⋠ ψ`, where `ψ_2(t) = R̃(t, 1/t, 2)`, since `ψ_2 ≈ CR`.
- *Pairs.* `CR ⋠ (t ↦ PR_{2/t}(t))`. Every single pair `α, β ∈ P(B_t)` can be brought within ℓ¹-distance `2/t` by
  some measure of window `n` non-elementarily earlier than one measure becomes coarsely invariant under `B_M`.

**A consequence (not an equivalent form).** Since `CR ≼ ψ∘ψ`, SFG implies `ψ∘ψ ⋠ ψ`. The composition in Towsner's
inequality `R̃(m, ε, 2) ≤ R̃(R̃(m, ε), ε)` is then not absorbed by bounded towers. In particular `ψ` is not bounded
by a fixed tower: `ψ ≤ exp_k` would give `ψ∘ψ ≤ exp_k∘ψ`, so `ψ∘ψ ≼ ψ`.

**It implies amenability of F** (clause 5 of the degree-order node). A proof of SFG is a proof of
`thompson-f-is-amenable`, through the route `thompson-f-single-ramsey-reiter-gap-via-second-test-function-gap`
followed by `thompson-f-amenable-via-single-ramsey-reiter-gap`.

**It can fail on its own.** Its negation SFC (`CR ≼ ψ`) says nothing about `R`, and it holds in every group whose
coarse Reiter radius is bounded by a fixed tower. SFC also holds vacuously if `F` is not amenable. SFG and ¬AMP are
logically independent as far as is known. Consider the case where AMP holds, so `ψ ≈ R`. Then SFG is equivalent to
RGAP₁. So SFG is the route to the root that survives if Ramsey precision amplification turns out to be cheap in `F`.

**Why this is not ¬AMP in disguise.** ¬AMP asks one test function at fine precision to be much harder than a set at
precision 1/2. SFG asks two test functions to be much harder than one, at the same fine precision. The first is a
precision question and the second a multiplicity question. The sandwich showed precision is free for *measures*.
SFG asks whether multiplicity is free for *Ramsey balances*. By minimax (pair identity), one function is one pair
`(α, β)`. Two functions are a weighted family of two pairs, and in particular include the two generator point pairs
`(δ_{x_0}, δ_e)` and `(δ_{x_1}, δ_e)` jointly. Joint point pairs are Reiter invariance. Single point pairs are
free at window `9m` by Cesàro averaging (clause (D) of the pair identity).

**Known obstructions to refuting it (that is, to proving SFC).** Encoding two test functions as one is the
selector coding of the quantifier swap. Its death is recorded on `thompson-f-ramsey-radius-double-gap-below-reiter-radius`
(w9-f-last1): the one-function measure may choose a different conditional push-forward for each encoded function.
Encoding two pairs as one marked pair is marker coding, which dies at the pigeonhole `c_{g'}⁻¹c_g ∈ XX⁻¹` (w10-f-last1).
Both kills apply here with the same invariant and at the same step. SFC is the two-function case of the packing those
kills address, which otherwise involves `|B_M|` point pairs.
