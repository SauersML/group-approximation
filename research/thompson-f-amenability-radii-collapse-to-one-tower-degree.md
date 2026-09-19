---
rg: 2
id: thompson-f-amenability-radii-collapse-to-one-tower-degree
kind: claim
title: In Thompson's F the Ramsey radius, the one- and many-test-function fine Ramsey radii, the coarse Reiter radius and the Følner function are all equivalent up to bounded towers, so every gap statement between them is false
distinct_from:
  thompson-f-ramsey-radii-in-the-elementary-degree-order: that places R ≼ ψ ≼ CR ≈ ψ_l in one preorder and leaves the two gaps ψ ⋠ R and CR ⋠ ψ open; this proves the preorder collapses to a single class and adds the Følner function to it.
  thompson-f-coarse-reiter-radius-is-one-ramsey-call-away: that proves CR ≼ R by a self-wreath coding; this combines it with the degree order and two elementary Følner lemmas to get the full collapse, and derives SFC, the negation of the second-test-function gap, which that node does not state.
  thompson-f-second-test-function-costs-more-than-any-tower: that is SFG, CR ⋠ ψ; this refutes it.
  thompson-f-folner-function-dominates-every-ackermann-level: that is the open primitive-recursive question for the Følner function; this shows it is the same question for the Ramsey function and every other radius in the family, and does not settle it.
  thompson-f-folner-function-exceeds-every-tower: that is Moore's absolute lower bound for Følner sets; this is a relative statement, and imports that bound only to note that no radius in the family is elementary.
---

**ESTABLISHED** by `thompson-f-amenability-radii-collapse-proof`. It is a short deduction from two established
nodes (`thompson-f-coarse-reiter-radius-is-one-ramsey-call-away`, `thompson-f-ramsey-radii-in-the-elementary-degree-order`)
plus two elementary Følner lemmas proved in full in the route (a connected-component lemma and the Namioka
layer-cake lemma, over `coarse-ball-invariance-gives-fine-reiter-measures`). It has not been independently reviewed.
The deep input is the one-Ramsey-call theorem; the rest is bookkeeping, and the point of this node is to record the
consequence for the graph exactly.

**Setting.** `S = {x_0, x_1}`, balls `B_r` in the word metric of `S ∪ S⁻¹`. Values lie in `[0, ∞]`, with
`exp_E(∞) = ∞`. Notation as in `thompson-f-ramsey-radii-in-the-elementary-degree-order`:
- `R(m) = R_{F,S}(m, 1/2)`, Moore's Ramsey radius;
- `ψ(t) = R̃(t, 1/t)` and `ψ_l(t) = R̃(t, 1/t, l)`, the fine Ramsey radii with one and with `l` test functions;
- `CR(M)`, the least `r` such that some `ν ∈ P(B_r)` has `‖gν − ν‖₁ ≤ 1` for all `g ∈ B_M`;
- `Føl(k)`, the least `|A|` over nonempty finite `A ⊆ F` with `|sA △ A| ≤ |A|/k` for both `s ∈ S`
  (`|s⁻¹A △ A| = |sA △ A|`, so the symmetric convention differs by a constant factor in `k` only).
- `φ ≼ χ` means `φ(x) ≤ exp_E(χ(exp_E(x)))` for some `E` and all `x ≥ 1`; `φ ≈ χ` means both ways.

**Theorem (collapse).**
1. **(SFC.)** `CR(N) ≤ exp_{E+1}(ψ(exp_{E+1}(N)))` for all `N ≥ 1`, where `E` is the constant of CRE(E) in the
   one-Ramsey-call node. So `CR ≼ ψ`.
2. **(Følner, lower.)** `CR(M) ≤ Føl(2M) − 1` for all `M ≥ 1`.
3. **(Følner, upper.)** `Føl(k) ≤ 5^{CR(1110k²) + 555k² − 1}` for all `k ≥ 1`, hence `Føl(k) ≤ exp_4(CR(exp_4(k)))`.
4. **(Collapse.)** `R ≈ ψ ≈ ψ_l ≈ CR ≈ Føl` for every `l ≥ 2`.

**Corollaries.**
- *Every gap is false.* For any two functions `φ, χ` of the family `𝓡 = {R, ψ, ψ_l, CR, Føl}`, the statement
  `φ ⋠ χ` is false. In particular each of the following is refuted:
  - SFG, `thompson-f-second-test-function-costs-more-than-any-tower` (`CR ⋠ ψ`), by clause 1;
  - ¬AMP, `thompson-f-ramsey-amplification-needs-unbounded-tower-overhead` (`ψ ⋠ R`);
  - RGAP₁, `thompson-f-ramsey-radius-single-gap-below-reiter-radius` (`CR ⋠ R`);
  - RGAP₂, `thompson-f-ramsey-radius-double-gap-below-reiter-radius` (it implies ¬AMP);
  - PGAP_1 of `ramsey-functions-are-pairwise-reiter-radii` (it implies RGAP₁).
- *Every absolute elementary bound is false.* If `F` is amenable, `Føl` eventually exceeds every `exp_p`
  (`thompson-f-folner-function-exceeds-every-tower`), and `≈` preserves "bounded by some `exp_p`", so no member of
  `𝓡` is elementary. If `F` is not amenable, every member of `𝓡` is eventually `∞`.
- *The primitive-recursive question is one question.* `≈` also preserves "eventually bounded by some Ackermann level
  `Ack_j`", since `exp_E ∘ Ack_j ∘ exp_E ≤ Ack_{j+2}` eventually for `j ≥ 3`. So
  `thompson-f-folner-function-dominates-every-ackermann-level` holds for `Føl` iff it holds for `R`, for `ψ`, for
  `CR` (and iff it holds for any other member of `𝓡`).

**Class kill (the invariant and the step where every member dies).** The invariant is the *tower degree*
`deg(F)`, the `≈`-class of `Føl_F`. Clause 4 says every radius in `𝓡` has degree `deg(F)`. Any route to
`thompson-f-is-amenable` whose open prerequisite asserts a strict gap `φ ≺ χ` between two members of `𝓡` (a
"quantitative Ramsey route") therefore dies at that prerequisite, and it dies whether or not `F` is amenable. Any
route that asks for an elementary or moderate bound on a member of `𝓡` dies by Moore's tower theorem, or is
vacuous. The only statements about `𝓡` that remain undecided are statements about `deg(F)` itself:
- whether it is finite, which is amenability of `F`;
- where it sits against the Ackermann hierarchy, which is the open primitive-recursive node.

So the Ramsey family contributes no decomposition of `thompson-f-is-amenable`. This holds for the Ramsey,
fine Ramsey, pair and coarse Reiter radii and for the Følner function alike, and it does not depend on which of them
a future route names. What makes F special is the self-wreath embedding `(F ≀ Z) × Z ≤ F` with linear coordinate
distortion used in the one-Ramsey-call theorem. In `F_2`, `R(1) = 3` while `CR(1) = ∞`, so the collapse is not a
formal property of all groups.
