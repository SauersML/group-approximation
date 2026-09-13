---
rg: 2
id: bauer-unit-division-iff-summable-local-division-proof
kind: route
title: Run the staircase-and-move construction over any summable family of local divisions, and localize by compactness and property C screening
target: bauer-unit-division-iff-summable-local-division
requires:
  - strict-comparison-unit-divisibility-equivalences
artifacts:
  - research/artifacts/ex-tw-c-space-unit-division-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part2-2026-09-13.md
  - research/artifacts/ex-tw-c-space-unit-division-part3-2026-09-13.md
---

Full proof: Section 6 of the part 3 artifact, using Lemmas 1 and 3 of part 1 and
Section 3 of part 2.

**(a) ⟹.** A tracially large order zero `M_N → A` with `N ≥ 4/ε²` gives the ε-summable
family consisting of `K` alone.

**(a) ⟸.** Use one level per member of an `ε/14`-summable family covering `K`, with a
partition of unity `supp h_i ⊆ O_i`.
- **Pieces.** Each piece is a central staircase with rank within `t h_i ± O(ω_i)` where
  it is active, and below `8η/s_min` elsewhere.
- **Moves.** Strict comparison and Rørdam's lemma move each piece into the exact
  orthogonal complement of the earlier pieces. The rank margin stays at least `1/8`.
- **Result.** Active errors at `λ` sum to at most `8 Σ_{i ∋ λ} ω_i`. The final orthogonal
  sum has rank within `γ` of `t` at every trace.
- **Division.** Item 3 ⟹ item 1 of `strict-comparison-unit-divisibility-equivalences`.

**(b).** The complement of `Z_sum` is open by definition.
- If the unit divides, `K` is summably divisible by (a).
- Conversely, suppose `Z_sum = ∅`. Pick finitely many summably divisible closed
  neighbourhoods, `m` of them, whose interiors cover `K`. Their `ε/m`-summable families
  combine into an ε-summable family covering `K`.

**(c).**
- Screen the covers of `Y` at precisions `ω_k = ε 2^{−k}` by property C.
- Shrink finitely many members to closed sets, and separate each level by disjoint open
  sets of `K` inside division sets.
- At most one set per level contains any point, so the weights there sum to at most `ε`.

**(d).** Suppose `λ ∈ Z_sum` has a closed C-neighbourhood `F` in `Z_sum`. Take an open
`B ∋ λ` with `cl B ∩ Z_sum ⊆ F`.
- **Cover `F`.** By (c), `F` has an ε-summable cover with union `G`.
- **Cover the rest.** The compact set `cl B ∖ G` misses `Z_sum`, so `m` summably divisible
  closed sets cover it. Take `ε/m`-summable families for them.
- **Combine.** The union covers `cl B` and is `2ε`-summable. So `λ ∉ Z_sum`, a contradiction.
- **C-kernel.** Property C passes to closed subspaces, so a set equal to its own
  non-C-point set lies in every stage of the transfinite C-derivation of `K`. ∎
