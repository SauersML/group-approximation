---
rg: 2
id: fibre-products-over-b-a-quotients-proof
kind: route
title: P is the preimage of the diagonal of Q x Q, which is a retract; the word problem of the lamplighter decides the word problem of Q
target: fibre-products-over-b-a-quotients-lie-in-cr
requires:
  - pbh-coset-wreath-subgroups-closure-properties
  - pbh-coset-wreaths-iff-identity-edge-hnns
  - boone-higman-type-a-class-closed-under-finite-extensions
  - pbh-wreath-closure-fails-over-undecidable-stabilizers
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

Direct proof (2026-09-18, lane bh-openq-papers). Not independently reviewed.

**1. Positive.**
- `Q × Q ∈ B_A` and `F × F ∈ B_A`, as finite products
  (`boone-higman-type-a-class-closed-under-finite-extensions`).
- The diagonal `Δ_Q = {(q,q)}` is a retract of `Q × Q`, via `(q_1, q_2) ↦ (q_1, q_1)`. So
  `Δ_Q ∈ CR(Q × Q)` by case 3 of `pbh-coset-wreaths-iff-identity-edge-hnns`.
- `P = (φ × φ)^(-1)(Δ_Q)`, so `P ∈ CR(F × F)` by part 3 of
  `pbh-coset-wreath-subgroups-closure-properties`.
- The listed groups come from conditions (b) and (c) of the equivalence, and the double from
  Britton's lemma inside `(F × F) *_P (P × Z)`, as in `virtual-retracts-satisfy-pbh-coset-wreath-closure-proof`,
  item 1.

**2. Negative.**
- Let `S` generate `F`. For a word `w` in `S^(±1)`, `(w, 1) ∈ P` iff `φ(w) = 1`. So membership in
  `P` decides the word problem of `Q` on the generators `φ(S)`, and is undecidable.
- By item 2 of `pbh-wreath-closure-fails-over-undecidable-stabilizers`, which is stated for
  any finitely generated `G` and any `C ≤ G`, the word problem of `Z/2 ≀_{(F×F)/P} (F × F)` would
  decide membership in `P`.
- That lamplighter is finitely generated, so it is not in `B_A`
  (`type-a-action-gives-boone-higman-for-subgroups`). By the equivalence (a) ⇔ (e),
  `P ∉ CR(F × F)`.

**Finite generation of `P` (standard).**
- Let `D = ⟨(g,g), (r_j,1)⟩ ≤ P`.
- For `(g, h) ∈ P`, write `(g, h) = (gh^(-1), 1)(h, h)`. Here `gh^(-1) ∈ ker φ`, the normal
  closure of the `r_j`.
- Each conjugate `(u r_j u^(-1), 1) = (u,u)(r_j,1)(u,u)^(-1)` lies in `D`. So `P = D`. ∎
