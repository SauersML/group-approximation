---
rg: 2
id: jacobson-finite-weyl-and-boundary-splitting-proof
kind: route
title: Split the finite boundary factor and conjugate the defect into the common root direction
target: jacobson-coherence-defect-is-an-orthogonal-translation
requires:
  - jacobson-stable-letter-closes-boundary-recursion
  - jacobson-shift-literal-quotient-is-laurent-times-z
  - jacobson-shift-head-dies-in-amenable-targets
artifacts:
  - research/artifacts/jacobson-missing-laurent-coherence-word-and-finite-cell-countermodel-2026-09-08.md
---

Sections 1--2 of the artifact authenticate the boundary factor in
`C_0`, split `v=v_0 v_1` in `C_0 x C_far`, and use exact
finite-table commutations to obtain `E=e_P v_0^(-1)`. The literal
operator calculation puts `E` in `ker(pi)`. The established
kernel comparison and centralizer equality give the stated
centralization and the equivalence of its vanishing with that
of the quotient word.

Section 4 uses the two actual finite Weyl tables to write
`v=(h s h)c(h s h)` and `r=(s q s)c(s q s)`. Substitution
gives the displayed conjugate commutator. The local and mixed
Weyl braids make `h s q s` and `q h s h` commute and show
that their ratio `t_0` commutes with `s`. Its Laurent diagonal
is calculated directly.

Section 5 proves the conditional finite-packet completion.
Assuming `q v q=d`, the two Weyl elements permute the six
specified roots coherently. Their conjugates of the mixed cell
give every finite-field Steinberg relation. The finite-field
presentation in Steinberg, Section 6, Theorem 9, gives the
claimed finite quotient, and its Laurent image proves faithfulness.
No infinite-group spectral or invariant-vector theorem is used.
