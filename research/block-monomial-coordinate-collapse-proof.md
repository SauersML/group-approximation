---
rg: 2
id: block-monomial-coordinate-collapse-proof
kind: route
title: Permutation parts survive the fiber; faithfulness is bought back by tensoring
target: block-monomial-coordinate-collapse
requires: []
artifacts:
  - notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md
  - research/artifacts/kun-thom-2608-06222-verified.md
---

# Permutation parts survive the fiber

Direct establishment. The complete argument — Lemma 1 (Hilbert–Schmidt
rigidity of permutation parts, uniform in the fiber dimension) and Theorem 2
(the collapse, in five steps) — is written out in
`notes/TRUE_BLOCK_MONOMIAL_COORDINATE_COLLAPSE.md`. `requires: []` is a proof
commitment, not a placeholder.

The one external input is Kun–Thom Corollary D, used at the last step and
nowhere else, with Păunescu Definition 1.4 supplying the notion of a sofic
action that Corollary D refutes. Both are transcribed verbatim, with
provenance, in `research/artifacts/kun-thom-2608-06222-verified.md`; the trust
surface is the one recorded in `wreath-not-sofic-proof` and is inherited
unchanged. Everything else is finite-dimensional linear algebra plus the
residual finiteness of `G` (Kun–Thom Theorem E) feeding
`Sofic/LEFSofic.isSofic_of_isLEF`.

**Formalization note.** Lemma 1 is a self-contained statement about
`U(m) ≀ Sym(Y)` in the normalized Hilbert–Schmidt metric and is a plausible
next Lean target; the repository already carries the wreath permutation gadget
(`Sofic/MonomialModel.wreathPerm`, `wreathPerm_mul`,
`hammingDistance_wreathPerm`) and the metric infrastructure
(`Sofic/Hyperlinear.hsDistSq`) that it would be stated against. That would put
the whole of Theorem 2 except the final citation inside the kernel.
