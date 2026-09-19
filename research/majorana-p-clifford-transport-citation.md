---
rg: 2
id: majorana-p-clifford-transport-citation
kind: route
title: Import the binary-orthogonal model and braid generators of parity-preserving Majorana Cliffords
target: majorana-p-clifford-transport-is-binary-orthogonal
requires: []
artifacts:
  - research/artifacts/majorana-clifford-transport-audit-2026-08-20.md
---

**Established by citation.** Bettaque--Swingle, *The Structure of the
Majorana Clifford Group*, arXiv:2407.11319v2.

The user-supplied TeX source was read directly on 2026-08-20, including
`sections/majorana.tex`, `sections/cliffords.tex`,
`sections/stabilizers.tex`, `sections/design.tex`, and the relevant appendix
proofs.  The symplectic representation is their Theorem
`thm:clifford_symplectic`; parity preservation and the binary orthogonal
subgroup are in `def:orthogonal_group` and the following corollary; braid
generation by weight-two and weight-four Majorana strings is Theorem
`thm:gottesman_knill`; and the fixed-parity quotient/frame-potential result
is Theorem `thm:frame_equality` together with `sec:subgroup_lemma`.

Only those finite-dimensional algebraic statements are imported.  The paper
does not assert a normalized-Hilbert--Schmidt stability theorem, an
approximate-representation rounding result, or a nonhyperlinearity
obstruction.
