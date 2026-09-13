---
rg: 2
id: soft-kazhdan-central-elements-fixed-by-normal-closure
kind: claim
title: In a monomial Hilbert--Schmidt model, a soft element centralizing an infranormal Kazhdan subgroup is fixed by the subgroup's normal closure
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that is the Hamming row, transporting every centralizing element along all of G inside a sofic group; this is a monomial-HS statement, transporting only elements with trivial permutation part, and only along the normal closure.
  hyperlinear-groups-kill-rigid-compression-defects: that is the open Hilbert--Schmidt row for arbitrary unitary models; this proves the part of the monomial row carried by the abelian soft kernel.
  normal-closure-fixes-gamma-fixed-algebra: that is the permutation-side statement about the diagonal fixed algebra of a sofic representation; this pulls it back to monomial models of an arbitrary ambient group through the exact phase-blind covariance of diagonals.
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part2-2026-09-13.md
---

**ESTABLISHED** (unreviewed).  Let `H` be a countable group and
`Lambda <= G <= H`, with `Lambda` and `G` Kazhdan, `Lambda` infranormal in
`G` (its compression semigroup generates `G`), and `G` sofic.  Let
`rho : H -> prod_omega (U(1) wr S_n)` be any homomorphism into the tracial
ultraproduct of monomial unitaries, with permutation part
`psi : H -> S_omega`.  If `a in C_H(Lambda)` and `psi(a) = 1`, then

```text
rho(n a n^(-1)) = rho(a)      for every n in <<Lambda>>_G.
```

`psi(a) = 1` holds automatically for `a in Rad_sof(H)`, since `psi(H)` is
sofic.

**Why.**  `rho(a)` is diagonal.  Conjugating a diagonal by a monomial acts by
the permutation part exactly, whatever the phases.  So `rho(a)` is a
`psi(Lambda)`-fixed diagonal element.  Tensoring `psi|G` with a sofic
representation of `G` gives a genuine sofic representation fixing
`rho(a) ⊗ 1`.  Part 2 of `normal-closure-fixes-gamma-fixed-algebra`, which
comes from Kun--Thom 4.1, makes the normal closure fix it.

**Use.**  With deep congruence subgroups of the Theorem E pair and
perfectness of `EL_r(R)`, it gives
`kt-wreath-monomial-models-kill-fibre-even-lamps`: every monomial HS model of
the Kun--Thom wreath kills all of `K_even`.

**Scope.**
- Block size `k >= 2` is not covered: conjugating block-diagonals by
  block-monomials rotates inside blocks.
- `G` must be sofic, for the tensoring step.
- The trust surface of arXiv:2608.06222 travels with this claim.

Derivation: `soft-kazhdan-central-elements-fixed-by-normal-closure-proof`.
