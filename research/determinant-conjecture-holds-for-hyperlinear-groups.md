---
rg: 2
id: determinant-conjecture-holds-for-hyperlinear-groups
kind: claim
title: Every hyperlinear group satisfies Lück's determinant conjecture
distinct_from:
  determinant-conjecture-holds-for-sofic-groups: that is the proved sofic case; this asks the same bound on the larger hyperlinear class, where no case beyond sofic is known
  determinant-conjecture: that is the conjecture for every group; this restricts to hyperlinear groups, so a determinant violation over a hyperlinear group would refute this and a violation over a non-hyperlinear group would not
---

**OPEN.** For every hyperlinear group `G` and every `A in M_(m x n)(Z[G])`,
`det_(N(G))(r_A) >= 1`.

**The question behind it: would a determinant below one make a group
non-hyperlinear?** As far as the sources read go, no.
- **Lück's status list.** Lück, arXiv:1901.00827v2, Remark 4.2 ("Status of the
  Determinant Conjecture", read from the PDF) lists closure under amenable
  quotients, directed colimits, inverse limits, subgroups and quotients by
  finite kernels, and membership of sofic groups. No hyperlinear case appears.
- **The sofic theorem.** Elek--Szabó (Math. Ann. 332, 2005) proves the sofic
  case (`determinant-conjecture-holds-for-sofic-groups`); the title's
  "hyperlinearity" refers to other results of that paper.
- **Thom 2007** (arXiv:math/0701294v3) works with sofic groups throughout.

So a determinant violation certifies nonsoficity of the support subgroup
(`determinant-violation-needs-nonsofic-support-subgroup`) and nothing is known
to certify non-hyperlinearity. Checked: those three sources only.

## Attempts

- **Unitary models carry no integrality.** A hyperlinear model of `A` is a
  complex matrix, and its characteristic polynomial need not be integral, so the
  mechanism of `integral-spectral-limits-satisfy-serre-inequalities` does not
  apply.
- **Integral unitary models are monomial.** Let a unitary matrix have
  algebraic-integer entries in a CM field, with every Galois conjugate matrix
  also unitary.
  - Each column has `sum_i |sigma(a_ij)|^2 = 1` for every embedding `sigma`, so
    every entry is `0` or has all conjugates of modulus at most `1`.
  - By Kronecker the nonzero entries are roots of unity, so each column has
    exactly one of them.
  - Such models are generalized permutation matrices and give only sofic
    approximations.
- **Finite-group models with rational characters.** These do prove the
  conjecture, and Galois balance too
  (`rational-character-approximable-groups-obey-determinant`).
  - Their characteristic polynomials are integral because rational
    representations of finite groups preserve lattices.
  - They are approximations by finite subgroups of unitary groups, and the
    Kun--Thom wreath admits none
    (`kun-thom-wreath-is-not-rational-character-approximable`).
  - Whether this class is larger than the sofic class is not known here.
- **What a proof for hyperlinear groups must do.** It needs integrality from
  somewhere other than the models, for instance the one-variable approximation
  of `integral-group-ring-spectra-are-integer-root-limits`. Galois balance and
  the Serre inequalities are exactly its content.
