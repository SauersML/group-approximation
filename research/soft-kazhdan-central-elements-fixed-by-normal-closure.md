---
rg: 2
id: soft-kazhdan-central-elements-fixed-by-normal-closure
kind: claim
title: In a bounded-block monomial Hilbert--Schmidt model, a soft element centralizing an infranormal Kazhdan subgroup is fixed by the subgroup's normal closure
distinct_from:
  sofic-groups-kill-rigid-compression-defects: that is the Hamming row, transporting every centralizing element along all of G inside a sofic group; this is a block-monomial HS statement, transporting only elements with trivial permutation part, and only along the normal closure.
  hyperlinear-groups-kill-rigid-compression-defects: that is the open Hilbert--Schmidt row for arbitrary unitary models; this proves the part of the bounded-block monomial row carried by the amenable soft kernel.
  normal-closure-fixes-gamma-fixed-algebra: that is the permutation-side statement about the diagonal fixed algebra of a sofic representation; this pulls it back to block-monomial models of an arbitrary ambient group, through phase-blind covariance for block size one and a finite atom cocycle for block size k.
artifacts:
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part2-2026-09-13.md
  - research/artifacts/ex-q34-kt-wreath-soft-kernel-part3-2026-09-13.md
---

**ESTABLISHED.**  Reviewed 2026-09-13:
- `ex-verify2-groups`: PASS, `research/artifacts/ex-review2-groups-2026-09-13-part1.md`
  §§2--3.  Its one notation note, on the Lemma 10 cocycle display, is fixed in
  74c1de27c3.
- Item 2 also passed in `research/artifacts/ex-review-groups-2026-09-12-part16.md`
  §16.5.

Kun--Thom 4.1 and Kadison's diagonalization theorem remain imports.

Let `H` be a countable group and
`Lambda <= G <= H`, with `Lambda` and `G` Kazhdan, `Lambda` infranormal in
`G` (its compression semigroup generates `G`), and `G` sofic.  Let
`rho : H -> prod_omega (U(k) wr S_n)` be any homomorphism into the tracial
ultraproduct of block-monomial unitaries with fixed block size `k`, and let
`psi : H -> S_omega` be its permutation part.

1. **Block size 1.**  If `a in C_H(Lambda)` and `psi(a) = 1`, then
   `rho(n a n^(-1)) = rho(a)` for every `n in <<Lambda>>_G`.
2. **Block size k.**  The same conclusion holds for every `k`, provided `a`
   lies in an abelian normal subgroup `A <= H` with `psi(A) = 1`.

`psi(a) = 1` holds automatically for `a in Rad_sof(H)`, since `psi(H)` is
sofic.

**Why.**
- *Block size 1.*  `rho(a)` is diagonal, and conjugating a diagonal by a
  monomial acts by the permutation part exactly, whatever the phases.
- *Block size k.*  Kadison diagonalization puts `rho(A)` into `Z ⊗ D_k`.
  Conjugation by `rho(g)` permutes the atoms of `rho(A)` inside blocks,
  preserving rank.  Ordering atoms canonically gives an `S_k`-valued cocycle
  over `psi`, hence a genuine homomorphism `G -> prod_omega Sym(Y × [k])`
  covariant for `rho(A)` (part 3 artifact, Lemma 10).
- *Conclusion.*  In both cases `rho(a)` becomes a `Lambda`-fixed diagonal
  element for a homomorphism into a symmetric ultraproduct.  Tensoring it with
  a sofic representation of `G` gives a sofic representation.  Part 2 of
  `normal-closure-fixes-gamma-fixed-algebra` (Kun--Thom 4.1) makes the normal
  closure fix `rho(a)`.

**Use.**  With deep congruence subgroups of the Theorem E pair and perfectness
of `EL_r(R)`, it gives `kt-wreath-monomial-models-kill-fibre-even-lamps`:
every bounded-block monomial HS model of the Kun--Thom wreath kills all of
`K_even`.

**Scope.**
- Unbounded block size is not covered, and cannot be in this form: block
  models with unbounded blocks are universal.
- `G` must be sofic, for the tensoring step.
- The trust surface of arXiv:2608.06222 travels with this claim.

Derivation: `soft-kazhdan-central-elements-fixed-by-normal-closure-proof`.
