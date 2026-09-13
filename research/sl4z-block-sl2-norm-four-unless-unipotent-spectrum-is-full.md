---
rg: 2
id: sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full
kind: claim
title: A representation of SL_4(Z) whose column unipotent spectrum is not the whole torus gives the block SL_2(Z) Laplacian norm four
distinct_from:
  sl4z-representations-have-sl2-invariant-vectors: that is the finite-dimensional theorem; this extends its norm conclusion to every unital C-star or unitary representation with non-full column unipotent spectrum, including infinite-dimensional and corona ones.
  sl4z-corona-representations-have-block-sl2-norm-four: that is the open crux for all corona representations; this settles it exactly for those with non-full spectrum.
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13-part2.md
---

ESTABLISHED (unreviewed).  Let `sigma : C*(SL_4(Z)) -> B` be a unital *-homomorphism into
a unital C*-algebra.  Suppose the joint spectrum of `sigma(I + v_1 e_14 + v_2 e_24 + v_3 e_34)`,
`v in Z^3`, is not all of `T^3`.  Then `||sigma(S + S^-1 + T + T^-1)|| = 4` for the
upper-left block `SL_2(Z)`.  If `B = B(H)`, that block fixes a nonzero vector.

**What it does for the crux.**  The crux
`sl4z-corona-representations-have-block-sl2-norm-four` holds off the full-spectrum case,
so it is equivalent to that case.
- Every MF embedding of `C*_r(SL_4(Z))` already has Haar, hence full, unipotent spectrum.
- So Magee--de la Salle's congruence mechanism, extended here from finite-dimensional to
  arbitrary representations, reaches none of the maps the MF question is about.

**Model tests.**
- The regular representation has full spectrum and norm `< 4` (Kesten), so the
  hypothesis cannot be dropped.
- The trivial representation has spectrum `{0}` and norm `4`.

Proof: `sl4z-block-sl2-norm-four-unless-unipotent-spectrum-is-full-proof`.
