---
rg: 2
id: mdls-averaging-at-non-torsion-character-gives-spectral-gap
kind: claim
title: At a non-torsion character, the Magee-de la Salle averaging step yields a representation weakly contained in the regular representation of SL_2(Z)
distinct_from:
  mdls-obstruction-is-affine-mechanism-plus-level-matching: that shows Steps 2 and 3 of Magee-de la Salle live in the affine group at finite level; this shows their averaging step gives the opposite conclusion when the character is not a torsion point.
  sl3z-has-no-invariant-vector-witnesses: that is about finite families of subgroups of SL_3(Z) catching genuine representations; this is about the spectral mechanism at irrational characters of Z^2 in an arbitrary unitary representation.
artifacts:
  - research/artifacts/sl4z-mf-corona-reduction-2026-09-13.md
---

ESTABLISHED (unreviewed).  Setup:
- `G = SL_2(Z)` acts on `A = Z^2` by matrix multiplication.
- `sigma` is a unitary representation of `A x| G` on a Hilbert space `H`.
- For `theta in T^2`, `H_theta` is the eigenspace of `A` with character
  `a -> exp(2 pi i theta . a)`.
- `z = S + S^-1 + T + T^-1` for `G`.

If `theta` is not a torsion point, let `K` be the closed span of `sigma(G) H_theta`.  Then
`sigma|_K` restricted to `G` is weakly contained in `lambda_G`, so
`||sigma|_K(z)|| <= ||lambda_G(z)|| < 4`.

**Why this matters.**  Magee--de la Salle Step 3 (arXiv:2312.03220v2, Section 2.4; the
repo's re-derivation is in `mdls-obstruction-is-affine-mechanism-plus-level-matching`)
takes an eigenvector for the character of `A = {[0;y;z]}` (entries `(2,4)`, `(3,4)` of
`SL_4`) and averages it over the coordinate-`(2,3)` block `SL_2`.  The orbit of a
level-`p^r` character is finite, so the average is a nonzero invariant vector.

At a non-torsion character this claim shows that the same construction can only ever
give spectral gap.  So in any unitary representation of `SL_4(Z)`, including
corona representations realized on a Hilbert space, norm four for the block `SL_2`
cannot come from eigenvectors at non-torsion characters of `A`.  It must come from torsion
points of the spectrum of `A`, or from its continuous part.

Proof: `mdls-averaging-at-non-torsion-character-gives-spectral-gap-proof`.
