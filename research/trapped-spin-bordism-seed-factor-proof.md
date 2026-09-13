---
rg: 2
id: trapped-spin-bordism-seed-factor-proof
kind: route
title: Toms's proofs use S^4 only through uniqueness of spin structures and dimension four, and fixing the structures removes both
target: trapped-spin-bordism-class-over-any-spin-seed-factor
requires:
  - toms-trapped-spin-bordism-class
artifacts:
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
---

Part 1, Proposition 2.1 of the artifact goes through Toms's arguments and
lists every use of S^4 or of dimension four.

Spin structures: Toms uses simple connectivity of B only to make the spin
structures on TB and W_R unique. We fix them instead. TB gets the product of
the chosen structure on M with the unique one on X. W_R gets the pullback from
X. After that, the two-out-of-three rule (Lemma 2.3) and the transport through
the normal derivative use only fixed structures.

Dimension: the locus Z(v) has codimension rank_R W = dim X, so it is an
m-manifold, and the homotopy bordism is an (m+1)-manifold. Relative
transversality (Proposition 2.8), the normal bundle of the block-diagonal
subbundle (Lemma 3.1), and the bordism argument of Theorem 3.3 hold in every
dimension.

Values: perturb by the rotation R_{eps s} (Lemma 4.1), where s is a
transverse section of W over X. The loci of R and of (f o pr_M) R are both
M x Z(s), with the same normal identification, since left translation
removes f. The normal derivative is constant along each copy M x {xi}, so
each copy carries the fixed structure on M, up to orientation. It contributes
sign_xi(s)·[M, f]_red, or 0 for the identity. The signed count is
<c_r(Q)^2, [X]> by (10) and (19) of Toms.
