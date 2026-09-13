---
rg: 2
id: trapped-lambda-mod-eight-class-proof
kind: route
title: The normal bundle of the block-diagonal locus is canonically W_R, so the trapped structure is a restriction of one on TB − W_R
target: trapped-lambda-mod-eight-class-over-seed-factor
requires:
  - toms-trapped-spin-bordism-class
artifacts:
  - research/artifacts/class-four-lambda-mod-eight-trapping-2026-09-13.md
  - research/artifacts/class-three-spin-bordism-trapping-2026-09-12.md
---

Part 1, Proposition 2.1.

(a) At g in D(E), left translation by g^{-1} carries the normal space of the
block-diagonal subbundle onto the off-diagonal skew-Hermitian matrices, which
form W_R. This is continuous in g, so the normal bundle is canonically
pi^* W_R (Toms Lemma 3.1). A transverse locus Z(v), or a transverse bordism
Z ⊂ B x I, has stable tangent bundle (TB − W_R)|_Z. The structure
sigma_M (+) tau restricts to it.

(b) Toms's proof of Theorem 3.3 uses transversality, Lemma 3.1 and
two-out-of-three for structures. For BSpin_8, two-out-of-three is this
restriction. So the class depends only on the path component, as in the spin
case (CT3 Proposition 2.1).

(c) Values: perturb by R_{eps s}. The loci are M x Z(s). On M x {xi} the
bundle TX − W_R restricts to a trivial virtual bundle over a point. There a
BSpin_8-structure is an orientation, so each copy carries sigma_M up to sign.
The signed count is <e(W_R), [X]> = <c_r(Q)^2, [X]>.
