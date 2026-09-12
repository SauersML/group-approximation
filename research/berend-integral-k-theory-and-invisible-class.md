---
rg: 2
id: berend-integral-k-theory-and-invisible-class
kind: claim
title: Eckhardt's cubic Berend algebra has an integral K-class invisible to every proper quotient
distinct_from:
  berend-finite-orbit-quotients-are-asymptotically-isometric: that proves norm separation by finite-orbit quotients; this computes integral K-theory and exhibits a nonzero class killed even by their norming product model.
  berend-proper-quotients-have-decomposition-rank-at-most-two: that bounds the quotient dimensions; this identifies integral topology which none of those quotients detects.
artifacts:
  - research/artifacts/berend-k-theory-quotient-obstruction-2026-09-05.md
---

Use the exact cubic `p(t)=t^3+t^2-2t-1` and the independent units
`a,b` in Eckhardt's Theorem 2.4, as in
`berend-torus-actions-give-strongly-qd-polycyclic-groups`. Put
`A=C*(Z^3 ⋊ <a,b>)` and `epsilon=Norm(b) in {+1,-1}`. Then, for both
`i=0,1`,

`K_i(A) = Z^4` if `epsilon=+1`,

`K_i(A) = Z^2 direct_sum Z/2` if `epsilon=-1`,

where these are isomorphisms of abelian groups. The image `nu` of the
top exterior class in `K_1(C(T^3))` has infinite order when `epsilon=+1`
and exact order two when `epsilon=-1`. Every proper quotient of `A`
kills `nu`; equivalently, `nu` belongs to the image of `K_1(I)` for
every nonzero ideal `I`.

The diagonal homomorphism into any product of finite-orbit quotients
also kills `nu` on `K_1`, as does its composition with quotient by the
direct sum. In particular the faithful model in
`berend-finite-orbit-quotients-are-asymptotically-isometric` is not
injective on `K_1`.

This is a direct calculation using standard K-theory, without a claim
of literature novelty or of infinite decomposition rank.
