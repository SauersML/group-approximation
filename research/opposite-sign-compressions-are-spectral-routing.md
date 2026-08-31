---
rg: 2
id: opposite-sign-compressions-are-spectral-routing
kind: claim
title: Opposite-sign compressed LCS equations are only spectral routing
artifacts:
  - research/opposite-sign-compression-spectral-proof.md
distinct_from:
  fixed-perfect-seeds-do-not-black-box-exactify-tv: that kills a common gate and classifies black-box game products; this classifies the minimal use of two different projection gates.
  tv-central-flags-and-private-slacks-cannot-exactify: that treats central direct-sum flags; this begins with arbitrary noncentral projections and proves that the equations themselves force local orthogonality.
---

Let \(L\) be a reflection, let \(s\in\{+1,-1\}\), and let \(p_+\) and
\(p_-\) be arbitrary projections.  If

$$
p_+(L-sI)p_+=0,
\qquad
p_-(L+sI)p_-=0,                                        \tag{1}
$$

then

$$
Lp_+=sp_+,
\qquad
Lp_-=-sp_-,
\qquad
p_+p_-=0.                                              \tag{2}
$$

Thus each gate commutes with \(L\), and the two gates are orthogonal,
although no such commutation or orthogonality was assumed.

If \(p_++p_-=I\), they are exactly the two spectral projections of \(L\)
and

$$
L=s(p_+-p_-).                                          \tag{3}
$$

Consequently the smallest relation-dependent repair of the
same-left-side, opposite-right-side Taller--Vidick pair is not a genuinely
noncommuting flag.  It merely routes the two equations to the two spectral
sectors of their common reflection.  Without a further cross-relation, it
adds no more than one seed reflection; with uncovered support it leaves an
unconstrained sector.

This is a local classification only.  Gates attached to different source
words can still fail to commute with one another, and a cyclic network of
such spectral identifications could carry new information.  No
nonhyperlinear group is constructed here.
