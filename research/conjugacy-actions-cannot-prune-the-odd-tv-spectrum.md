---
rg: 2
id: conjugacy-actions-cannot-prune-the-odd-tv-spectrum
kind: claim
title: Conjugacy actions cannot prune the odd TV spectrum
artifacts:
  - research/semidirect-odd-character-induction-proof.md
distinct_from:
  nested-conjugacy-stops-at-tv-dictator-projectors: that proves a scalar affine obstruction and locates the ordinary BCS relation left by Fanizza et al.; this allows noncommuting auxiliaries which permute spectral atoms and constructs finite-dimensional bad sectors.
  lcs-parity-gadgets-preserve-odd-dictator-affine-hull: that assumes scalar extensions of each honest atom; this requires no scalar extension of the auxiliary conjugators.
  word-level-seed-wirings-preserve-marked-matricial-approximability: that transfers pre-existing matrix approximations through a word map; this directly builds finite-dimensional representations for every odd character orbit.
---

Let

$$
H\cong(C_2)^P
$$

be the finite abelian factor of a zero-noise Taller--Vidick cell, and let
\(z\in H\) be its constant-minus-one element.  Let an arbitrary group
\(K\) act on \(H\) by automorphisms which fix \(z\), and form

$$
G=H\rtimes K,
\qquad
J=(z,1).                                                \tag{1}
$$

For every character \(\chi\in\widehat H\) with \(\chi(z)=-1\), the group
\(G\) has a finite-dimensional unitary representation \(\rho_\chi\) such
that

$$
\rho_\chi(J)=-I                                        \tag{2}
$$

and the restriction to \(H\) contains \(\chi\).

In particular, every odd high-degree Taller--Vidick character survives in
a finite-dimensional perfect sector.  This remains true even though the
auxiliary \(K\)-operators can be noncommuting and can permute the joint
spectral atoms of \(H\).

Thus adding only conjugacy relations which implement a genuine
automorphism action on the TV torsor cannot select the singleton dictator
spectra.  A possible escape must leave the semidirect-product class, for
example through an \(H\)-valued cycle relation among conjugators, a
nonsplit extension, or an ordinary BCS spectral-projector relation.  The
claim does not classify those cases and does not construct a
nonhyperlinear group.
