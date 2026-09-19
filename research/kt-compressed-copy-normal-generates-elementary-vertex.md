---
rg: 2
id: kt-compressed-copy-normal-generates-elementary-vertex
kind: claim
title: The compressed Kun--Thom copy normally generates its elementary vertex
artifacts:
  - research/constant-roots-give-the-kt-normal-generation-fence.md
distinct_from:
  fd-invisibility-of-compression: that proves equality of compressed and ambient images in every finite-dimensional representation of the full Laurent actor; this is a purely internal normal-generation theorem in the polynomial Kazhdan vertex, with no representation theory.
  two-bs-edges-hide-an-amenable-q8-splitting: that makes the Q8 selector interact with two freely independent invisible words and finds a transverse amenable splitting; this rules out the most direct attempt to replace those words by the whole Kun--Thom vertex.
  shared-center-extraspecial-wreath-has-fd-invisible-spin-sector: that lets the actor move one finite packet through infinitely many sites; the resulting base is not one finite group normalized by the whole elementary vertex, so it escapes this fence.
---

Let \(S\) be a unital ring, let \(r\ge3\), and let
\(\beta:S\to S\) be a unital ring endomorphism. Put
\[
 \Gamma=EL_r(S),\qquad
 \Lambda=\beta_*(EL_r(S))\le\Gamma.
\]
Then
\[
 \langle\!\langle\Lambda\rangle\!\rangle_\Gamma=\Gamma. \tag{KTN1}
\]

In particular, this applies to the pinned Kun--Thom polynomial vertex
\[
 S=\mathbb F_q[x_1,\ldots,x_d]
\]
and its strict monomial compressor. Although \(\Lambda\) is a proper
subgroup of \(\Gamma\), it normally generates \(\Gamma\).

Consequently, if \(K\) is any group and
\[
 \alpha:\Gamma\longrightarrow\operatorname{Aut}(K)
\]
is an action for which \(\Lambda\) fixes \(K\) pointwise, then \(\alpha\)
is trivial. Thus no nontrivial finite-selector coinvariant can be produced:
\[
 N_\alpha=
 \left\langle\!\left\langle
   \alpha(\gamma)(k)k^{-1}:\gamma\in\Gamma,\ k\in K
 \right\rangle\!\right\rangle_K
 =1.                                                       \tag{KTN2}
\]

This blocks the most direct nonamenable-edge replacement of the terminal
Q8/\(BS(2,3)\) amalgam. Namely, one would like to take a finite \(K\) with
a central mark \(z\), make \(\Lambda\) centralize \(K\), let \(\Gamma\)
act nontrivially on \(K\), and form
\[
 (K\rtimes_\alpha\Gamma)
 *_{\Gamma\times\langle z\rangle}
 (G\times\langle z\rangle).                              \tag{KTN3}
\]
Bass--Serre normal form would embed \(K\), and exact
finite-dimensional image collapse would make the \(\Gamma\)-action
invisible. But the left vertex in (KTN3) exists with
\(\Lambda\) centralizing \(K\) only when \(\alpha\) is trivial. Then
\(N_\alpha=1\), so no nontrivial \(z\) can lie in the coinvariant subgroup.

The obstruction is stronger than finiteness of \(K\): every homomorphism
from \(\Gamma\) to any group which kills \(\Lambda\) is trivial. It also
does not use property \((T)\), finite presentation, or finite-dimensional
image collapse.

The scope is exact. It does not rule out partial HNN identifications which
do not normalize all of \(K\), nor an infinite-site base on which
\(\Gamma\) permutes different copies of a packet. The shared-center Pauli
wreath uses precisely the latter escape. Its remaining moving-window
normalized-HS problem is untouched. No nonhyperlinear group is proved here.

DERIVATION
constant-roots-give-the-kt-normal-generation-fence
