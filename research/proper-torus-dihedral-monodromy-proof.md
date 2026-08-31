---
rg: 2
id: proper-torus-dihedral-monodromy-proof
kind: route
title: Compute Weyl label transport and Fourier transform one missing-lift triangle row
target: proper-torus-label-cover-has-dihedral-monodromy
requires:
  - proper-torus-diagonal-code-is-incomplete-cover-curl
  - proper-torus-reynolds-is-edge-refinement
  - right-u-reynolds-has-torus-hecke-blocks
---

Identify each vertex fiber of
\[
 P\backslash G\longrightarrow\overline P\backslash G
\]
with the torsor \(K=T_s/H\) after choosing a local section. Reversing an
oriented edge is left multiplication by \(x\). Since
\[
 x\,s\,x=s^{-1}\qquad(s\in T_s),
\]
a label \(k\) at one endpoint becomes \(-k\) at the other endpoint.
Changing either local section adds a constant. Hence every transition is
exactly \(k\mapsto\gamma-k\), proving (DHM1). Composition along a path
alternates the sign and proves (DHM2).

In particular, monodromy around a triangle is an affine reflection.
For odd \(i>1\), such a reflection is a nonidentity involution with one
fixed point. If the connected cover had a regular cyclic deck group of
order \(i\), that group would centralize the monodromy group. After
identifying one fiber with a regular \(C_i\)-torsor, its centralizer is
the cyclic translation group itself, which has no nonidentity involution
when \(i\) is odd. This is impossible. Directly, a translation by \(s\)
commutes with \(k\mapsto\gamma-k\) exactly when \(2s=0\), giving (DHM3)
and the stated even-index remnant as well.

Now choose oriented \(K\)-coordinates on the three edge fibers meeting
any selected arithmetic triangle row. That row reads one coordinate from
each fiber, so it has the form (DHM4). If all \(i\) deck translates were
present, the translated rows would be
\[
 L_{\triangle,s}(f_1,f_2,f_3)
 =f_1(s+\gamma_1)+f_2(s+\gamma_2)+f_3(s+\gamma_3),
\]
up to replacing \(s\) by \(-s\) on edges whose orientation was reversed.
Fourier transformation in the row variable \(s\) would then isolate one
character at a time.

The arithmetic complex retains only its selected correlated rows. For
odd \(i\), Maschke's theorem makes \(\mathbb F_2[K]\) semisimple, and
after extension to a splitting field \(\mathbb E\) the usual finite
Fourier inversion is valid. Substitution into the single evaluation row
gives (DHM5), with a possible replacement of a character by its inverse
on a reversed edge. Since inversion only permutes \(\widehat K\), the row
still contains every character. There is no row-Fourier coordinate with
which to separate the sum.

For \(i=2^\nu m\), characteristic two gives
\[
 z^i-1=(z^m-1)^{2^\nu}.
\]
Because \(m\) is odd, \(z^m-1\) is square free. This proves (DHM6) and the
claimed radical filtration. The inversion \(z\mapsto z^{-1}\) preserves
its powers. But a coordinate evaluation obeys
\[
 \operatorname{ev}_\gamma(S_s f)=f(\gamma-s),
\]
whereas its scalar output has no translated row coordinate. It is
therefore not a homomorphism of the label group algebra, so the radical
filtration does not turn the cubic curl into independent graded maps.

Global right multiplication by \(T_s\) is different: it simultaneously
moves every base coset and every triangle row, hence really commutes with
the arithmetic column. That is exactly the symmetry used in the
right-torus Hecke decomposition, and completes the firewall.
