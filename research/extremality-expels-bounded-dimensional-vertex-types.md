---
rg: 2
id: extremality-expels-bounded-dimensional-vertex-types
kind: route
title: Use extremality of the regular character against a compact character hull
target: regular-modular-microstates-have-no-bounded-atomic-mass
requires:
  - capture-gap-localizes-to-regular-character-face
---

# Extremality expels bounded-dimensional types

Fix \(D\). Let \(K_D\) be the union, for \(1\leq j\leq D\), of the normalized
characters of \(j\)-dimensional unitary representations of
\(V=\operatorname{PSL}_2(\mathbb Z)\). The representation varieties
\(\operatorname{Hom}(V,U(j))\) are compact and the character map is
continuous in the pointwise topology. Hence \(K_D\) is compact.

Let \(\operatorname{co}(K_D)\) denote its closed convex hull in the compact
space of normalized positive-definite class functions on \(V\). This hull is
compact: it is the image of the compact probability-measure space
\(\operatorname{Prob}(K_D)\) under the continuous barycenter map
\[
 \mu\longmapsto\left[g\longmapsto
       \int_{K_D}\chi(g)\,d\mu(\chi)\right].               \tag{1}
\]
The normalized character of every direct sum of irreducibles of dimension
at most \(D\) belongs to \(\operatorname{co}(K_D)\).

Put
\[
 r_n=\frac{\dim\sigma_n^{\leq D}}{d_n}.
\]
If (RAM1) fails, pass to a subsequence with \(r_n\to r>0\). Let
\(\varphi_n\) be the normalized character of the bounded-dimensional
summand. When \(r_n<1\), let \(\psi_n\) be the normalized character of its
orthogonal complement. Compactness of the full character space and of
\(\operatorname{co}(K_D)\) gives pointwise subsequential limits
\(\varphi\in\operatorname{co}(K_D)\) and \(\psi\), and
\[
 \delta_e=r\varphi+(1-r)\psi.                             \tag{2}
\]
For \(r=1\), read (2) as \(\delta_e=\varphi\).

The regular character is extremal because its GNS von Neumann algebra
\(L(V)\) is a factor: \(V\) is ICC. Therefore (2) forces
\[
 \varphi=\delta_e.                                        \tag{3}
\]
But (1) then expresses the extremal character \(\delta_e\) as a barycenter
of characters in \(K_D\). An extremal point has only the point mass at
itself as a representing probability measure on a convex set of characters,
so (3) would imply \(\delta_e\in K_D\). This is impossible: the GNS
representation of \(\delta_e\) is the infinite-dimensional regular
representation, whereas every member of \(K_D\) has a finite-dimensional
GNS representation. Hence \(r=0\), proving (RAM1).

Applying the same argument separately to the two exact vertices of a pure
regular Iwahori countersequence proves the stated two-sided escape.
