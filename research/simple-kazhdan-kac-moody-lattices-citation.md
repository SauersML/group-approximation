---
rg: 2
id: simple-kazhdan-kac-moody-lattices-citation
kind: route
title: Import the Caprace-Remy simple Kazhdan group corollary and check the explicit Cartan matrix
target: simple-kazhdan-kac-moody-lattices-exist
requires: []
---

Established by citation plus a finite check.

**Citation.**  P.-E. Caprace and B. Remy, *Simplicity and superrigidity of
twin building lattices*, Invent. Math. 176 (2009), no. 1, 169--221;
arXiv:math/0607664v2.  The introduction (pp. 2--3 of the arXiv version,
read from the PDF on 2026-08-21) states verbatim: "**Simple Kazhdan group
corollary.** If the generalized Cartan matrix `A` is 2-spherical (i.e.
every `2 x 2`-submatrix is of spherical type) and if `q > 1764^n`, then the
group `Lambda/Z(Lambda)` is finitely presented, simple and Kazhdan.
Moreover there exist infinitely many isomorphism classes of infinite groups
with these three properties."  The preceding "Simplicity theorem
(Kac--Moody version)" carries the standing hypotheses that the Weyl group
is irreducible, infinite and non-affine and `q >= |S|`; the corollary is
stated for "any neither spherical nor affine, indecomposable generalized
Cartan matrix".  Finite presentation is the Abramenko--Muhlherr
amalgam presentation for 2-spherical root data over fields with more than
three elements and property (T) is Dymara--Januszkiewicz's theorem for
buildings of large thickness, both as invoked by Caprace--Remy; only the
corollary's statement is used here.

**Finite check for `(KM2)`.**  A generalized Cartan matrix needs
`a_ii = 2`, `a_ij <= 0` for `i != j`, and `a_ij = 0 <=> a_ji = 0`: all hold.
The rank-two types are read off from `a_ij a_ji in {0, 1, 2, 3}` giving
`m_ij in {2, 3, 4, 6}`: here `(0, 2, 3) -> (2, 4, 6)`, all spherical.  The
Coxeter group with these orders is the `(2, 4, 6)` triangle group; since
`1/2 + 1/4 + 1/6 < 1` it is infinite hyperbolic, not affine (the affine
triangle groups are `(3,3,3)`, `(2,4,4)`, `(2,3,6)`), and the diagram is
connected (`m_13, m_23 != 2`), so `A` is indecomposable and of neither
spherical nor affine type.  The corollary applies with `n = 3`.

The "no finite-dimensional unitary representation" consequence is
Malcev's theorem (finitely generated linear groups are residually finite)
applied to the image of a simple infinite group.
