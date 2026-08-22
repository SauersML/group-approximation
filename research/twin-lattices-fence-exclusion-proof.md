---
rg: 2
id: twin-lattices-fence-exclusion-proof
kind: route
title: Bridson semisimplicity, properness of the twin action, and the flat torus theorem force a norm-preserving normalizer
target: twin-lattices-exclude-known-llp-fences
requires: []
---

**(a).**  By Bridson's semisimplicity theorem (M. Bridson, *On the
semisimplicity of polyhedral isometries*, Proc. Amer. Math. Soc. 127
(1999) 2143--2146; also Bridson--Haefliger III.C), a cellular isometry of
a locally finite polyhedral complex with finitely many shapes is
semisimple: elliptic (fixes a point) or hyperbolic (positive translation
length, attained on an axis).  An element `g = (g_+, g_-)` of a
factor-preserving action is semisimple on the product with
`l(g)^2 = l_+(g_+)^2 + l_-(g_-)^2` and `Min(g) = Min(g_+) x Min(g_-)`.
If `l(g) = 0` then `g` fixes a point `(x_+, x_-)` of the product; the
action of `Lambda` is proper (for a twin building lattice, discreteness
of `Lambda` in `G_+ x G_-` with compact open point stabilizers makes
point stabilizers of the product action finite), so `g` has finite
order.  Hence infinite order implies `l(g) > 0`.

**(b).**  Let `A = Z^k <= Lambda`.  Every nontrivial `a in A` has
infinite order, so by (a) `A` acts properly by semisimple isometries on
the complete CAT(0) space `X_+ x X_-`.  By the Flat Torus Theorem
(Bridson--Haefliger II.7.1) there is an `A`-invariant flat `E^m subset
Min(A)` on which `A` acts as a lattice of translations; properness makes
the translation homomorphism injective with discrete image, so `m = k`
and

```text
l(a) = || tau(a) ||   for all a in A,                              (TF1)
```

the Euclidean norm of the translation vector, a positive definite norm
on `A (x) R` restricted to the lattice `A`.  Translation length is a
conjugation invariant of the ambient isometry group:
`l(gamma a gamma^(-1)) = l(a)`.  So for `gamma in N_Lambda(A)` the
automorphism `Ad(gamma)|_A in GL(A) = GL_k(Z)` preserves the norm
`(TF1)`.  The isometry group of a positive definite lattice is finite,
so the image of `N_Lambda(A)` in `GL_k(Z)` is finite.

**(c).**  A pair `A rtimes Sigma <= Lambda` with `Sigma` acting through
an infinite subgroup of `GL_k(Z)` would put an infinite group in the
image of `N_Lambda(A) -> GL_k(Z)`, contradicting (b).  For the listed
groups: `Z^2 rtimes Sigma` with `Sigma <= SL_2(Z)` nonamenable has
infinite image (a nonamenable subgroup of `SL_2(Z)` is not virtually
cyclic, hence certainly infinite in `GL_2(Z)`); `Z^3 rtimes GL_2(Z)`
(Siegel/Sym^2 pair) has infinite image; `SL_n(Z)`, `n >= 3`, contains
the block pair `Z^2 rtimes SL_2(Z)` (top-right column block normalized
by the upper-left `SL_2`), so it cannot embed either.  `BS(1, n)`,
`n >= 2`, has a distorted infinite-order element `a` with
`t a^n t^(-1)`-growth forcing `l(a) = lim d(x, a^(m) x)/m = 0` by the
logarithmic word growth of `a^(n^m)`, contradicting (a); this proves the
final scope remark.

**(d).**  A locally finite two-dimensional polyhedral complex of
Gromov-hyperbolic type has finite asymptotic dimension (bounded-geometry
hyperbolic spaces: Roe, *Hyperbolic groups have finite asymptotic
dimension*, Proc. AMS 133 (2005); the Euclidean/affine case is classical
for buildings), and `asdim(X_+ x X_-) <= asdim X_+ + asdim X_-`.  A
metrically proper isometric action of a finitely generated group on a
space of finite asymptotic dimension makes every orbit map a coarse
embedding, so every finitely generated subgroup of `Lambda` has finite
asymptotic dimension, hence Yu's property A.  A group containing a
coarsely embedded expander sequence does not coarsely embed in Hilbert
space, while property A implies such an embedding; so no subgroup of
`Lambda` contains coarsely embedded expanders, which is the defining
feature of the Osajda-type groups behind the Buss--Echterhoff--Willett
LLP failures.
