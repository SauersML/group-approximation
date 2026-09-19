---
rg: 2
id: monomial-root-elements-are-conjugate-in-the-leavitt-group
kind: claim
title: Every root element with a monomial-type coefficient is conjugate to the unit root, so every character is constant on all of them
artifacts:
  - research/monomial-root-conjugacy-proof.md
distinct_from:
  degree-zero-leavitt-core-characters-are-dirac-haar-mixtures: that classifies characters on the degree-zero core by dense-support character ratios; this transports the resulting constant to root elements of every gauge degree by an explicit conjugacy inside the Leavitt group, using no character bound.
  leavitt-one-compressor-defect-lies-in-amenable-subgroups: that says a Property-(T)-free proof must use nonzero-degree roots in Weyl-mixed relations; this computes the trace of exactly those roots under every character, and shows it carries no new information beyond the core's constant.
  full-leavitt-idempotent-defect-saturation: that shows one complementary root normally generates the rank-20 Steinberg group; this is a conjugacy statement between root elements themselves, in the elementary group, with the module-theoretic invariants that decide it.
---

**ESTABLISHED.**  Let `R=L_(F_2)(1,2)` and `H=EL_12(R)=GL_12(R)`.  Call
`y in R` **monomial-type** if

```text
y = s_u b t_v,     b in B_m regular (b=b b^- b for some b^- in B_m),  b!=0,   (MRC1)
```

for binary words `u,v` and some `m` (so `y` is `s_u t_v`, `s_0 b`, `b t_0`,
`s_0 b t_0`, any degree-zero regular matrix, etc.).  Then for every
`i!=j`,

```text
x_ij(y)  is conjugate in H to  x_ij(1).                                (MRC2)
```

Consequently, for every character `phi` of `H` (in particular every MF
character), with `w` the constant of
`degree-zero-leavitt-core-characters-are-dirac-haar-mixtures`,

```text
phi(x_ij(y)) = w    for every i!=j and every monomial-type y.           (MRC3)
```

In particular the manuscript's degree-one and degree-minus-one generators
`x_ij(s_a)`, `x_ij(t_a)`, the compressor images `x_ij(s_0 a t_0)` with `a`
regular of degree zero, and the elements `x_02(s_0 b)`, `x_21(b t_0)`
produced by the Heisenberg rows from `x_01(s_0)`, `x_10(t_0)` all have
trace `w`.  Moreover the order-three elements

```text
x_01(s_0)x_10(t_0)   and   x_01(1)x_10(1)                              (MRC4)
```

are conjugate in `H`, so the two `S_3` subgroups `<x_01(s_0),x_10(t_0)>`
and `<x_01(1),x_10(1)>` have identical character restrictions
`((5w+1)/6, (1-w)/6, (1-w)/3)` on (trivial, sign, two-dimensional).

## What this means for the Property-`(T)`-free endpoint

The amenable fences say a collapse proof must use nonzero-degree roots in
Weyl-mixed relations.  This shows the trace data of those roots is already
fixed: every surviving corona representation has normalized character `w`
on every monomial-type root of every degree, and on the mixed `S_3`'s the
profile is the regular-like one.  No trace value at a monomial-type root,
nor at the mixed `S_3` subgroups, can distinguish a surviving
representation from the regular character; the distinction must lie in
non-monomial coefficients (such as `1+s_0`, whose right ideal is not a
direct summand), in infinite-order elements, or in operator-norm data that
no character sees.

The proof is module-theoretic: a square-zero endomorphism `N=yE_ij` of the
free module `R^12` is classified up to conjugacy by the isomorphism types
of a complement of its kernel, of kernel modulo image, and of its image;
for monomial-type `y` all three are nonzero finitely generated projective
modules built from cylinder idempotents, hence free of rank one by the
Leavitt relation `R ~= R^2`.  No property `(T)`, character bound, or
literature input is used beyond `GL_12(R)=EL_12(R)`, which is
established in the graph.

DERIVATION
monomial-root-conjugacy-proof
