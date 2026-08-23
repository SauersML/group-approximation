---
rg: 2
id: smooth-label-cover-edges-are-finite-phase-projective-color
kind: claim
title: Every smooth-label-cover edge is exactly a finite-phase projective-color biclique relation
distinct_from:
  monomial-game-pair-compatibility-is-projective-color-rigid: that classifies the compatibility relation forced by a direct monomial matrix test; this proves that every raw smooth-label-cover edge has precisely the positive classified form.
  functional-support-is-affine-exactly-on-an-affine-domain-map: that asks whether a functional relation is affine after binary encoding; this uses the native finite label alphabet and does not assert affine or LCS syntax.
  smooth-label-cover-gap-full-corner-monomial-realization: that asks for one global square monomial linking algebra; this is only the exact edge-by-edge scalar-color representation.
---

**ESTABLISHED EXACT EDGE SYNTAX.**  Let `S=(G,[n],[k],Sigma)` be any
finite smooth-label-cover instance.  For an edge `e=(v,w)`, its accepted
label relation is

```text
R_e={(a,b) in [n]x[n] : pi_(e,v)(a)=pi_(e,w)(b)}
   = disjoint_union_(ell in [k])
       pi_(e,v)^(-1)(ell) x pi_(e,w)^(-1)(ell).          (SLC1)
```

Thus `R_e` is a disjoint union of complete bipartite projective-color
classes.  More strongly, fix any finite phase order `r`.  Choose nonzero
scalars `c_ell`, `ell in [k]`, in pairwise distinct `mu_r`-orbits, for
example distinct positive magnitudes, and put

```text
A_(e,v,a)=c_(pi_(e,v)(a)),
B_(e,w,b)=c_(pi_(e,w)(b)).                               (SLC2)
```

For phases `alpha,beta in mu_r`, there exist `alpha,beta` satisfying

```text
alpha A_(e,v,a)=beta B_(e,w,b)                           (SLC3)
```

if and only if `(a,b) in R_e`.  Hence every individual edge predicate is
already in the projected compatibility syntax of a finite-phase monomial
test.

This is a local statement.  It does not complete the vertex PVMs to one
square order-`r` quantum-reflection matrix, combine all edge-dependent color
tables into one matrix pair, or prove that any auxiliary completion is a
full corner.
