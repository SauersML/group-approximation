---
rg: 2
id: reduced-group-algebras-contain-no-nonzero-ghosts
kind: claim
title: The only ghost operator in a matrix algebra over the reduced group C*-algebra of an infinite group is zero
invalidates:
  - bc-counterexample-via-ghost-projection
distinct_from:
  subgroup-average-projections-give-no-reduced-bc-obstruction: that disposes of subgroup averages, Kazhdan projections and compression relations; this disposes of ghost operators, the witnesses of the Higson--Lafforgue--Skandalis counterexamples with coefficients.
  kazhdan-projections-vanish-in-regular-group-algebra: that says invariant vectors of an infinite subgroup are not square-summable; this says an element of the reduced algebra whose matrix entries tend to zero at infinity is zero, by translation invariance of those entries.
---

**ESTABLISHED** by `reduced-group-algebras-contain-no-nonzero-ghosts-proof`.

Let `G` be an infinite countable discrete group and `n >= 1`. Let `T` lie in
`M_n(C*_r G)`, acting on `C^n ⊗ l^2(G)`. Call `T` a **ghost** if for every
`eps > 0` there is a finite `F ⊆ G` with

```text
| < T (e_i ⊗ delta_h), e_j ⊗ delta_g > |  <  eps     whenever (g, h) ∉ F × F.
```

Then `T` is a ghost only if `T = 0`.

**Why it matters for `baum-connes-counterexample-group-exists`.**
- The Higson--Lafforgue--Skandalis counterexamples (GAFA 12 (2002); context,
  not imported) use a non-compact ghost projection. It is built from an
  expander coarsely embedded in a Gromov monster.
- That projection lives in a crossed product with commutative coefficients,
  such as the uniform Roe algebra `l^inf(G) ⋊_r G`. Its K-class is detected
  because it dies in the boundary quotient but is not a compact operator.
- Inside `M_n(C*_r G)` the matrix entries of every element are constant along
  the infinite translates `{(kh, h) : h ∈ G}`. So a ghost is zero, and the
  compact operators meet `M_n(C*_r G)` only in `0`.
- The ghost mechanism therefore has no trivial-coefficient form. A
  trivial-coefficient counterexample built from expanders must first convert
  the coefficient failure into a statement about some group algebra.

The fact is elementary and certainly known. No novelty is claimed.
