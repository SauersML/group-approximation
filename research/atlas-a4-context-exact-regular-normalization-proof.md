---
rg: 2
id: atlas-a4-context-exact-regular-normalization-proof
kind: route
title: Trim the o(d) type residuals and repair every edge intertwiner by Reynolds polar correction
target: atlas-a4-context-exact-regular-normalization
requires:
  - atlas-a4-context-type-vector-converges-to-regular-point
  - finite-graph-of-groups-representation-types-are-integer-flows
artifacts:
  - research/artifacts/a4-context-virtually-free-compiler-2026-08-19.md
---

Write the common dimension as `d_n=20160 k_n`.  By
`atlas-a4-context-type-vector-converges-to-regular-point`, at every finite
vertex the exact representation `sigma_n` has irreducible multiplicities whose
total dimension differs from the desired regular multiplicity vector by
`o(d_n)`.  There are only finitely many vertices.

For one finite vertex group `F`, decompose the old representation and the
desired regular representation into irreducibles.  Match the common copies of
each irreducible and change only the unmatched summands.  The unmatched total
dimension is `r_n=o(d_n)`.  On the common summand the two representations are
identical; on the residual summand both are unitary.  Hence, after choosing the
matching decomposition on the same Hilbert space, for every `g in F`,

```text
||sigma_n(g)-sigma'_n(g)||_2^2 <= 4 r_n/d_n = o(1).
```

Do this independently at all vertices.  The target types are compatible on
every edge: restriction of `k_n Reg(A8)` to an edge group `E=C2` or `C3` is

```text
[A8:E] k_n Reg(E),
```

while restriction of `1680 k_n Reg(A4)` is

```text
1680 k_n [A4:E] Reg(E),
```

and these numbers agree because `20160=1680*12`.  Thus the edited endpoint
representations have equivalent restrictions to every edge group.

It remains to repair the stable letters without losing closeness.  Let `t_e`
be an old exact stable letter for an oriented edge `e`, and write `alpha_e,
beta_e` for the new endpoint restrictions.  Since the old endpoint actions
were exactly intertwined by `t_e` and the new endpoint actions are `o(1)` from
them, uniformly for `g in E`,

```text
|| beta_e(g) t_e - t_e alpha_e(g) ||_2 = o(1).
```

Average `t_e` onto the exact intertwiner space:

```text
X_e = (1/|E|) sum_(g in E) beta_e(g) t_e alpha_e(g)^*.
```

Then `beta_e(h) X_e = X_e alpha_e(h)` for every `h in E`, and the displayed
approximate intertwining gives `||X_e-t_e||_2=o(1)`.  Because the two edge
representations have the same multiplicity type, the polar partial isometry of
`X_e` can be completed, irreducible block by irreducible block, to a unitary
intertwiner `t'_e`.  Singular-value truncation gives

```text
||t'_e-X_e||_2 <= ||X_e-t_e||_2,
```

up to an inessential universal constant, so `||t'_e-t_e||_2=o(1)`.

Replacing every stable letter by `t'_e` therefore gives an exact representation
of the same graph-of-groups presentation on the same `d_n`-dimensional space,
with exactly regular type at every finite vertex, and changes every fixed
presentation generator by `o(1)`.  If the original stable letters were
`o(1)` from the identity, the repaired ones remain so by the triangle
inequality.  This is precisely the claimed normalization.