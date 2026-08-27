---
rg: 2
id: atlas-a4-context-exact-regular-normalization-proof
kind: route
title: Trim the o(d) type residuals coherently along the tree and repair cycle intertwiners by Reynolds polar correction
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
identical; on the residual summand both are unitary.  Hence one can place a
regular-type representation `rho'_v` on the same Hilbert space so that, for
every `g in F`,

```text
||rho_v(g)-rho'_v(g)||_2^2 <= 4 r_n/d_n = o(1).        (1)
```

The target types are compatible on every edge.  For `E=C2` or `C3`,

```text
(k_n Reg(A8))|_E = [A8:E] k_n Reg(E),
(1680 k_n Reg(A4))|_E = 1680 k_n [A4:E] Reg(E),
```

and the multiplicities agree because `20160=1680*12`.  Thus every pair of
edited endpoint restrictions has the same `E`-representation type.

There is one coherence issue: tree edges in the standard graph-of-groups
presentation are literal identifications, not stable-letter relations.  Fix the
same maximal spanning forest used by the exact representation and root each
component.  Process its vertices away from the root.  Suppose the parent has
already been fixed and `e` joins it to a child.  Before adjustment, the new
parent and child restrictions to `E` are both `o(1)` from the old **common**
edge action, by `(1)`.  Hence they are equivalent exact `E`-representations and
are `o(1)` apart.

For two equivalent exact finite-group representations `alpha,beta` that are
`o(1)` apart, average the identity onto their intertwiner space:

```text
X = (1/|E|) sum_(g in E) beta(g) alpha(g)^*.
```

Then `beta(h)X=X alpha(h)` and `||X-I||_2=o(1)`.  The polar partial isometry of
`X`, completed blockwise on its kernel, is a unitary intertwiner `W` with
`||W-I||_2=o(1)`: on each irreducible multiplicity block this is just polar
correction of a square matrix, and the missing kernel/cokernel multiplicities
match.  Conjugate the **entire child vertex representation** by `W^*`.  Its
regular type is unchanged, it moves only `o(1)` on every fixed vertex
generator, and now its edge restriction equals the already fixed parent edge
restriction exactly.  Because the forest is finite and each child is adjusted
only when attached, induction makes every tree-edge identification exact while
preserving the `o(1)` vertex perturbation bounds.

It remains to repair the non-tree stable letters.  Let `t_e` be an old exact
stable letter for such an oriented edge, and write `alpha_e,beta_e` for the
now-coherent regular endpoint restrictions.  Since the old endpoint actions
were exactly intertwined by `t_e` and the new endpoint actions are `o(1)` from
them, uniformly for `g in E`,

```text
|| beta_e(g) t_e - t_e alpha_e(g) ||_2 = o(1).
```

Average `t_e` onto the exact intertwiner space:

```text
X_e = (1/|E|) sum_(g in E) beta_e(g) t_e alpha_e(g)^*.
```

Then `beta_e(h)X_e=X_e alpha_e(h)` and `||X_e-t_e||_2=o(1)`.  As above, the
polar partial isometry can be completed blockwise to a unitary intertwiner
`t'_e`, and singular-value truncation gives `||t'_e-t_e||_2=o(1)`.

The adjusted vertex maps together with the `t'_e` therefore form an exact
representation of the same graph-of-groups presentation on the same
`d_n`-dimensional space, with **exact regular type at every finite vertex** and
`o(1)` change on every fixed presentation generator.  Non-tree stable letters
which were `o(1)` from the identity remain so by the triangle inequality.  This
is precisely the claimed normalization.