---
rg: 2
id: bounded-tagged-mark-seam-finiteness-proof
kind: route
title: Propagate the outer mark through the seam tree and apply centralizer-area properness
target: bounded-tagged-mark-seam-complex-has-finite-row-range
requires:
  - finite-mark-centralizer-commutator-area-is-proper
---

Choose a spanning tree of the mark-seam graph rooted at `o`.  Every vertex
has tree distance at most `K` from `o`.  Concatenating the seam diagrams in
`(MSC2)` along its root path gives

```text
Area_R(Z_v z^(-1))<=KB.                                  (MSCP1)
```

Because every seam word is null, connectedness also gives `Z_v=z` in
`Gamma`.  Hence every element represented by `g_v` belongs to
`C_Gamma(z)`, and `(MSCP1)` is the commutator-area bound

```text
Area_R([g_v,z])<=KB                                      (MSCP2)
```

up to inversion.

By `finite-mark-centralizer-commutator-area-is-proper`, only finitely many
cosets in `C_Gamma(z)/<z>` contain elements satisfying `(MSCP2)`.  Since
`<z>` itself is finite, the possible group elements represented by all the
`g_v` form one finite set `F_(K,B,z)`.

There are now only finitely many chart-carried row values

```text
g p_a g^(-1),             g in F_(K,B,z), 1<=a<=m.       (MSCP3)
```

A word of length at most `K` in this finite set and its inverses has only
finitely many possible values.  The finite list of assembly schemas cannot
increase that to an infinite set.  This proves the abstract conclusion.

For the tagged application, fix `i`.  If
`x_12(A_i+A_j)=x_12(A_i+A_k)`, the elementary-matrix quotient and root
injectivity give `A_j=A_k`, hence `j=k` by independence of the orthogonal
address rows.  Thus `(MSC4)` supplies infinitely many output values, which
contradicts the finite-row conclusion.
