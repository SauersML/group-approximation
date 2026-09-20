---
rg: 2
id: coherent-literal-mark-torsion-codes-are-finitely-colorable
kind: claim
title: Coherent literal-mark torsion commutator codes have bounded chromatic number, so the collision escape needs incoherent row words
distinct_from:
  finite-prototype-column-codes-force-coset-collisions: that normalizes only the column and leaves unbounded normalized-row fibres as an escape; this also uses the literal diagonal mark on the row side, which bounds how many column values one row element can carry and closes that escape for coherent codes.
  binary-leavitt-tagged-shift-table-has-centralizer-collisions: that builds the exact tagged table and locates the open problem at the multi-predecessor edge comparison (CCC2); this shows that the tagged diagonal (CCC1) already has divergent area once each row element has one word, before any edge is filled.
  bounded-tagged-mark-seam-complex-has-finite-row-range: that roots conjugated marks in the centralizer of the mark z; this uses the centralizer of the row c, with the mark literally shared by two diagonal cells.
  finite-mark-centralizer-commutator-area-is-proper: that is the imported properness theorem for exact commutation; this transfers it to the marked fibre {y : [c,y]=z}, which is a translate of the centralizer.
---

**ESTABLISHED.**  Let `Gamma=<S|R>` be finitely presented.  Fix
finite-order prototype words `rho_1,...,rho_r` (rows) and
`beta_1,...,beta_s` (columns), and mark words `z_1,...,z_t`, each
nontrivial in `Gamma`.  Consider a finite graph `G` with vertex words
`c_v,h_v`, a mark label `mu(v) in {1,...,t}`, and constants
`A_Delta,A_0,B,C` such that the following hold.

- **(LM1) Literal marked diagonal.**
  `Area_R([c_v,h_v] z_(mu(v))^(-1)) <= A_Delta`.
- **(LM2) Edge commutation.**  `Area_R([c_w,h_v]) <= A_0` for every oriented
  edge `v -> w`.
- **(LM3) Torsion prototypes.**  There are words `e_v,b_v` with
  `Area_R(c_v (e_v rho e_v^(-1))^(-1)) <= B` for some row prototype `rho`,
  and `Area_R(h_v (b_v beta b_v^(-1))^(-1)) <= B` for some column
  prototype `beta`.
- **(LM4) Coherence.**  `Area_R(c_v c_(v')^(-1)) <= C` whenever
  `c_v=c_(v')` in `Gamma`, and `Area_R(h_v h_(v')^(-1)) <= C` whenever
  `h_v=h_(v')` in `Gamma`.

Then

```text
chi(G) <= 2 D_row D_col + 1,                                  (LM5)
```

where `D_row,D_col` depend only on the presentation, the prototypes, `t`,
and `A_Delta,A_0,B,C`.  They do not depend on `G`.  In particular, no family
satisfying (LM1)--(LM4) with uniform constants has unbounded chromatic
number, so no such family can feed `infinite-chromatic-commutator-code-kills-mf-mark`.

## The marked-fibre lemma

The only new ingredient is the following.  Let `c,x,y,z` be words with

```text
Area_R([c,x]z^(-1)) <= A,     Area_R([c,y]z^(-1)) <= A.
```

Then

```text
Area_R([c,x^(-1)y]) <= 2A.                                    (LM6)
```

If `c` has finite order, `finite-mark-centralizer-commutator-area-is-proper`
then puts `x^(-1)y` in the finite set `<c> Ball(R_c)`, with
`R_c=(2A+B_c)/A_c`.  So the marked fibre

```text
{ y in Gamma : Area_R([c,eta]z^(-1)) <= A for some word eta representing y }
```

is finite: commutator area is proper on it, just as it is on the centralizer.

## Corollary: the tagged shift diagonal

Take the tagged table of `binary-leavitt-tagged-shift-table-has-centralizer-collisions`
on one infinite orthogonal corner sequence.  Fix a source row `i` and one
word `c_i` for `x_12(A_i)`.  Every column
`h_(ij)=x_23(B_i+D_(ij))` with `j>i` satisfies `[x_12(A_i),h_(ij)]=z`.  The
differences

```text
h_(ij)^(-1) h_(ij') = x_23(D_(ij)+D_(ij'))
```

are pairwise distinct and nontrivial, and they meet `<x_12(A_i)>` only at
`1` (use the elementary matrix quotient).  So they lie in infinitely many
cosets of `<c_i>`, and (LM6) with properness gives

```text
sup_(j>i) Area_R([c_i,h_(ij)] z^(-1)) = infinity.             (LM7)
```

This holds for any column words.  If the vertex words `c_(ij)` are allowed
to depend on `j`, then `kappa_(ij)=Area_R(c_(ij)c_i^(-1))` enters
(LM1) at most twice, and the same argument gives

```text
lim_(j -> infinity) max( Area_R([c_(ij),h_(ij)]z^(-1)), kappa_(ij) ) = infinity
```

for every `i`.  So a bounded-area tagged code must use row words that are
unboundedly incoherent along every source row.  This constraint sits on the
diagonal (CCC1), and it is independent of the edge problem (CCC2) recorded
in the tagged node.

## What survives

The theorem fences every chromatic compiler that uses torsion rows and
columns, one word per group element and a finite mark palette.  That covers
the root involutions of the binary-Leavitt Steinberg group in
characteristic two and the involution and order-three words of Thompson's
`V`.  A surviving code needs at least one of the following:

1. **Incoherent words.**  The same row or column element carries words with
   unbounded comparison area, and the incoherence diverges as in (LM7).
2. **Unbounded mark conjugators.**  The marks `a_v z a_v^(-1)` do not come
   from a finite palette of words.  When `z` has finite order,
   `bounded-tagged-mark-seam-complex-has-finite-row-range` constrains these
   as well.
3. **Infinite-order rows or columns, or infinitely many prototypes.**  For
   example, the lifted group `T̄` is torsion-free, so none of the
   finite-mark fences apply to it.

No Property `(T)`, Kazhdan input, trace or matrix approximation is used.

DERIVATION
coherent-literal-mark-torsion-code-coloring-proof
