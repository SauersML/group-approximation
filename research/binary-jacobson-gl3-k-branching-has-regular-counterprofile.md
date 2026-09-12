---
rg: 2
id: binary-jacobson-gl3-k-branching-has-regular-counterprofile
kind: claim
title: The Jacobson GL-three overlap branching table has a positive marked regular counterprofile
distinct_from:
  binary-jacobson-one-step-finite-type-envelope-is-marked-mf: that uses the regular representations of the finite vertex and edge groups to rule out a Hall deficit before any extra cell is imposed; this gives the complete complex branching table at the literal overlap and audits what remains after the two shortest cell relations are added.
  binary-jacobson-joint-shortest-cells-exclude-natural-completions: that obtains a genuine contradiction for natural characteristic-two head modules by following actual vectors; this proves that complex irreducible multiplicity and branching counts alone do not reproduce that vector-level obstruction.
  binary-jacobson-raw-cycle-selects-common-pi-intertwiner: that asks for one occurrence-authenticated operator between degree-two and degree-four packet algebras; this identifies the nonlinear block-holonomy information which is absent from the overlap branching ledger.
---

**ESTABLISHED.**  Let

```text
G=GL_3(F_2) ~= PSL_2(7),
K=GL(<e_1,e_3>) fixing e_2 ~= S_3.                       (JBR1)
```

Write `1,epsilon,tau` for the trivial, sign and two-dimensional standard
irreducibles of `K`.  For the six complex irreducibles of `G`, the complete
restriction table is

```text
G-type       degree    restriction to K                  r_alpha
-----------------------------------------------------------------
1              1      1                                     0
3              3      epsilon + tau                         2
3bar           3      epsilon + tau                         2
6              6      2*1 + 2*tau                           2
7              7      1 + 2*epsilon + 2*tau                 4
8              8      1 + epsilon + 3*tau                   4.   (JBR2)
```

Here `r_alpha` is the dimension of the negative eigenspace of the head
transvection `w=x_13(Q)`, which is an involution in `K`.  In particular every
nontrivial `G`-type has a positive marked part, and the marked part is exactly
one negative line in every `epsilon` or `tau` summand of `(JBR2)`.

For the finite vertex

```text
F=G_Q x G_P,
```

the regular multiplicity vector

```text
M_(alpha,beta)=d_alpha d_beta                            (JBR3)
```

is a strictly positive integral counterprofile for every homogeneous ledger
made only from:

* decomposition into complex `F`-types;
* restriction of the head factor to `K` by `(JBR2)`; and
* rank conservation under the `K`-central braid involution and the unitary
  words in the controlled-swap cell.

Indeed the restriction of `lambda_F` to `K` is

```text
4704 lambda_K,                                           (JBR4)
```

so its `1,epsilon,tau` multiplicities are respectively

```text
4704,                 4704,                 9408.        (JBR5)
```

The head mark has dimension

```text
(sum_alpha d_alpha r_alpha)(sum_beta d_beta^2)
 =84*168=14112=|F|/2.                                   (JBR6)
```

Consequently the two shortest Jacobson cells do not force a
dimension-independent type-cycle inequality merely by being unitary closed
paths: at the level of ranks, each path conserves the positive reservoirs in
`(JBR3)--(JBR6)`.  A successful all-complex-type argument must use additional
information not present in the branching ledger—an authenticated zero block,
a projective/determinant holonomy inside a multiplicity commutant, or a
matrix-selected compression on which the two path operators have genuinely
different support.

This does not assert that the regular counterprofile extends to a
finite-dimensional representation of the joint-cell quotient.  The exact
remaining finite problem is to decide the nonlinear matrix equations for the
`K`-commuting multiplicity gauges.  The claim rules out only a linear
branching/rank proof and leaves that holonomy problem explicit.

DERIVATION
binary-jacobson-gl3-k-branching-counterprofile-proof
