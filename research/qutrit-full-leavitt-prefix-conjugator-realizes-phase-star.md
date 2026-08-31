---
rg: 2
id: qutrit-full-leavitt-prefix-conjugator-realizes-phase-star
kind: claim
title: A full binary Leavitt prefix conjugator realizes the qutrit three-to-one phase star
artifacts:
  - research/qutrit-full-leavitt-prefix-conjugator-proof.md
distinct_from:
  qutrit-jacobson-central-line-twist-is-similarity-impossible: that obstruction applies after the augmentation of the Jacobson chart, where the two order-three matrices have unequal fixed-space ranks; the full two-sided Leavitt algebra supplies rectangular module equivalences which erase that rank obstruction.
  qutrit-line-hnn-router-has-full-source-but-coincident-range: that adjoins an abstract stable letter over a finite edge; this constructs the router as an explicit matrix already inside the minimally almost periodic Leavitt elementary group.
  qutrit-external-cyclic-router-selects-only-one-hidden-third: that finite router loses a hidden third of every source phase; the present group element has the exact canonical Hecke star without a finite auxiliary head.
---

Let
`L=L_(F_2)(1,2)` be the binary Leavitt algebra with

```text
t_i s_j=delta_(ij),             s_0t_0+s_1t_1=1.
```

On the 27 qutrit leaves labelled by `(u_1,u_2,r) in F_3^3`, with one
additional fixed coordinate `star`, let

```text
J:(u_1,u_2,r) |-> (u_1,u_2,r+1),
Z:(u_1,u_2,r) |-> (u_1,u_2,r-u_1).
```

Put `C=<J,Z> isomorphic to C_3^2` and `h=J^2Z`. There is an explicit
`g in GL_28(L)=EL_28(L)` such that

```text
gJg^(-1)=h,                  C intersect gCg^(-1)=<h>.   (QLP1)
```

The matrix `g` uses only the standard binary comb prefix codes of sizes
`6,9,10,16`. In particular every entry is a finite sum of words `s_d t_e`,
its inverse is written by reversing the two rectangular prefix
equivalences, and `g` is a finite word in a fixed finite elementary
generating set of `EL_28(L)`.

Let `omega` be a primitive cube root of unity and let `e_a` be the
`C`-character projection with

```text
J | e_a = omega,             Z | e_a = omega^a
```

for `a in F_3`. The canonical group trace of the matrix subgroup
`Gamma=<C,g>` has the exact Hecke table

```text
e_b g e_a !=0  if and only if  b=2,
||e_2 g e_a||_2^2=1/27                          (QLP2)
```

for every `a,b in F_3`. Thus the full Leavitt chart realizes the
previously missing three-source-to-one-target qutrit phase star. It is
not a bounded-word accident and it cannot occur in the one-sided
Jacobson chart.

This positive selector is not yet a nonhyperlinearity certificate. If
`q=e_0+e_1+e_2` and `R=e_0+e_1`, every canonical matrix microstate
which has been exactified on the finite qutrit head satisfies

```text
||(1-q)gR||_(2,n)^2 >= 1/9-o(1).                       (QLP3)
```

The Hall excess is discharged by leakage into the other two
`J`-spectral thirds; no defining relation presently returns that leakage
to `q`. Indeed the finite packet together with only
`gJg^(-1)=h` has exact regular finite-dimensional models realizing the
same phase-star zero pattern. Therefore the prefix equivalence itself
forces a quantitative leakage law, not a uniform relator defect.

The subgroup `<F,g>`, for the finite qutrit head `F`, is a concrete
finitely generated subgroup faithfully embedded in `EL_28(L)`. No
finite presentation for this particular subgroup is produced here.
The next load-bearing object is an additional mixed relation of this
specific prefix matrix with elementary Leavitt roots which forces the
leaked `1/9` mass back into the selected qutrit corner.
