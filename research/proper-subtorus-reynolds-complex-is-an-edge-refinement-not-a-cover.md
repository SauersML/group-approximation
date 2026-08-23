---
rg: 2
id: proper-subtorus-reynolds-complex-is-an-edge-refinement-not-a-cover
kind: claim
title: A proper-subtorus Reynolds complex refines edges but does not cover triangles
distinct_from:
  full-torus-reynolds-is-multipartite-curl: that identifies the full-torus column with an ordinary clique-complex curl; this compares a proper subtorus with the full-torus edge and triangle sets.
  multipartite-triangle-curl-has-uniform-infinity-green-bound: that constructs a uniformly bounded Green operator for the base clique complex; this proves why that operator does not lift to the extra-label sector.
  right-u-reynolds-has-torus-hecke-blocks: that decomposes the proper-subtorus domain into explicit torus-character blocks; this gives the global labeled-edge geometry and the obstruction to a covering-space contraction.
  fourth-power-mersenne-reynolds-levels-have-diagonal-crt-coupling: that produces an explicit unbounded-index composite family and isolates its right-unipotent blocks; this gives the exact edge-refinement model shared by all proper-subtorus levels.
---

**ESTABLISHED; COVERING-TRANSFER NO-GO.**  Let `Q` be a finite congruence
quotient with split projective torus `T`, let `H<T` be normalized by the
Weyl involution `w`, and put `i=[T:H]`.  Use the sign character of
`<H,w>` (respectively `<T,w>`) which is trivial on the torus and sends `w`
to `-1`.  The scalar input modules are

```text
E_H=Ind_(<H,w>)^Q sign,
E_T=Ind_(<T,w>)^Q sign.                                (PSE1)
```

The quotient of left cosets gives an `i`-to-one map of signed oriented
edge coordinates

```text
pi:E(H) -> E(T).                                       (PSE2)
```

Thus `E(H)` is the full-torus oriented-edge set with one extra label in
`T/H` (with the Weyl involution reversing the edge and inverting the
label).  Pullback along `(PSE2)` is an isometric inclusion

```text
pi^*:E_T -> E_H                                        (PSE3)
```

for the scalar infinity norm.

The two triangle sets do **not** acquire this label.  Put

```text
A=XS^2,             B=XRS,             A^3=B^3=1.
```

After removing the harmless threefold row repetition, the triangle rows
for both columns are the same two sets

```text
F_A=<A>\Q,             F_B=<B>\Q,                      (PSE4)
```

independent of `H` and `T`.  The three `H`-edge labels in a row are the
specific cosets represented by the three translates in `(DSS3)`.  Their
images under `(PSE2)` are exactly the three full-torus edges of the same
row.  Consequently

```text
C_H pi^* = C_T.                                        (PSE5)
```

Equation `(PSE5)` proves that the bounded full-torus Green theorem controls
the fiber-constant subspace of the proper-subtorus column.  It also proves
that the remaining issue is precisely the fiber-mean-zero edge sector.

Crucially, `(PSE2)` is not the one-skeleton of an `i`-sheeted cover of the
two-dimensional complex when `i>1`.  Such a cover would have `i|F_A|`
and `i|F_B|` lifted triangle rows.  The actual row sets `(PSE4)` have only
`|F_A|` and `|F_B|` rows: each base triangle selects one correlated triple
of edge labels rather than all `i` deck translates.  Hence no simplicial
lift of the bounded contraction from
`multipartite-triangle-curl-has-uniform-infinity-green-bound` is defined
on the extra-label sector.

For the explicit composite family

```text
M_n=4^n-1,       Q_n=SL_2(Z/M_n Z)/{+-I},
H_n=<h(2)>,      T_n=the split projective torus,
```

`fourth-power-mersenne-reynolds-levels-have-diagonal-crt-coupling` gives

```text
i_n=[T_n:H_n]=phi(M_n)/(4n) -> infinity.               (PSE6)
```

Thus `(PSE2)--(PSE5)` are an explicit growing labeled-edge family with no
corresponding growth in triangle lifts.  This is a rigorous obstruction to
the proposed **covering-space** proof of a uniform Green bound.  It is not
a divergent Green mode: the Moore--Penrose inverse may still be uniformly
bounded because the selected label triples can couple the fiber-mean-zero
sector efficiently.

The exact remaining theorem is therefore finite and concrete.  On the
orthogonal complement of `(PSE3)` and of `ker(C_(H_n))`, prove a uniform
infinity Green bound, or construct `f_n` in that sector with

```text
||f_n||_infinity /
max(||C_(1,H_n)f_n||_infinity,||C_(2,H_n)f_n||_infinity)
 -> infinity.                                          (PSE7)
```

The base multipartite contraction settles none of `(PSE7)` because its
entire image lies in the fiber-constant summand `(PSE3)`.
