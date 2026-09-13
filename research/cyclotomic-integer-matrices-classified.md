---
rg: 2
id: cyclotomic-integer-matrices-classified
kind: claim
title: Every connected integer symmetric matrix with spectrum in [-2,2] sits inside a toral or cylindrical tessellation, a sporadic graph on at most 16 vertices, or a 2 by 2 block
distinct_from:
  integral-operator-norm-below-two-is-quantized: that is the group-ring norm quantization below two, proved through Pólya's theorem; this is the literature classification of finite integer symmetric matrices of norm at most two, with no group in it
  atomic-serre-measures-are-equal-weight-real-orbits: that characterizes atomic Serre-class measures; this classifies finite integer matrices whose eigenvalues all have the form 2cos(2 pi r)
---

**ESTABLISHED (literature import)** by `cyclotomic-integer-matrices-classified-citation`.

J. McKee and C. Smyth, *Integer symmetric matrices having all their eigenvalues
in the interval [-2,2]*, arXiv:0705.3599v1 (24 May 2007); J. Algebra 317 (2007).
Read from the PDF, pages 2--8.

**Conventions (Sections 2--3).**
- A *cyclotomic matrix* is an integer symmetric matrix all of whose eigenvalues
  lie in `[-2, 2]`.
- It is *indecomposable* if its underlying graph is connected.
- One matrix is *contained in* another if it is obtained by deleting rows and
  the corresponding columns, i.e. it is an induced subgraph.
- *Equivalence* is conjugation by a signed permutation matrix, possibly followed
  by negation.

> **Theorem 1** ("Uncharged, signed, [−2,2]"). Every maximal connected cyclotomic
> signed graph is equivalent to one of the following: (i) For some `k = 3,4,...`,
> the `2k`-vertex toral tesselation `T_(2k)` shown in Figure 1; (ii) The 14-vertex
> signed graph `S_14` shown in Figure 3; (iii) The 16-vertex signed hypercube
> `S_16` shown in Figure 4. Further, every connected cyclotomic signed graph is
> contained in a maximal one.

> **Theorem 2** ("Charged, signed, [−2,2]"). Every maximal connected cyclotomic
> charged signed graph not included in Theorem 1 is equivalent to one of the
> following: (i) For some `k = 2,3,4,...`, one of the two `2k`-vertex cylindrical
> tesselations `C^(++)_(2k)`, `C^(+−)_(2k)` shown in Figure 6; (ii) One of the
> three sporadic charged signed graphs `S_7, S_8, S'_8` shown in Figure 7.
> Further, every connected cyclotomic charged signed graph is contained in a
> maximal one.

> **Theorem 3** ("Integer matrix, [−2,2]"). Every maximal indecomposable
> cyclotomic matrix is equivalent to one of the following: (i) The adjacency
> matrix of a maximal connected charged cyclotomic signed graph (given by
> Theorems 1 and 2); (ii) The `1 × 1` matrix `(2)` or the matrix `[[0,2],[2,0]]`.
> Further, every indecomposable cyclotomic matrix is contained in a maximal one.

**Shape of the infinite families (Figures 1 and 6).** The vertices of `T_(2k)`,
`C^(++)_(2k)` and `C^(+−)_(2k)` form `k` rungs of two vertices, and edges join
only vertices in the same or consecutive rungs, cyclically for `T_(2k)`. So every
ball of radius `r` in these graphs has at most `2(2r+1)` vertices. The sporadic
maximal graphs have at most `16` vertices. The paper remarks that every maximal
graph of Theorems 1 and 2 satisfies `A^2 = 4I`.
