---
rg: 2
id: no-a3-b3-and-cyclic-type-artin-groups-have-solvable-wp
kind: claim
title: Artin groups without a (2,3,m) triple with m at most 4, and Artin groups of cyclic type, have solvable word problem
distinct_from:
  known-artin-classes-have-solvable-word-problem: that imports the right-angled, spherical, euclidean, FC-type, large-type, 2-dimensional and rank-three classes; this imports two further classes from different sources, one containing the large-type and 2-dimensional cases and one containing the hyperbolic cyclic types.
---

Let `Γ` be a Coxeter graph on a finite set `S`. Its *Dynkin diagram* has vertex set `S` and
an edge for each pair with `m_st ≥ 3`, carrying the label `m_st`.

1. Suppose there are no pairwise distinct `x, y, z ∈ S` with `m_xy = 3`, `m_xz = 2` and
   `m_yz ∈ {2, 3, 4}`. Then `A_Γ` has solvable word problem.
2. Suppose `A_Γ` is of *cyclic type*. That is, the Dynkin diagram is a cycle with no label
   `∞`, and `W_T` is finite for every proper subset `T ⊊ S`. Then `A_Γ` has solvable word
   problem.

See route `no-a3-b3-and-cyclic-type-artin-wp-citation`.

**Remarks.**
- Class (1) contains:
  - the right-angled groups and the groups with no label 3, since they have no
    `m_xy = 3`;
  - the large-type groups, since they have no label 2;
  - the groups of dimension at most 2, since a triple with labels `3, 2, m` and `m ≤ 4`
    has `1/3 + 1/2 + 1/m > 1`.
- Class (1) is the class of the source under its most restrictive reading.
  - The source's usage supports the larger class with `m_yz ∈ {3, 4}`, so that
    reducible triples `A_2 × A_1` are allowed.
  - That larger class is not claimed here.
- Groups of cyclic type have only finite labels. They include the hyperbolic Coxeter
  4-cycles with labels `(3,3,3,4)`, `(3,3,3,5)`, `(3,4,3,4)` and `(3,4,3,5)`. Each of these
  contains a triple excluded in (1), so (2) is needed for them.
