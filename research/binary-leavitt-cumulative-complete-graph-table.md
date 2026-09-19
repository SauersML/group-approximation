---
rg: 2
id: binary-leavitt-cumulative-complete-graph-table
kind: claim
title: Cumulative binary Leavitt rows realize exact marked complete commutator graphs
distinct_from:
  binary-leavitt-shift-graph-has-exact-marked-commutator-table: that folds two source addresses at vertices indexed by ordered pairs and realizes sparse shift graphs; this uses cumulative rows and adjacent column pairs to realize complete graphs with one-indexed canonical vertex words.
  leavitt-prefixes-form-exponential-heisenberg-packet: that uses the complete equality/off-diagonal table on all row-column address pairs; this uses a triangular cumulative pairing in which every later row kills an earlier adjacent column pair by characteristic-two cancellation.
  binary-leavitt-bounded-area-chromatic-code: that additionally requires uniform filling area in one fixed finite presentation; this proves the exact complete-graph identities and removes pair-dependent vertex charts but leaves uniform wordization open.
artifacts:
  - research/property-t-free-leavitt-full-mf-radical.md
---

**ESTABLISHED.**  Put

```text
R=L_(F_2)(1,2),          q=s_1t_1,
Delta=St_20(R),          z=x_13(q).
```

For every `M>=2`, choose `M` distinct binary prefixes
`alpha_0,...,alpha_(M-1)` of one common depth.  In the corner `qRq`, put

```text
A_r=s_1 t_(alpha_r) t_1,       B_r=s_1 s_(alpha_r) t_1.       (LCG1)
```

Then

```text
A_r B_s=delta_(rs)q.                                         (LCG2)
```

For `0<=j<M-1`, define the cumulative row and adjacent column pair

```text
C_j=A_0+...+A_j,                H_j=B_j+B_(j+1),              (LCG3)
c_j=x_12(C_j),                  h_j=x_23(H_j).                (LCG4)
```

Then the full pairing table is diagonal:

```text
[c_j,h_j]=z,                                                   (LCG5)
[c_k,h_j]=1                         whenever j!=k.              (LCG6)
```

Thus each `K_(M-1)` carries an exact marked commutator table, and their
disjoint union is an exact code of infinite chromatic number.  Every vertex has one canonical
index.  In particular, no ordered-pair transporter, global endpoint section,
or diagonal conjugator `a_j` occurs in the algebraic table.

Equivalently, in the finite prefix matrix chart the row vectors

```text
v_j=e_0+...+e_j
```

and columns `w_j=e_j+e_(j+1)` are dual (adjoin the last column
`w_(M-1)=e_(M-1)`).  Hence one lower-triangular change of basis simultaneously
normalizes the *whole* table.  This is global finite-packet coherence, not a
separate simultaneous conjugator for each ordered pair.

The statement does not assert a uniform filling-area bound for `(LCG5)--(LCG6)`
in a fixed finite presentation of `Delta`.  Its gain is that the remaining
word problem is now triangular and one-indexed: uniformly wordize one global
cumulative/adjacent dual-basis chart.  The older pair-chart holonomy is no
longer built into the vertex definitions.
