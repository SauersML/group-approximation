---
rg: 2
id: balanced-greendlinger-separates-sign-cosets
kind: claim
title: Balanced mixed contours and Greendlinger separate the Pauli sign cosets
distinct_from:
  relative-c-sixth-protects-sign-double-cosets: that uses free-product syllable length and a minimum relator length; this works in ordinary word length and allows pure equality relators by peeling them first.
  gsc-does-not-separate-sign-double-cosets: that counterexample has one mixed contour with only two sign letters and violates the balance hypothesis here.
---

Let a symmetrized presentation have a disjoint alphabet

```text
S = D_X disjoint_union D_Z disjoint_union P_0 disjoint_union P_1
```

and split its relators into pure X relators, pure Z relators, and mixed
relators.  Assume the whole presentation satisfies classical `C'(lambda)`
for `lambda<=1/6`.  Write `P=P_0 union P_1`.  Suppose there is

```text
beta < 1-3 lambda                                                (BG1)
```

such that, in every mixed relator `r`, every cyclic interval containing at
most two `P`-letters has ordinary length at most

```text
beta |r|.                                                       (BG2)
```

Let `G` be the presented group and let `H_X=<D_X>`, `H_Z=<D_Z>`.  Then

```text
H_X P_0 H_Z  intersect  H_X P_1 H_Z = empty.                  (BG3)
```

The statement handles arbitrary composite van Kampen diagrams.  Its content
is that a double-coset collision has only two sign letters on its entire
outer boundary, while a mixed Greendlinger cell is forced by `(BG2)` to
expose at least three.

