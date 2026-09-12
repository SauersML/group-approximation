---
rg: 2
id: full-depth-one-leavitt-menu-clifford-proof
kind: route
title: Close the finite role permutations and two-qubit Clifford automorphisms
target: full-depth-one-leavitt-menu-has-finite-clifford-model
requires:
  - closed-compression-fold-loop-retains-s3-gauge
  - binary-branch-flip-weyl-has-s3-c2-model
  - literal-whiteheads-give-gauged-moving-bridge-table
---

The first two requirements give one common finite matrix model for items
1--4 of `M_1`, with every coefficient occurrence literally reused.  The
remaining audit is finite.  A root-position Weyl word permutes the finite
coordinate-role set `Omega`.  On a Pauli pair, ordinary root conjugation
changes an exponent vector by a binary transvection; the branch flip swaps
the two two-bit Pauli blocks.  Permutations and binary transvections preserve
the Pauli commutator form, so their implementers belong to the finite
two-qubit Clifford group.

Represent a named occurrence by its role permutation together with its
controlled Pauli operator.  For an actor `g`, represent the occurrence in
the target chart by `gXg^(-1)`.  A mixed square comparing actor transport
with coefficient conjugation is then

```text
g(hXh^(-1))g^(-1)=(gh)X(gh)^(-1),
```

on both paths.  Hence every square in item 6 is exact.  Singer conjugation
only permutes the seven finite actor roles already present in the literal
Whitehead table, so it adds a finite permutation generator and does not
change the argument.

There are finitely many roles, the diagonal character group is finite, and
the two-qubit Clifford group is finite.  Their generated monomial group
`G_1` is therefore finite, proving `(DFC2)`.  The element `J` is nonidentity
in the explicit three-character model, so it remains nonidentity in `G_1`.
In the left regular representation every nonidentity translation has trace
zero, which proves `(DFC3)` and completes the firewall.

