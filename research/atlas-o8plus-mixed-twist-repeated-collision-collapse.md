---
rg: 2
id: atlas-o8plus-mixed-twist-repeated-collision-collapse
kind: claim
title: Every mixture of the two natural Omega8+(2) Q1920 twists collapses at every multiplicity
distinct_from:
  atlas-o8plus-type-a-repeated-collision-collapse: that treats homogeneous copies of only the dimension-12-centralizer twist; this permits arbitrary mixing with the other twist.
  atlas-o8plus-type-b-repeated-collision-collapse: that treats homogeneous copies of only the dimension-20-centralizer twist; this controls the nonzero inter-twist Hom spaces.
  atlas-o8plus-type-b-multiplicity-two-collision-collapse: that is a bounded-rank SAT exhaustion; this is an arbitrary-multiplicity free-associative-algebra theorem.
---

Fix either marked Q tuple.  Let `H_A,H_B` be the two eight-dimensional
`F2[Q]` modules obtained by restricting the natural `Omega8+(2)` module along
the two embedding twists, characterized by

```text
dim End_A(H_A)=12,          dim End_A(H_B)=20.
```

For arbitrary `a,b>=0`, let Q act diagonally on

```text
H_A^a + H_B^b.
```

Every A-central operator `c` satisfying

```text
c^2=1,       (ct)^3=1,       t c s c t^-1 c s t c=1
```

is `c=1`.  Thus no homogeneous or mixed direct sum of the natural
`Omega8+(2)` carrier types realizes the protected collision `S4`, in either
marking and at any multiplicity.

The claim is confined to direct sums of the two natural orthogonal twists;
it does not classify other indecomposable `F2[Q]`-modules.
