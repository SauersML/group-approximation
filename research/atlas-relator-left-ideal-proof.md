---
rg: 2
id: atlas-relator-left-ideal-proof
kind: route
title: Read the infinite Bass--Serre kernel and identify one-sided augmentation generators
target: atlas-augmented-relator-ideal-not-left-finite
requires:
  - atlas-augmented-relations-have-unbounded-chart-width
  - atlas-charts-overlap-trivially
---

First prove `(RIL3)`.  Write `J=ker(k[F]->k[F/N])`.  If a set `S` generates
`N` as a group, the identities

```text
ab-1=a(b-1)+(a-1),
a^-1-1=-a^-1(a-1)
```

show that

```text
J=sum_(s in S) k[F](s-1).                              (RIL5)
```

Conversely suppose `J` is generated on the left by finitely many elements.
Expanding those elements in the standard group basis collects a finite set
`S subset N` such that `J=sum_(s in S)k[F](s-1)`.  Put `H=<S>`.  The quotient

```text
k[F] / sum_(h in H) k[F](h-1)
```

is the permutation module with basis the right cosets `F/H`.  Since
`n-1 in J` for every `n in N`, the cosets `nH` and `H` coincide; hence
`n in H`.  Thus `N=H` is finitely generated, proving `(RIL3)`.

Apply this to the Atlas kernel.  Both chart factors embed in `Gamma_+`, so
`N` acts freely on the Bass--Serre tree of `A8*A8`; hence `N` is free.  Its
quotient graph is the infinite locally finite chart-coset graph from
`atlas-augmented-relations-have-unbounded-chart-width`.  The kernel is
nontrivial because the mixed augmented relators are reduced nonidentity
words in the free product.  Translating one resulting cycle by `Gamma_+`
and using edge transitivity shows that every edge of the infinite quotient
graph lies in its core.  A graph with finitely generated fundamental group
has a finite core, so this infinite core proves that `N` has infinite free
rank.  Equation `(RIL3)` now gives `(RIL2)`.

Finally, if one fixed finite family `(RIL4)` computed the orbit-span in every
module, applying it to the left regular `P`-module would finitely generate
`I` on the left.  This contradicts `(RIL2)` and proves the bounded-saturation
no-go.

