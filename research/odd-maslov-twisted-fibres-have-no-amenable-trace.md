---
rg: 2
id: odd-maslov-twisted-fibres-have-no-amenable-trace
kind: claim
title: Every odd degree-six Maslov fibre has no amenable trace
distinct_from:
  deligne-twisted-fibres-have-no-amenable-trace: that treats the two nontrivial mod-three fibres of the triple cover; this also treats the order-six odd fibres needed when the target is metaplectic.
  finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres: that excludes finite exact coefficient shifts; this combines the same finite-dimensional invisibility with C-star property T to exclude amenable traces.
---

Let `Gamma=Sp_4(Z)` and let

```text
A_theta=C^*(Gamma; exp(2 pi i theta b))
```

for the Maslov cocycle `b`.  If

```text
theta in {1/3,2/3,1/6,5/6},                            (OMAT1)
```

then `A_theta` has no amenable tracial state.

For `theta=1/3,2/3` this is
`deligne-twisted-fibres-have-no-amenable-trace`.  For
`theta=1/6,5/6`, the fibre `A_theta` is a central summand of `C^*(E_6)`.
The finite central extension `E_6` has property `(T)`, so the summand has
C-star property `(T)`.  An amenable trace would therefore yield a nonzero
finite-dimensional representation of `A_theta` by
`property-t-cstar-amenable-trace-forces-fd-quotient`.  But such a
representation is nontrivial on the full finite residual

```text
<z^2>=Z/3  in  1 -> Z/3 -> E_6 -> E_2 -> 1,
```

contradicting
`finite-metaplectic-morita-shifts-cannot-reach-odd-maslov-fibres` (or its
finite-residual argument directly).  Thus all four odd difference fibres
obey the same amenable-trace obstruction.

This remains weaker than failure of Connes embeddability: it excludes
Folner compressions of exact odd projective representations, not arbitrary
matrix-ultraproduct models.
