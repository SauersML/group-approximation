---
rg: 2
id: atlas-separate-chart-module-ledger-blindness-proof
kind: route
title: Conjugate every restricted chart module and isolate the mixed intersection boundary
target: atlas-separate-chart-module-ledger-is-kernel-blind
requires:
  - atlas-repeated-h6-gauge-is-one-gl2m-coordinate
  - atlas-fixed-packet-arithmetic-has-no-hs-gap
---

For `(SML2)`, multiplication by `T` is an explicit `F2[K]`-module
isomorphism from `Res_K(rho_m^T)` to `Res_K(rho_m)`.  The second isomorphism
is the definition of the repeated natural module.  This argument applies to
every marked subgroup separately and does not use either collision word.
It therefore holds before restricting to either exact kernel stratum.

Fixed spaces commute with an inert multiplicity factor, giving

```text
Fix_K(V tensor M)=Fix_K(V) tensor M.
```

The centralizer algebra likewise satisfies

```text
End_K(V tensor M)=End_K(V) tensor End(M),
```

which proves `(SML4)`.  Module isomorphism preserves the complete extension
structure, so the composition-factor and `K0` assertions are weaker immediate
consequences.  The amplification statement for finite residues is exactly
the established fixed-packet arithmetic no-gap theorem.

It remains to justify the Lipschitz boundary `(SML6)`.  Set
`F=Fix_K(E)`, `G=Fix_L(E)`, and `r=rank(T-T')`.  On

```text
Q=ker(T-T')
```

the maps `T` and `T'` agree, while `codim(Q)<=r`.  Therefore

```text
F intersect T^-1 G intersect Q
 =F intersect T'^-1 G intersect Q.
```

Intersecting either of the two spaces in `(SML5)` with a codimension-`r`
subspace can lower its dimension by at most `r`.  Since the intersections
inside `Q` agree, their dimensions differ by at most `r`.  Direct-sum
additivity is immediate.

Thus separate restriction data are identically constant, while the first
available additive rank-Lipschitz coordinates are mixed relative-position
data.  No claim is made that `(SML5)` itself separates the two word-zero
strata.
