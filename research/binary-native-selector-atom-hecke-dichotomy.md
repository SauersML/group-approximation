---
rg: 2
id: binary-native-selector-atom-hecke-dichotomy
kind: claim
title: A finite character atom makes native selector cross-Gram either fixed positive or exactly zero
artifacts:
  - research/binary-native-selector-atom-hecke-proof.md
distinct_from:
  finite-character-hecke-intersection-formula: that gives the general finite-subgroup coefficient formula; this specializes it to the ten-bit marked binary-Leavitt packet and the two actual selector occurrences.
  binary-leavitt-native-two-scale-cross-gram-positive: that must authenticate the two analytic selector transports as restrictions of the displayed group words and verify their relative action; this gives the complete scalar estimate after those two finite checks.
  marked-root-star-carries-three-anchored-cells: that puts the factor occurrences on one positive carrier but does not identify their products with the selector transports; this starts only after that occurrence identification has been made.
---

Let `Delta=St_20(L_2(F_2))`, let `z` be the fixed marked involutory root,
and let

```text
Z=<C_ij:1<=i,j<=3>~=(C_2)^9.                           (NSH1)
```

be a fixed commuting nine-root packet disjoint from `z`.  Put
`H=<z> times Z`, so `|H|=2^10`.  For a character `chi` of `H` with
`chi(z)=-1`, write

```text
e_chi=|H|^(-1) sum_(h in H) chi(h) h.                 (NSH2)
```

Let `g_1,g_2 in Delta` be the two fixed group words proposed for the actual
stabilized native selector occurrences, assume that they centralize `z`, and
put

```text
u=g_1^(-1)g_2,       I=H intersect uHu^(-1),
chi^u(a)=chi(u^(-1)au)       (a in I).                (NSH3)
```

If the two selector contractions on the selected atom are literally

```text
S_i=rho(g_i)rho(e_chi),                                (NSH4)
```

then the canonical cross-Gram moment has the exact dichotomy

```text
tau(S_1^*S_2S_2^*S_1)
 = |I|/|H|^2,             if chi|I=chi^u|I,
 = 0,                     otherwise.                  (NSH5)
```

Since `u` centralizes `z`, one has `<z><=I`.  In the compatible case,

```text
tau(S_1^*S_2S_2^*S_1)
 >=2^(-9) tau(e_chi).                                  (NSH6)
```

The same estimate, with `o(1)` loss, holds in every canonical normalized-HS
microstate sequence once the fixed finite subgroup and the two word
occurrences have been exactified.  Thus finite character packing completely
defeats orthogonal multiplicity reservoirs for these two *literal word
restrictions*: compatibility gives `(NCG1)` with `gamma>=2^(-9)`, while
incompatibility gives an exact zero fence.

This is a reduction, not a proof of the native cross-Gram claim.  The
current binary packet does not yet prove that the analytically stabilized
selector contractions are `(NSH4)`, nor does it compute the action of `u`
on the selected ten-bit atom.  Having the two coefficients literally among
the commuting roots is insufficient: compression to `e_chi` scalarizes
those roots, and moving one occurrence to an opposite root can move the
character atom.  The remaining work is exactly the finite occurrence and
character-compatibility check in `(NSH3)--(NSH4)`.

When `u` normalizes `H`, the compatibility test is just the finite equation

```text
chi=chi composed with Ad_(u^(-1)) on H.               (NSH7)
```

For a nine-bit sign matrix this is ordinary linear algebra over `F_2`.  In
particular, the tridiagonal matrix

```text
1 1 0
1 1 1
0 1 1
```

is invariant under reversal `1<->3`, but not under either adjacent
simultaneous row/column swap or their three-cycle.  Hence it gives positive
Hecke mass only if the actual relative selector action has the compatible
intersection type; it cannot be treated as an automatic overlap certificate.

DERIVATION
binary-native-selector-atom-hecke-proof
