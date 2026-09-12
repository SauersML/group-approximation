---
rg: 2
id: center-chain-character-atom-gives-scalar-gram
kind: claim
title: The nonabelian center chain recovers scalar Gram but loses the Pauli carrier
artifacts:
  - research/center-chain-character-gram-proof.md
distinct_from:
  literal-selector-roots-force-center-chain: that proves the literal selector incidence destroys the commuting three-center packet; this shows that a nonabelian one-dimensional character still recovers the scalar overlap, and identifies simultaneous Pauli reduction as the exact remaining failure.
  binary-native-selector-atom-hecke-dichotomy: that gives the general intersection formula after a finite selector atom and its transports have been typed; this computes one concrete nonabelian atom for the literal chained-root words.
  binary-leavitt-native-two-scale-cross-gram-positive: that also requires the mixed source-Pauli commutators and the actual selector normal forms; this proves only the scalar Gram component and explicitly shows why the local Pauli arms do not reduce its carrier.
---

Use the literal chained realization from
`literal-selector-roots-force-center-chain`:

```text
C_1=x_42(q),                 C_2=x_54(q),
C_3=x_65(q),                 q=s_1t_1=q^2,
g_1=x_87(s_(00)t_0),         g_2=x_98(s_(000)t_(00)).  (CCG1)
```

The subgroup `H=<C_1,C_2,C_3>` is the six-root unitriangular group
`UT_4(F_2)` on the ordered indices `(6,5,4,2)`.  Let `chi:H->{+1,-1}` be
the one-dimensional character which sends the three simple roots
`C_1,C_2,C_3` to `-1`; it sends every derived root to `+1`.  Its regular
character atom

```text
e_chi=|H|^(-1) sum_(u in H) chi(u)u
```

has canonical trace

```text
tau(e_chi)=1/|H|=1/64.                                  (CCG2)
```

Both literal selector roots `g_1,g_2` have indices disjoint from the four
indices of `H`, so they centralize `H` and reduce `e_chi`.  Hence, with
`S_i=g_i e_chi`, one has the exact scalar Gram identity

```text
tau(S_1^*S_2S_2^*S_1)=tau(e_chi)=1/64.                 (CCG3)
```

Noncommutation of the centers therefore does **not** by itself kill all
positive selector Gram.  The failure is the label packet.  For the earlier
arms `A_1=x_47(a_1)` and `A_2=x_58(a_2)`,

```text
[C_2,A_1]=x_57(a_1) !=1,
[C_3,A_2]=x_68(a_2) !=1.                               (CCG4)
```

Conjugation by `A_1` or `A_2` moves `H` outside itself and therefore moves
`e_chi` in the regular representation.  Thus the atom in `(CCG2)` is not a
simultaneous reducing carrier for the anchored Pauli arms which authenticate
the fixed `1/4` and `1/8` selector labels.  Equation `(CCG3)` closes only the
scalar-overlap half of the proposed literal-root shortcut; it supplies
neither the mixed-Pauli commutator estimates nor the controlled-selector
normal forms required by the native cross-Gram claim.

DERIVATION
center-chain-character-gram-proof

