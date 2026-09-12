---
rg: 2
id: literal-a1-head-forces-arbitrary-profile-native-cross-gram
kind: claim
title: The literal A1 finite head forces native cross-Gram mass in every operator-norm profile
artifacts:
  - research/literal-a1-head-cross-gram-profile-proof.md
distinct_from:
  full-q-a1-binary-extension-closes-zero-cross-block: that proves full central support in the canonical finite binary group but leaves faithfulness of the literal Steinberg lift open; this uses the faithful projective-head lift and converts full central support into a uniform trace-energy floor in every finite-dimensional profile.
  b2-b3-pair-full-hecke-four-native-sectors: that proves the common quarter source F has one quarter of the full-Q rank but gives no target overlap; this supplies the missing uniform positive target cross energy for that exact F.
  binary-leavitt-arbitrary-profile-native-cross-gram: that states the full frontier theorem; this proves its operator-norm finite-profile content using the additional ordinary occurrence A1 already present in the literal source-factor inventory.
---

**ESTABLISHED PROPERTY-`(T)`-FREE CROSS-GRAM FLOOR.**  Put

```text
F=Q(1+r)(1+l)/4,               g=J_1J_2,
h=FgF.                                                  (LAG1)
```

There is a constant `kappa>0`, depending only on the fixed literal finite
head

```text
H_A=<L_0,r,l,J_1,J_2,B_2,B_3,A_1><Delta,              (LAG2)
```

such that every exact finite-dimensional unitary representation `pi` of
`Delta` satisfies

```text
Tr(pi(h)^*pi(h)) >= kappa Tr(pi(F)).                    (LAG3)
```

The same inequality holds with `o(1)` loss for operator-norm asymptotic
representations after exactifying the fixed finite head.  Thus any profile
with positive normalized rank on the literal full-Hecke quarter source has
uniformly positive normalized-Hilbert--Schmidt native cross-Gram mass.

The proof uses no canonical trace: `(LAG3)` holds irreducible block by
irreducible block.  It uses no Property `(T)`, Kazhdan correction, spectral
gap, asymptotic commutant theorem, or representation-stability theorem for
the ambient group.  Only same-dimension operator-norm correction of one
fixed finite group is used.

DERIVATION
literal-a1-head-cross-gram-profile-proof
