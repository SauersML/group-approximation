---
rg: 2
id: atlas-a8-mixed-block-transport-has-permutation-models
kind: claim
title: Every rational regular-A8 mixed-block transport has an exact permutation model
artifacts:
  - experiments/atlas-boundary-h-irrep-tangent.json
  - experiments/atlas-signed-group-algebra-irrep-screen.json
distinct_from:
  unitary-block-energy-transport: that sends every unitary to a transportation plan; this proves the converse for every rational regular-A8 plan after amplification and gives an exact permutation absorber.
  regular-subgroup-branching-is-hall-balanced: that balances a subgroup-restriction incidence graph; this treats the full two-chart minimal-Wedderburn block alphabet and all rational mixed mass profiles.
  atlas-fixed-packet-arithmetic-has-no-hs-gap: that gives the general multiplicity-semigroup closure theorem; this computes the concrete fourteen A8 degrees, constructs the realizing unitary, and identifies the exact Hall-gap mesh.
  finite-sheet-transport-networks-are-exactly-matricial: that realizes prescribed bijective transports on an arbitrary finite context network; this realizes arbitrary rational mass splitting between the 448 minimal regular-A8 Fourier blocks and computes the resulting Hall mesh.
---

**ESTABLISHED MIXED-BLOCK ABSORBER.**  The complex irreducible degrees of
`A8` are

```text
1,7,14,20,21,21,21,28,35,45,45,56,64,70,             (MBT1)
```

whose squares sum to `20160`.  In `k Reg(A8)`, each minimal Wedderburn
projection `p_(sigma,a)`, `1<=a<=d_sigma`, has rank `d_sigma k` and normalized
weight

```text
alpha_(sigma,a)=d_sigma/20160.                         (MBT2)
```

There are `448=sum_sigma d_sigma` such vertices on each chart.

Let `n_(u,v)` be **any** nonnegative integral table on the two copies of this
vertex set with margins

```text
sum_u n_(u,v)=d_v k,          sum_v n_(u,v)=d_u k.     (MBT3)
```

Then there is a permutation unitary `U in U(20160k)` such that

```text
||q_u U p_v||_2^2=n_(u,v)/(20160k)                    (MBT4)
```

for every mixed block.  Hence every rational transportation plan with the
regular-A8 marginals `(MBT2)` is realized exactly after choosing one common
amplification clearing its denominators.  Permutation models are dense in
the whole real transportation polytope as `k->infinity`.

This gives two sharp consequences.

1. Separate mixed-block ranks, masses, support integrality, and their
   amplification limits contain no finite-matrix-only obstruction.  Before
   relation-sensitive singular directions are used, the complete rational
   transport polytope already has exact finite models.
2. Every strict weighted Hall deficit on this minimal alphabet is an integer
   multiple of

   ```text
   1/20160.                                           (MBT5)
   ```

   Thus once the Atlas relators produce *any* genuinely deficient hard
   support graph, the dimension-free leakage gap is automatically at least
   `1/20160`; no separate quantitative estimate for `gamma` is needed.

The absorber does not satisfy the mixed Atlas kernel relations in general.
Its role is exact and narrower: it proves that those relations must delete or
spectrally shrink simultaneous directions *inside* the blocks `q_u U p_v`.
They cannot win through the concrete A8 multiplicities, rational block
masses, or finite transport integrality alone.
