---
rg: 2
id: stw99-xciv-norm-matrix-tower-has-zstable-hull
kind: claim
title: Uniformly large Bratteli tails give Z-stable hulls and tail-central copies
distinct_from:
  stw99-xciv-commuting-car-seed-has-zstable-hull: that theorem assumes one exact CAR copy in the relative commutant of the entire seed; this theorem constructs approximate central copies from large finite-dimensional tail multiplicities even when the whole seed has scalar relative commutant.
  stw99-xciv-separable-zstability-iff-local-norm-central-z: that is a criterion quantified over every finite subset of the ambient algebra; this theorem verifies norm-centralization for subsets approximated by one coherent finite-dimensional tower satisfying a checkable Bratteli multiplicity condition.
  stw99-xciv-two-norm-centrality-does-not-control-norm-centrality: that obstruction concerns tracial approximation and bad representatives; the hypothesis here is operator-norm approximation by a fixed increasing tower.
artifacts:
  - research/artifacts/stw99-xciv-norm-matrix-tower-audit-2026-08-30.md
---

Let `B` be a unital C\*-algebra and let `S subset B`.  Suppose there are
increasing unital finite-dimensional subalgebras

```text
F_1 subset F_2 subset ... subset B
```

such that `dist(x,F_n)->0` for every `x in S`.  Write

```text
F_n ~= direct_sum_i M_(r_(n,i)).
```

For `m>=n`, let `mu^(n,m)_(j,i)` be the multiplicity with which the `i`-th
block of `F_n` acts in the `j`-th block of `F_m`.  Assume the uniform Bratteli
tail condition

```text
for every n,N, some m>=n has
mu^(n,m)_(j,i)>=N whenever mu^(n,m)_(j,i)>0.            (UBT)
```

Then

```text
A=closure(union_n F_n)
```

is approximately divisible and hence `Z`-stable.  It contains `S`, so it is
a separable unital `Z`-stable hull of `S` in `B`.

More strongly, every tail relative commutant

```text
C_n=F_n' intersect A
```

is approximately divisible and `Z`-stable.  Consequently, for every finite
`E subset S`, finite `G subset Z`, and `epsilon>0`, some `n` and some unital
homomorphism `phi:Z->C_n subset B` satisfy

```text
||[x,phi(z)]|| < epsilon       (x in E, z in G).
```

Condition (UBT) includes every increasing full-matrix tower with unbounded
matrix sizes, but also allows arbitrary finite-dimensional Bratteli diagrams
whose nonzero tail multiplicities grow uniformly.  Thus this strictly
extends the UHF-core positive class for Problem XCIV to approximately
divisible AF norm cores inside `R`.
