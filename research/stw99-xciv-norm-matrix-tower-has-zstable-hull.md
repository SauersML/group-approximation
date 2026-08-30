---
rg: 2
id: stw99-xciv-norm-matrix-tower-has-zstable-hull
kind: claim
title: A coherent norm-matrix tower has a Z-stable hull with tail-central copies
distinct_from:
  stw99-xciv-commuting-car-seed-has-zstable-hull: that theorem assumes one exact CAR copy in the relative commutant of the entire seed; this theorem only uses relative commutants of finite matrix stages, and applies to a weakly dense UHF core whose relative commutant in R is scalar.
  stw99-xciv-separable-zstability-iff-local-norm-central-z: that is a criterion quantified over every finite subset of the ambient algebra; this theorem verifies norm-centralization only for subsets approximated by one coherent matrix tower and directly identifies their UHF hull.
  stw99-xciv-two-norm-centrality-does-not-control-norm-centrality: that obstruction concerns tracial approximation and bad representatives; the hypothesis here is operator-norm approximation by a fixed increasing tower.
artifacts:
  - research/artifacts/stw99-xciv-norm-matrix-tower-audit-2026-08-30.md
---

Let `B` be a unital C\*-algebra and let `S subset B`.  Suppose there are
unital full matrix subalgebras

```text
A_1 subset A_2 subset ... subset B,       A_n ~= M_(r_n),
```

such that `r_n -> infinity` and

```text
dist(x,A_n) -> 0       (x in S)
```

in operator norm.  Then

```text
A=closure(union_n A_n)
```

is a separable infinite-dimensional UHF algebra, contains `S`, and is
`Z`-stable.  Thus `S` has a separable unital `Z`-stable hull in `B`.

The tower also gives actual finite-set norm control.  For every finite
`F subset S`, finite `G subset Z`, and `epsilon>0`, some `n` and some unital
homomorphism

```text
phi:Z -> A_n' intersect A subset B
```

satisfy

```text
||[x,phi(z)]|| < epsilon       (x in F, z in G).
```

In particular, fix a dyadic matrix model of the hyperfinite factor
`R=(union_n M_(2^n))''`.  Every subset of its norm-closed CAR core satisfies
the theorem, even though that core is weakly dense in `R` and hence has
scalar relative commutant in `R`.  This is an unconditional positive class
for Problem XCIV which is not covered by the exact commuting-CAR criterion.
