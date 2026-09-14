---
rg: 2
id: fp-simple-full-mf-radical-from-boone-higman
kind: route
title: Feed the rank-twelve Leavitt group to Boone-Higman and push its radical up the inclusion
target: fp-simple-full-mf-radical-group
requires: [boone-higman-conjecture, rank-twelve-leavitt-simple-non-mf, rank-twelve-leavitt-elementary-wp-decidable, mf-radical-functoriality]
artifacts:
  - research/artifacts/boone-higman-mf-radical-bridge-2026-09-11.md
---

Put `R=L_(F_2)(1,2)` and `H=EL_12(R)`.

## The input is admissible

By `rank-twelve-leavitt-simple-non-mf`, `H` is nontrivial, finitely
generated and simple, with `Rad_MF(H)=H`. By
`rank-twelve-leavitt-elementary-wp-decidable`, `H` has decidable word
problem. So `H` is a finitely generated group with solvable word problem,
which is exactly the hypothesis of `boone-higman-conjecture`.

## The envelope inherits the radical

Assume the conjecture. It supplies a finitely presented simple group `K` and
an embedding

```text
iota : H -> K.                                               (BHR1)
```

Apply `mf-radical-functoriality` to `iota`:

```text
iota(Rad_MF(H)) <= Rad_MF(K).                                (BHR2)
```

Since `Rad_MF(H)=H`, the left side is `iota(H)`, so `Rad_MF(K)` contains
`iota(H)`, which is nontrivial because `H` is nontrivial and `iota` is
injective.

`Rad_MF(K)` is the intersection of the kernels of the corona representations
of `K`, hence an intersection of normal subgroups, hence normal in `K`. It is
a nontrivial normal subgroup of a simple group, so

```text
Rad_MF(K) = K.                                               (BHR3)
```

`K` is finitely presented and simple, so it witnesses
`fp-simple-full-mf-radical-group`. `∎`

## What this route does and does not use

It uses nothing about `H` beyond the four requirements, and in particular no
property of the Leavitt algebra beyond what those claims already record. Any
other finitely generated group with solvable word problem and full MF radical
would do; `H` is named because it is the one this repository has.

It does **not** show that the conjecture is equivalent to the target: a single
finitely presented simple group with full MF radical says nothing about
embedding arbitrary solvable-word-problem groups. The implication runs one
way, and its value is the contrapositive recorded in the target's body.
