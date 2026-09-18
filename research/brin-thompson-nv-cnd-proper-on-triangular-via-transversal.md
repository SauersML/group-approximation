---
rg: 2
id: brin-thompson-nv-cnd-proper-on-triangular-via-transversal
kind: route
title: "R2 follows from R1: averaging a transversal function over permutations and shears gives a proper function, which is proper on T_n"
target: brin-thompson-nv-cnd-proper-on-triangular-subgroup
requires:
  - brin-thompson-nv-cnd-proper-modulo-triangular-subgroup
  - brin-thompson-nv-haagerup-iff-proper-modulo-triangular
---

Let `n ≥ 2`. By `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup` some cnd function is proper
modulo `T_n`. By (2) ⇒ (1) of `brin-thompson-nv-haagerup-iff-proper-modulo-triangular`, `nV` has a
proper cnd function `Ψ`. Its restriction to `T_n` has finite sublevel sets, so `Ψ` is proper on `T_n`.

So R2 is not an independent prerequisite of `brin-thompson-nv-a-t-menable-via-triangular-split`. Any
obstruction found for R2 (for example relative property (T) for the central direction of
`C(C,Z) ⋊ V ≤ T_n`) is an obstruction to R1.
