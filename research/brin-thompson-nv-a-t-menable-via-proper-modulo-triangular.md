---
rg: 2
id: brin-thompson-nv-a-t-menable-via-proper-modulo-triangular
kind: route
title: "One hole: a cnd function proper modulo T_n, averaged over permutations and shears, is proper on nV"
target: brin-thompson-groups-nv-are-a-t-menable
requires:
  - brin-thompson-nv-cnd-proper-modulo-triangular-subgroup
  - brin-thompson-nv-haagerup-iff-proper-modulo-triangular
---

Compared with `brin-thompson-nv-a-t-menable-via-triangular-split`, which needs R1 and R2, this route
needs R1 only: R2 follows from R1 by averaging over finitely many automorphic images of `T_n`.


Let `n ≥ 2`. By `brin-thompson-nv-cnd-proper-modulo-triangular-subgroup` there is a cnd function `ψ`
on `nV` proper modulo `T_n`. By (2) ⇒ (1) of `brin-thompson-nv-haagerup-iff-proper-modulo-triangular`,
`Σ_{t,σ} ψ ∘ α_σ^{-1} ∘ Ad(t)` is a proper cnd function, so `nV` has the Haagerup property.

**Necessity.** The hole is also necessary, by (1) ⇒ (2) of the same claim. So this route is an exact
reformulation of the goal, with one hole, and a counterexample to R1 refutes the goal.

**Forced shape of the hole.** By `brin-thompson-nv-no-cubical-action-proper-mod-triangular`, a
function for R1 is not a finite sum of wall counts, and on the Callard–Salo element it has
`ψ(f^N) → ∞` and `ψ(f^N) = O(log^8 N)`.
