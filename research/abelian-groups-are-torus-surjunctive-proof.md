---
rg: 2
id: abelian-groups-are-torus-surjunctive-proof
kind: route
title: Peel off the primary torsion components that the support meets, one prime at a time, and finish on a torsion-free finitely generated support group
target: abelian-groups-are-torus-surjunctive
requires:
  - torus-surjunctivity-lifts-through-normal-p-subgroups
  - torus-degree-regular-on-prime-power-residual-support
artifacts:
  - research/artifacts/torus-normal-p-lifting-2026-09-17.md
  - experiments/torus-normal-p-lifting-2026-09-17/check_normal_p_lifting.py
---

Artifact Section 3 (Theorem 7, Corollary 8).

1. `A = <supp D>` is finitely generated abelian. Let `p_1, ..., p_r` be the primes dividing
   `|A_tor|`, and let `N_j` be the sum of the `p_1`-, ..., `p_j`-primary components of the
   torsion subgroup of `G`. Each factor `N_j / N_(j-1)` is a locally finite abelian
   `p_j`-group, so a locally normal `p_j`-subgroup (`G` abelian).
2. The support of `p_(N_r)(D)` generates `A / (A cap N_r)`, which is torsion-free: if
   `m a in N_r` then `a` is torsion, so `a in A_tor subset N_r`. So it is `Z^k`, which is
   residually a finite 2-group, hence RPP.
3. By Claim (a) of `torus-surjunctivity-lifts-through-normal-p-subgroups`, `tau_(N_r)` is
   an injective torus automaton over `G / N_r`. By
   `torus-degree-regular-on-prime-power-residual-support` it is onto.
4. By the chain form of Claim (c), `tau` is onto. A bijective torus automaton has
   invertible degree (artifact Lemma 2).
