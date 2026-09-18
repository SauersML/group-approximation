---
rg: 2
id: bhm-singfix-finiteness-holds-for-type-fp-n
kind: claim
title: Belk–Hyde–Matucci's finiteness theorem for finite germ extensions holds verbatim with type FP_n in place of type F_n
distinct_from:
  bhm-singfix-condition-forces-fp-germ-groups: that is a consequence of the one-point hypothesis of Theorem 2.1 in its homotopical form; this is the homological form of Theorem 2.1 and Corollary 2.10 themselves.
  ha2-actions-give-fp2-twisted-brin-thompson-groups: that is the homological finiteness of twisted Brin–Thompson groups from [HA_2] actions; this is the homological finiteness of finite germ extensions.
---

**ESTABLISHED** (lane proof, bh-free-08, 2026-09-18; a check of the published argument; not reviewed; no novelty claimed).

## Statement

Let `G` be a finite germ extension of `B ≤ Homeo(X)` in the sense of Belk–Hyde–Matucci
(arXiv:2407.03149v1), and let `n ≥ 1`. Suppose that:
1. `B` acts on `sing(G)^n` with finitely many orbits;
2. `SingFix_G(M,M')` has type `FP_n` over `Z` for all `M ⊆ M' ⊆ sing(G)` with `|M'| ≤ n`.

Then `G` has type `FP_n`. Likewise, Corollary 2.10 holds with `FP_n` throughout. Its hypothesis (3)
in the normal clause then reads: `(B)_p ⊴ (G)_p` and `(G)_p/(B)_p` has type `FP_n`.

## Proof

The proof of Theorem 2.1 (TeX lines 454–473) uses three facts:
- the sublevel complex `K_{≤n}` of the germ complex satisfies `H̃_i(K_{≤n}) = 0` for `i ≤ n−1`. Line 460 derives this from Bestvina–Brady Corollary 2.6, *before* passing to `π_1`;
- `G` has finitely many orbits of cubes in `K_{≤n}` (Proposition `prop:FinitelyManyOrbitsCells`, from hypothesis 1);
- each cube stabilizer contains some `SingFix_G(M,M')` with finite index (Proposition `prop:CellStabilizers` and line 416).

`FP_n` passes to finite-index overgroups. By the homological form of Brown's criterion, a group
acting cellularly on an `(n−1)`-acyclic complex with finitely many cell orbits and cell stabilizers
of type `FP_n` has type `FP_n` (K. S. Brown, *Finiteness properties of groups*, JPAA 44 (1987),
Proposition 1.1; recalled, not re-read). This replaces the homotopical statement at line 471.

The two propositions behind Corollary 2.10 (lines 503–525) are group-theoretic:
- `SingFix_G(M,M')` contains `Fix_B(M')` with finite index;
- or `SingFix_G(M,M')` is an extension of a finite-index subgroup of `∏_{p∈M} (G)_p/(B)_p` by `Fix_B(M')`.

`FP_n` is closed under finite-index passage and under extensions, so the corollary transfers too. ∎
