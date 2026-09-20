---
rg: 2
id: periodic-planar-rips-patterns-bend-to-finite-quotients
kind: claim
title: "Bending N periods of a generic translation-periodic planar pattern around a large circle gives a finite planar set whose Rips complex is the quotient of the periodic Rips complex by the N-th power of the translation"
distinct_from:
  some-finite-planar-set-has-a-non-wedge-rips-complex: that claim asks for a finite counterexample; this one is a geometric transfer lemma from periodic patterns to finite sets that holds for every generic pattern, wedge or not
  some-planar-rips-chain-gadget-multiplies-a-sphere-class: the gadget needs a separated finite local configuration and a multiplier of absolute value at least two; this lemma needs no separation and says nothing about multipliers
artifacts:
  - experiments/planar-rips-periodic-strip-2026-09-17/bend_check.py
  - experiments/planar-rips-periodic-strip-2026-09-17/results.txt
---

Let `M ⊆ R^2` be finite, `v ≠ 0`, `τ(y) = y + v`, and `Y = M + Zv`. Assume the
points `m + jv` (`m ∈ M`, `j ∈ Z`) are pairwise distinct. Let `r > 0` be
**generic**: `|y − y'| ≠ r` for all `y, y' ∈ Y`. (Only finitely many
`τ`-orbits of pairs are at distance `≤ 2r`, so genericity is a finite
condition. It fails only for `r` in the countable, locally finite set of
distances realised in `Y`.) Let `G` be the `r`-graph of
`Y`, and `R_r(Y)` its clique complex. Up to genericity, the open and closed
conventions agree.

Then there is `N_0` such that for every `N ≥ N_0` there is an injective map
`β_N : Y/⟨τ^N⟩ → R^2` with the following properties. Write
`X_N = β_N(Y/⟨τ^N⟩)`, a finite set of `N·|M|` points.

1. For distinct classes `p̄ ≠ q̄`: `|β_N p̄ − β_N q̄| ≤ r` if and only if some
   lifts `p, q` satisfy `|p − q| ≤ r`, and then the lift pair is unique up to
   applying `τ^N` to both. So the `r`-graph of `X_N` is `G/⟨τ^N⟩`.
2. `R_r(X_N) ≅ R_r(Y)/⟨τ^N⟩`. The quotient map `R_r(Y) → R_r(X_N)` is a
   regular covering with deck group `⟨τ^N⟩ ≅ Z`, i.e. an infinite cyclic
   covering with deck generator `τ^N`.
3. If `R_r(Y)` is connected, so is `R_r(X_N)`, and the covering is connected.

In particular `H_*(R_r(Y); k)` is a module over `k[t^{±1}]` with
`t = τ_*`. For every `N ≥ N_0` it is also the homology of a connected
infinite cyclic cover of the finite planar Rips complex `R_r(X_N)`, with
deck generator acting as `t^N`.

The lemma also runs in reverse, so it gives a computation. The twisted
chain complex `C_*(R_r(Y); k)` is a free `k[t^{±1}]`-complex of finite rank,
with one basis element per `τ`-orbit of cliques. So the module structure of
`H_*(R_r(Y); k)`, and hence the twisted Betti numbers of every `R_r(X_N)`,
come from a finite computation on one period.

## Attempts

- Proof in the companion route
  `periodic-planar-rips-patterns-bend-to-finite-quotients-proof`.
- Numerical check (`bend_check.py`, output in `results.txt`). Take a pattern
  with 12 orbits, period length 2.047 and margin 0.0037. Twisted Betti numbers
  on one period are `[1,1,1]` at `λ = 1` and `[0,0,1]` generically, so `H_2`
  is free of rank 1. For `N = 32` and `64` the `r`-graph of `X_N` equals
  `G/⟨τ^N⟩`, and `b(R_r(X_N)) = [1, 1, N]`, as the lemma and the
  Wang sequence predict. For `N = 8` and `16` the bending is too tight for
  this small margin: the graphs differ and `b_2 = 0`. This matches the
  lemma's `N ≥ N_0`.
