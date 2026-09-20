---
rg: 2
id: sl4z-odd-central-sector-bott-is-realizable
kind: claim
title: Some asymptotic homomorphism of SL_4(Z) sending -I near -1 has nonzero Bott index on the block-swap torus in a g-eigenspace
distinct_from:
  weak-matricial-stability-kills-centralizer-even-cohomology: that is an abstract vanishing theorem for all linear groups, whose proof would realize classes through Kasparov theory; this asks for one explicit asymptotic homomorphism of one group, and it would refute stability of SL_4(Z) on its own.
  sl4z-delocalized-bott-lives-in-odd-central-sector: that constrains every asymptotic homomorphism (even central sector dead, odd sector antisymmetric) and realizes the invariant on the normalizer of F; this asks for realization on the whole group.
artifacts:
  - research/artifacts/laurent-sl4-delocalized-bott-2026-09-16.md
---

**OPEN.** In the notation of `sl4z-delocalized-bott-lives-in-odd-central-sector`, there is
an asymptotic homomorphism `φ_n : SL_4(Z) → U(k_n)` with `β_{+,−}(φ_n) ≠ 0` for infinitely
many `n`. Equivalently, by that claim, `β_{−,−}(φ_n) ≠ 0`.

## Why it matters

Part 1 of `sl4z-delocalized-bott-lives-in-odd-central-sector` then refutes matricial
stability of `SL_4(Z)` directly, with no Kasparov theory
(`sl4z-instability-from-odd-sector-bott`).

## Constraints on a construction

- The `c = +1` part of `φ_n` carries nothing. So one may assume `φ_n(−I) = −1`, i.e. work
  with asymptotic projective representations of `PSL_4(Z)` with the nontrivial central sign.
- The construction is not induced from a normal finite-index subgroup avoiding `g`, and not
  a sum of such a model with genuine representations (part 5).
- It exists on the normalizer `Δ' = N_{SL_4(Z)}(F)` (part 6). What is needed is an extension
  of such a model across the infinite-index inclusion `Δ' ⊂ SL_4(Z)`.

## Attempts

- **Induction from finite index.** Dead, by part 5 of
  `sl4z-delocalized-bott-lives-in-odd-central-sector`.
- **Direct extension from `Δ'`.** Not attempted in detail. `Δ'` contains the unipotent
  `M_1, M_2`. The Steinberg relations of `SL_4(Z)` tie these elements to others outside
  `Δ'`, which is the rigidity question already noted in the Attempts of
  `sl4z-matricially-stable`.
