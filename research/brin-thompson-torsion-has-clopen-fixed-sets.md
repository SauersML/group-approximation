---
rg: 2
id: brin-thompson-torsion-has-clopen-fixed-sets
kind: claim
title: Torsion elements of Brin–Thompson groups nV fix clopen sets, so every minimal dihedral action by involutions of nV is free, and a finitely generated subgroup of nV is finite exactly when its level cocycle is a continuous coboundary
distinct_from:
  almost-automorphism-torsion-subgroups-are-rf: that proves residual finiteness of finitely generated torsion subgroups of the one-dimensional almost automorphism group (V, V_d, V_d(G)) by a depth cocycle and a pumping bound; this is the n-dimensional Brin–Thompson case, where pumping fails, and proves only the germ statement, the dihedral freeness and an exact finiteness criterion.
  brin-thompson-groups-contain-full-groups-of-their-elements: that shows topological full groups of elements of nV lie in nV; this constrains the fixed sets of torsion elements of nV and the dihedral subgroups they generate.
  fp-simple-groups-can-contain-infinite-finite-exponent-groups: that is the open question for finitely presented simple groups in general; this isolates, for the candidate hosts nV, exactly what a finiteness proof or a periodic example must do.
---

**ESTABLISHED** by `brin-thompson-torsion-has-clopen-fixed-sets-proof` (lane proof, bh-free-01,
elementary, not independently reviewed; no priority claimed). No imported theorems.

## Setting

`C = {0,1}^N`. An element of Brin's `nV` is a homeomorphism of `C^n` given by two partitions into
finitely many dyadic boxes and a bijection between them, acting on each box by a prefix replacement
`(p_1 w_1, ..., p_n w_n) -> (q_1 w_1, ..., q_n w_n)`. Its **level cocycle** is
`c_g(y) = (|q_1|-|p_1|, ..., |q_n|-|p_n|) ∈ Z^n` for any such box containing `y`.

## Statement

1. **Level cocycle.** `c_g` is well defined, locally constant, and satisfies
   `c_(gh)(y) = c_g(h y) + c_h(y)`.
2. **Clopen fixed sets.** If `g ∈ nV` has finite order and `g y = y`, then `c_g(y) = 0` and `g` is the
   identity on a neighbourhood of `y`. So `Fix(g)` is clopen, and every periodic subgroup of `nV` acts
   with trivial germs at its fixed points.
3. **Dihedral actions are free.** Let `a, b ∈ nV` be involutions generating `D_∞`, and let `Z ⊆ C^n` be
   an infinite closed `⟨a,b⟩`-invariant set on which the action is minimal. Then `⟨a,b⟩` acts freely on
   `Z`. Hence Nekrashevych's fragmentation construction (arXiv:1601.01033, Theorem 1.1: it needs a
   minimal `D_∞`-action in which `a` has a fixed point) can never be run with a dihedral subgroup of
   `nV`, on `C^n` or on any closed invariant subset.
4. **Finiteness criterion.** For a finitely generated `H ≤ nV`: `H` is finite if and only if there is a
   continuous `β : C^n -> Z^n` with `c_h(y) = β(h y) - β(y)` for all `h ∈ H`, `y ∈ C^n`.
5. **Periodic groups are orbitwise coboundaries.** If `H` is periodic, then on every orbit `H y` the
   cocycle is a coboundary: `β_y(h y) := c_h(y)` is well defined on `H y`. So
   `nV` is torsion locally finite **iff** for every finitely generated periodic `H ≤ nV` these orbitwise
   transfer functions can be chosen to form one continuous `β`.

## Use for Boone–Higman

- **Burnside hosts.** With `almost-automorphism-torsion-subgroups-are-rf` (which covers `n = 1`), item 4
  is the exact statement a finiteness proof for `nV`, `n ≥ 2`, must deliver to exclude
  `free-burnside-groups-satisfy-boone-higman` from Brin–Thompson hosts. Item 5 shows the only possible
  failure is **discontinuity or unboundedness** of the transfer, not a nonzero cocycle at a fixed point.
- **Periodic examples.** Item 3 rules out the most direct way to put a Grigorchuk–Nekrashevych periodic
  group into `nV`. What remains is the germ-resolved route of
  `brin-thompson-groups-contain-infinite-periodic-groups`.

## Scope

- Coordinate permutations are not allowed (Brin's `nV`). In variants that also permute coordinates,
  item 2 fails: the swap `(x, y) -> (y, x)` is an involution whose fixed set, the diagonal, is not open.
- Nothing here decides whether `2V` contains an infinite finitely generated periodic group.
