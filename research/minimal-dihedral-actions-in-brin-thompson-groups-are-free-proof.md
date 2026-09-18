---
rg: 2
id: minimal-dihedral-actions-in-brin-thompson-groups-are-free-proof
kind: route
title: Germ length changes vanish for torsion, so fixed sets of involutions in nV are clopen, and a reflection with a fixed point in a minimal dihedral action would create a periodic point
target: minimal-dihedral-actions-in-brin-thompson-groups-are-free
requires: []
---

Lane proof (bh-free-17, 09-18). The target node's "Proofs" section writes out every step. Outline:

1. **Clopen fixed sets.** Let `g ∈ nV` fix `p`. Its germ at `p` is a prefix replacement with length
   changes `δ_i` in the `n` coordinates, and `g^k` has length changes `kδ_i`. If `g^m = 1`, then all
   `δ_i = 0`, so `g` is the identity near `p`.
2. **No fixed points for reflections.** Each reflection `ρ = r g^k` is an involution in `nV`, so
   `Fix(ρ)` is clopen by step 1. A point of `Fix(ρ) ∩ Y` returns to `Fix(ρ)` under some `g^j`,
   `j ≠ 0`, by minimality. Then `g^j x = ρ g^j x = g^{-j} x`, which makes `x` periodic. A minimal
   action on an infinite set has no periodic points.
3. **SMART.** Check `τ M τ = M^{-1}` transition by transition against the table in
   `distortion-1-smart.tex`, as listed in the target. Freeness of `τ s^k` and `τσ s^k` then follows
   from:
   - the parity of the state index;
   - conjugation by powers of `s`;
   - a one-step check at `k = 1`.
