---
rg: 2
id: minimal-dihedral-actions-in-brin-thompson-groups-are-free
kind: claim
title: Involutions of nV have clopen fixed sets, so every minimal dihedral action by elements of nV is free, and SMART's time reversal is a cellwise symbol swap outside 2V
distinct_from:
  smart-trace-full-group-embeds-in-brin-thompson-2v: that puts the full group of SMART's trace subshift inside 2V; this shows the dihedral (reversal) symmetries of SMART lie outside 2V and act freely, so Nekrashevych's periodic fragmentations cannot be built from them inside 2V.
  bs13-in-3v-via-smart-renormalization: that uses SMART's ternary renormalization for BS(1,3); this is about involutions and dihedral actions, not renormalization.
---

**ESTABLISHED** (lane proof, elementary, not reviewed; no novelty claimed).

## Statement

Let `nV` act on `C^n`, `C = {0,1}^N` (or any finite alphabet).

1. **Finite-order elements have clopen fixed sets.** If `g ∈ nV` has finite order, then
   `Fix(g)` is clopen.
2. **Minimal dihedral actions inside nV are free.** Let `Y ⊆ C^n` be clopen, let
   `g ∈ nV` preserve `Y` and act minimally on the infinite set `Y`, and let `r ∈ nV` be an
   involution with `r(Y) = Y` and `r g r = g^{-1}` on `Y`. Then every reflection
   `r g^k` (`k ∈ Z`) is fixed-point free on `Y`, so `⟨g, r⟩ ≅ D_∞` acts freely on `Y`.
3. **SMART's reversal symmetry.** For the SMART machine of Callard–Salo
   (arXiv:2208.00685, TeX `distortion-1-smart.tex`, read at source; states
   `b_i, d_i, p_i, q_i`, `i ∈ {1,2}`, alphabet `{0,1,2}`), let `π = (1 2)` act on every tape
   cell and let `θ` be the fixed-point-free state involution
   `b_1↔q_2, b_2↔q_1, d_1↔p_2, d_2↔p_1`. Then `τ = θ∘π` conjugates the moving-tape map `s`
   of SMART to `s^{-1}`. The map `τ` normalizes the ternary Brin–Thompson group `2V_3` but
   is not in it (it changes infinitely many cells), and every reflection `τ s^k` and
   `τσ s^k` (`σ` the space mirror) is fixed-point free.

## Proofs

**1.** Let `p ∈ Fix(g)`. On a brick `D = [u_1]×…×[u_n] ∋ p` the element `g` acts by
`(u_i y_i)_i ↦ (u'_i y_i)_i`, so its germ at `p` is a prefix replacement with length changes
`δ_i = |u'_i| − |u_i|`. Since `g(p) = p`, points near `p` are mapped into `D`, so the germ of
`g^k` at `p` is the `k`-fold composite: a prefix replacement with length changes `k δ_i`. The
germ of `g^m = 1` has all length changes `0`, so `δ_i = 0` for all `i`. Then `u_i` and `u'_i`
are prefixes of `p_i` of the same length, hence equal. So `g` is the identity on `D`, and `p`
is interior to `Fix(g)`.

**2.** Each `r g^k` is an involution in `nV`, so by 1 its fixed set `F` is clopen. If
`F ∩ Y ≠ ∅`, minimality gives `x ∈ F ∩ Y` and `j ≠ 0` with `g^j x ∈ F`. Put `ρ = r g^k`, so
`ρ g ρ = g^{-1}`. Then `g^j x = ρ(g^j x) = g^{-j} ρ x = g^{-j} x`, hence `g^{2j} x = x`: a
periodic point of a minimal action on an infinite set, which is impossible.

**3.** Transition-by-transition check against the table. Moves: SMART has
`b_2 →R b_1, p_2 →R p_1, d_2 →L d_1, q_2 →L q_1`; its inverse has
`b_1 →L b_2, p_1 →L p_2, d_1 →R d_2, q_1 →R q_2`, and `θ` sends each inverse move to a SMART
move in the same direction (for example `b_1 →L b_2` to `q_2 →L q_1`). Writes: inverting
`(q, a, q', b)` gives `(q', b, q, a)`. After applying `π` to both symbols, the inverse write
states become exactly `θ` of SMART's write states. For example, the inverse `b_2` becomes
`(0→2, 1→0 to p_1; 2→0 to d_1)`, which is `θ` applied to SMART's
`q_1: (0→2, 1→0 to d_2; 2→0 to p_2)`. The other three write states match in the same way.
So `τ M τ = M^{-1}` as machines, and since `π` acts on every cell and commutes with shifts,
`τ s τ = s^{-1}` on moving-tape configurations.

Freeness: SMART alternates index-2 (move) and index-1 (write) states, and both `θ` and
`θ∘μ` (`μ`: `b↔d, p↔q`, the space-mirror relabelling) swap the two indices. So a fixed point
of `τ s^k` or of `τσ s^k` needs `k` odd. The conjugation `s^{-a} (τ s^k) s^a = τ s^{k+2a}`
(and likewise for `τσ`) reduces this to `k = 1`. A one-step check of all eight states shows
that neither `s c = τ c` nor `s c = τσ c` ever holds. Either the target state never matches,
or it matches only for `p_1, q_1` reading `0` or `1`, where the head cell would need
`π(a) = a'` but `π(0) = 0 ≠ 2` and `π(1) = 2 ≠ 0`. For even `k` the reflections are
conjugate to `τ` or `τσ`, which are fixed-point free because `θ` and `θμ` are.

## Consequences

- Nekrashevych's periodic groups (arXiv:1601.01033) come from fragmentations of NON-free
  minimal dihedral actions. By 2 no such action is realized by elements of any `nV`. A
  periodic fragmentation group inside `nV` must therefore fragment a dihedral action that is
  not itself in `nV` (for example a factor or lift), or use a Matte Bon-type edge-labelled
  `Z`-system.
- For SMART, the natural reversals (`τ`, `τσ`) lie outside `2V` and act freely, so they do not
  supply such an action. This bears on attempts to put infinite finitely generated periodic
  groups (Burnside-type test cases, BBMZ 5.3(6)) inside Brin–Thompson hosts.
- Open, and not settled here: whether any `nV` contains an infinite finitely generated
  torsion group.
