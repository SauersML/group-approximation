---
rg: 2
id: mod-s2-three-adic-first-layer-torelli-census
kind: claim
title: Every index-three subgroup Gamma(9) < G < Gamma(3) keeps the level-three Torelli relations - b_1 does not grow from M_3 to M_9, W(G) = W(Gamma(3)) exactly on the 13 conjugacy classes with no off-diagonal splitting, and up to prime-to-3 torsion on the other 3, so d(G) = 1/15 with the mass-5 certificate
distinct_from:
  mod-s2-gamma4-index-two-torelli-census: that is the first 2-adic layer (index two below Gamma(4), d = 1/30); this is the first 3-adic layer (index three below Gamma(3), d = 1/15), where the transfer obstruction of the census-limit claim is sharpest because the index is 3.
  mod-s2-torelli-abelian-census-limit-is-positive: that asks for d_inf > 0 over all levels; this settles the first 3-adic step below Gamma(3) and computes b_1(M_9), without bounding the limit.
  mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit: that proves the reduction (TA1)-(TA3) and the census at Gamma(2) and Gamma(3); this is a computation below Gamma(3) that uses it.
artifacts:
  - experiments/mod-s2-three-adic-census-2026-09-17/orbits.py
  - experiments/mod-s2-three-adic-census-2026-09-17/orbits.json
  - experiments/mod-s2-three-adic-census-2026-09-17/threeadic.py
  - experiments/mod-s2-three-adic-census-2026-09-17/equivariant.py
  - experiments/mod-s2-three-adic-census-2026-09-17/local.py
  - experiments/mod-s2-three-adic-census-2026-09-17/lelim.c
  - experiments/mod-s2-three-adic-census-2026-09-17/compare.py
  - experiments/mod-s2-three-adic-census-2026-09-17/summarize.py
  - experiments/mod-s2-three-adic-census-2026-09-17/test_lelim.py
  - experiments/mod-s2-three-adic-census-2026-09-17/first-layer-results.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-0.json
  - experiments/mod-s2-three-adic-census-2026-09-17/local-orbit-flat0.json
---

**ESTABLISHED** through `mod-s2-three-adic-first-layer-torelli-census-proof` (Hochschild-Serre and
property (T), then an exact 3-local computation over `(Z/81)[Z/3]` plus transfer). Unreviewed; no
novelty claimed.

Notation as in `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`:
- `M = Mod(S_2)`, `pi : M -> Sp_4(Z)`, and `M' = pi^(-1)(Gamma')`;
- `v_c` are the separating-twist classes in `H_1(M')`, `W(Gamma')` is their relation lattice, and
  `d(Gamma')` is the `l_inf` distance from `(1/3) 1` to `Ann(W)`.

`Gamma(3)/Gamma(9) = sp_4(F_3) = F_3^10`. Its index-three subgroups are `G_Y = ker (I + 3X -> tr(YX))`
for `Y != 0` in `sp_4(F_3)`, up to sign: 29524 subgroups in 16 conjugacy classes. `n_Y` is the number
of level-3 splittings `P + P^perp` with `Y` off-diagonal (`Y P <= P^perp`, `Y P^perp <= P`). `n_Y` is
`3, 2, 1` on three classes and `0` on the other 13.

## Statement

1. **No new real characters.** `b_1(M_Y) = 24` for every `Y != 0`, and `b_1(M_9) = 24 = b_1(M_3)`.
   Every real Torelli character of `M_9` is restricted from `M_3`.
2. **`n_Y = 0` (13 classes, exact).** The classes of `M_Y` are the 45 level-3 splittings, and
   `W(G_Y) = W(Gamma(3))` (rank 21, `gcd aug = 5`). Hence `d(G_Y) = 1/15`, attained by the frame-3
   certificate of `l1`-mass 5.
3. **`n_Y = 1, 2, 3` (3 classes, exact at 3).** There are `45 + 2 n_Y` classes. The three classes above
   each off-diagonal splitting differ by torsion of order prime to 3. The 3-saturation
   `W_(3)(G_Y) = {w : k w in W(G_Y), 3 not | k}` is the pull-back of `W(Gamma(3))` along the merge
   map to the 45 splittings. Hence `3 not | gcd aug W(G_Y)`, `d(G_Y) <= d(W_(3)) = 1/15`, and some
   prime-to-3 multiple of a mass-5 lift of the frame-3 certificate lies in `W(G_Y)`.

## What this changes

- *The transfer obstruction does not bite at the first 3-adic step.* The transfer only gives
  `3 W(Gamma(3)) <= W(G_Y)`, and `3` kills every transferred certificate. The computation shows that
  the level-3 relations themselves survive: `W(Gamma(3))/W(G_Y) = 0`, not `F_3^21`.
- *Where decay can come from below Gamma(3).* By part 1, down to `Gamma(9)` it can only come from
  torsion characters. For `n_Y > 0` it can only come from prime-to-3 torsion of `H_1(M_3; Z[omega]_chi)`.
  The 3-parts are computed and change nothing.
- *What it does not give.* `Gamma(9)` is the intersection of all `G_Y`, and only its `b_1` is computed
  here. Its classes and its `W` are not determined by the `W(G_Y)`. The next steps are the second-layer subgroups `G_Y cap G_Y'`, which the same chain complex
  over `(Z/3^m)[Z/3 x Z/3]` reaches (Lam stays local), and then `Gamma(9)`.
- *Open piece of part 3.* Exactness away from 3 for `n_Y > 0`, i.e. whether `H_1(M_3; Z[omega]_chi)` is
  zero or has prime-to-3 torsion. Z-coefficient elimination (`equivariant.py`) exhausted memory on these
  covers.
