---
rg: 2
id: mod-s2-gamma4-index-two-torelli-census
kind: claim
title: Every index-two subgroup Gamma(8) < G < Gamma(4) has d(G) = 1/30 with a mass-10 certificate, and b_1 does not grow from level four to level eight, so below Gamma(4) down to Gamma(8) every real Torelli character is pulled back from level four and only torsion characters can push d below 1/30
distinct_from:
  mod-s2-gamma4-torelli-census-is-one-thirtieth: that evaluates Gamma(4) itself (61440 cosets of H); this evaluates all 1023 index-two subgroups between Gamma(8) and Gamma(4) (15 conjugacy types, 122880 cosets each) and computes b_1(M_8) and b_1 of every intermediate subgroup, which that node does not reach.
  mod-s2-torelli-abelian-census-limit-is-positive: that asks for d_inf > 0 over all levels; this settles the first 2-adic step below Gamma(4) and reduces the level-eight question to torsion characters, without bounding the limit.
  mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit: that proves the reduction (TA1)-(TA3) and the level census up to Gamma(2) and Gamma(3); this is a computation below Gamma(4) using it.
artifacts:
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/index2.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/drive.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/combine.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/blocks.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/blocks-output.txt
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/test_lean.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/crosscheck.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/index2-results.json
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/index2-lean-crosscheck.json
---

**ESTABLISHED** through `mod-s2-gamma4-index-two-torelli-census-proof` (exact integer computation
plus transfer). Unreviewed; no novelty claimed.

Notation as in `mod-s2-gamma4-torelli-census-is-one-thirtieth`:
- `M = Mod(S_2)`, `pi : M -> Sp_4(Z)`, and `M' = pi^(-1)(Gamma')`;
- `v_c` are the separating-twist classes in `H_1(M')`, `W(Gamma')` is their relation lattice, and
  `d(Gamma')` is the `l_inf` distance from `(1/3) 1` to `Ann(W)`.

`Gamma(4)/Gamma(8) = {I + 4Y} = sp_4(F_2) = F_2^10`, and `Sp_4(Z)` acts on it through `Sp_4(F_2)`.
For a nonzero functional `chi` on it, put `G_chi = ker chi` and `M_chi = pi^(-1)(G_chi)`.

## Statement

- **(I1) Orbits.** The 1023 index-two subgroups `Gamma(8) < G < Gamma(4)` fall into 15 conjugacy
  classes under `Sp_4(Z)`. Their sizes are
  `60, 15, 45, 20, 180, 180, 60, 60, 120, 90, 10, 6, 90, 72, 15`.
- **(I2) Distance.** `d(G) = 1/30` for all 1023 of them. In each class some `w` in `W(G)` has
  `||w||_1 = aug(w) = 10` and support 10, and `gcd aug(W(G)) = 10`.
- **(I3) Homology.** `b_1(M_chi) = 54 = b_1(M_4)` for every `chi`. `H_1(M_chi; Z)` is `Z^54` for 14
  of the classes, and `Z^54 + Z/2` for class 2 (45 subgroups).
- **(I4) Classes.**
  - In 14 classes there are 160 distinct classes `v_c`, each hit by 768 of the 122880 cosets. So
    `W(G_chi)` is `W(Gamma(4))` on the same 160 classes (rank 106), and the two `M_4`-conjugates of
    each twist are homologous in `M_chi`.
  - In class 2 there are 192 classes (rank of `W` is 138). The 32 extra classes lie over the two
    level-two splittings whose block subalgebra `sp(P) + sp(P^perp)` is killed by `chi`.
  - Class 7 also kills one block (`blocks-output.txt`). Its twist orbits over that splitting
    split under conjugation, but the two halves stay homologous, so it still has 160 classes.
- **(I5) Level eight, rationally.** `b_1(M_8) = 54`. More generally, `b_1(M') = 54` for every
  `Gamma(8) <= Gamma' <= Gamma(4)`. `Gamma(4)/Gamma(8)` acts trivially on `H_1(M_8; Q) = Q^54`, and
  restriction `H^1(M_4; R) -> H^1(M'; R)` is an isomorphism.
- **(I6) Only torsion can lower d.** Let `Gamma(8) <= Gamma' <= Gamma(4)`.
  - Every real character of `M'` is the restriction of one of `M_4`. So the identity component of
    `Ann(W(Gamma'))` is the pullback of `Ann(W(Gamma(4)))` along the surjection of class sets, and on
    it the distance is exactly `1/30`.
  - Hence `d(Gamma') < 1/30`, and in particular `d(Gamma(8)) < 1/30`, can only be attained on a
    component translated by a torsion character of `H_1(M')`.

## What this changes

- **The first 2-adic step below `Gamma(4)` does not decay.**
  - Conjecture C (`d = 1/(15 m)`, with `m = 2` below `Gamma(2)`) predicts `1/30` on all 1023
    subgroups, and that is what they give.
  - The level-four transversal certificate survives into every index-two subgroup, still with
    mass 10. It does not spread to mass 20, which is all that transfer alone gives (the bound
    `d >= 1/60`).
- **Real characters are frozen from level four to level eight.**
  - `H_1(M_8; Q)` was out of reach: the direct Reidemeister-Schreier needs `61440 * 1024` cosets.
  - The character decomposition over the 15 orbit representatives computes it with 15 runs of
    122880 cosets each, and gives `b_1(M_8) = b_1(M_4) = 54`.
  - So no real Torelli-abelian character of `M_8` sees level eight at all. Any decay of the 2-adic
    tower at `Gamma(8)` would be a purely torsion effect in `H_1(M_8; Z)`.
  - Within the index-two layer the torsion is tiny: a single `Z/2`, in class 2, and it does not
    lower `d`.
- **A precise next target** on `mod-s2-torelli-abelian-census-limit-is-positive`.
  - Along `Gamma(2^k)`, (TAP) at level `2^k` reduces to torsion characters for as long as
    `b_1(M_(2^k))` stays 54.
  - Two questions follow. Does `b_1(M_(2^k)) = 54` for all `k >= 2`? And do the torsion characters
    of `H_1(M_8)` ever move the separating-twist values towards `1/3`?
  - The first question is again a finite character computation: `Gamma(8)/Gamma(16)` is again
    `sp_4(F_2)`, so it needs 15 orbit runs, each over twice the cosets of `M_8`.
