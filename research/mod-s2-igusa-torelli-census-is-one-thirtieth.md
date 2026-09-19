---
rg: 2
id: mod-s2-igusa-torelli-census-is-one-thirtieth
kind: claim
title: At the Igusa level H_1(pi^-1 Gamma(4,8)) = Z^54 + Z/2, the new order-two torsion character is nontrivial on separating twists but kills no level-four relation, so W, d = 1/30 and A_+ = 10 are exactly those of Gamma(4)
distinct_from:
  mod-s2-two-adic-torelli-tower-keeps-rank-to-level-sixteen: its item (I48) proves H_1 = Z^54 + Z/2^k with 1 <= k <= 4 and only locates A_+(Gamma(4,8)) in {10, ..., 160}; this computes k = 1 and the full integral census (classes, W, d, A_+) at Gamma(4,8).
  mod-s2-gamma4-torelli-census-is-one-thirtieth: that is the census of Gamma(4), where H_1 is torsion-free; this is the first level of the 2-adic tower where H_1 has torsion, so (R)(c) of the tower claim does not apply and the census had to be recomputed integrally.
  mod-s2-gamma4-index-two-torelli-census: that treats the 1023 index-two subgroups between Gamma(8) and Gamma(4); Gamma(4,8) has index 16 in Gamma(4) and is not among them.
  mod-s2-torelli-abelian-census-limit-is-positive: that asks for d_inf > 0 over all levels; this settles one more 2-adic level and gives no uniform bound.
artifacts:
  - experiments/mod-s2-igusa-torsion-2026-09-17/za_igusa.py
  - experiments/mod-s2-igusa-torsion-2026-09-17/igusa_exact.py
  - experiments/mod-s2-igusa-torsion-2026-09-17/w_compare.py
  - experiments/mod-s2-igusa-torsion-2026-09-17/igusa-census-results.json
---

**ESTABLISHED** through `mod-s2-igusa-torelli-census-proof` (exact modular computer calculation over
the group ring of `F_2^4`, plus the tower claim's structure theorem). Unreviewed; no novelty claimed.

Notation as in `mod-s2-two-adic-torelli-tower-keeps-rank-to-level-sixteen`. `G_I = pi^(-1)(Gamma(4,8))`,
where `Gamma(4,8)` is the Igusa group, of index 16 in `Gamma(4)`, with `Gamma(4)/Gamma(4,8) = F_2^4`.

## Statement

1. **(H) Homology.** `H_1(G_I; Z) = Z^54 (+) Z/2`. So `k = 1` in (I48).
2. **(C) Classes.** Separating twists give exactly 160 classes in `H_1(G_I)`, one over each of the 160
   level-four classes. Composing with the order-two torsion character `eps : H_1(G_I) -> Z/2` gives the
   value 1 on 76 of the 160 classes.
3. **(W) Relations.** `W(Gamma(4,8)) = W(Gamma(4))` on these 160 classes. The rank is 106, and `eps`
   pairs evenly with every level-four relation. So the torsion character is nontrivial on separating
   twists but imposes no new relation.
4. **(D) Census.** `d(Gamma(4,8)) = 1/30`, with the constant optimal character `3/10`. The best `l1`
   certificate has mass 10. `A_+(Gamma(4,8)) = 10`, via a positive 0/1 relation on 10 classes. The least
   positive relation with augmentation `2 mod 3` has mass 20.

## What this changes

- (I48) left `A_+(Gamma(4,8))` anywhere in `{10, 20, 40, 80, 160}`. It is 10: the level-four mass-10
  positive relation survives the first 2-adic level where `H_1` has torsion, with no 2-power loss.
- This is the first test of the torsion-only failure mode of the tower claim, and it does not fire.
  Torsion characters exist at `Gamma(4,8)` and are nontrivial on twists. Restricted to the twist
  classes, though, the order-two character coincides with a real character already present at level
  four, because `W(Gamma(4))` is saturated and `eps` annihilates it mod 2.
- By (TA2) monotonicity, squeezed between `d(Gamma(4,8)) = 1/30` and `d(Gamma(4)) = 1/30`, every
  `Gamma'` with `Gamma(4,8) <= Gamma' <= Gamma(4)` has `d(Gamma') = 1/30`.
- For `mod-s2-torelli-abelian-census-limit-is-positive`, the open 2-adic question moves to torsion
  characters of `M_8`, below `Gamma(4,8)`. The method here works equivariantly over `A = Gamma(4)/Gamma'`
  on the 512-coset level-four complex. Its dense stage has size about `54 |A|` integer columns, so it
  applies unchanged to other `Gamma(8) <= Gamma' <= Gamma(4)` with small `|A|`. It is not run here for
  `|A| = 2^10`.
