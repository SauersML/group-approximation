---
rg: 2
id: mod-s2-two-adic-torelli-tower-keeps-rank-to-level-sixteen
kind: claim
title: Between levels four and sixteen every Torelli preimage has first Betti number 54, and it kills a positive separating-twist relation of mass prime to 3, of mass at most 10 * 2^11 at level eight
distinct_from:
  mod-s2-gamma4-torelli-census-is-one-thirtieth: that computes H_1(M_4) = Z^54 and d(Gamma(4)) = 1/30 at the single level four; this computes b_1 of every preimage between levels four and sixteen (1024- and 4^10-sheeted covers of M_4) by Shapiro's lemma, and transports a positive relation down the tower.
  mod-s2-torelli-positive-relations-have-bounded-mass: that asks for sup A_+ < infinity over all finite-index Gamma'; this proves A_+ < infinity on the 2-adic interval Gamma(16) <= Gamma' <= Gamma(4), with the explicit bound 20480 at Gamma(8), and gives no uniform bound.
  mod-s2-induced-torelli-characters-have-positive-relation-floors: that defines A_+ and proves the floor D >= 1/(3 A_+); this supplies A_+(Gamma(4)) = 10 as a positive relation and finite A_+ below it.
artifacts:
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level8_betti.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level8-betti-results.json
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level16_betti.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level16-betti-results.json
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level16_f9.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/level16-f9-results.json
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/characters.py
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/random1-results.json
  - experiments/mod-s2-palindrome-transversal-relations-2026-09-17/igusa48-results.json
---

**ESTABLISHED** through `mod-s2-two-adic-torelli-tower-rank-proof` (exact and modular computer
calculation plus a transfer lemma). Unreviewed; no novelty claimed.

Notation as in `mod-s2-induced-torelli-characters-have-positive-relation-floors` and
`mod-s2-gamma4-torelli-census-is-one-thirtieth`. Put `M_N = pi^(-1)(Gamma(N))`, and for
`Gamma' <= Sp_4(Z)` of finite index put `Lambda(Gamma') = pi^(-1)(Gamma')`.

## Statement

1. **(R) Rank-stable transport.** Let `Gamma'' <= Gamma'` have finite index, and let
   `i : H_1(Lambda(Gamma'')) -> H_1(Lambda(Gamma'))` be induced by inclusion. Suppose
   `b_1(Lambda(Gamma'')) = b_1(Lambda(Gamma'))`. Then:
   - (a) `ker i` is finite. If its exponent `e` is prime to 3, then `A_+(Gamma'') <= e A_+(Gamma')`.
   - (b) Every real character of `Lambda(Gamma'')` is pulled back from `Lambda(Gamma')`. So the
     real-character part of the census does not change from `Gamma'` to `Gamma''`.
   - (c) If moreover `H_1(Lambda(Gamma''))` is torsion-free, then `i` is injective. The classes
     `v_c` are then in bijection, so `W`, `d` and `A_+` are the same at the two levels.
2. **(A4) Level four.** `A_+(Gamma(4)) = 10`. The mass-10 relation is positive: it is a product of
   ten separating twists, one over each of the ten level-two splittings, each with exponent 1. The
   least positive relation with augmentation `2 mod 3` has mass 20.
3. **(B8) Level eight.** `b_1(M_8) = 54`. For each nontrivial character `chi` of
   `Gamma(4)/Gamma(8) = F_2^10`, `H_1(M_4; Z_chi)` is a finite 2-group of exponent at most 4. The
   exponent is 4 for one orbit of size 45 and 2 for the others. `H_1(M_8)` has no odd torsion.
   `ker(H_1(M_8) -> H_1(M_4))` is a 2-group of exponent dividing `2^11`. The reason: an element
   of this kernel is trivial mod 2, so its `chi`-components lie in `2 H_1(M_4; Z_chi)`, which is at
   most `Z/2`; and the Shapiro defect is killed by `|A| = 2^10`. Hence
   `A_+(Gamma(8)) <= 10 * 2^11 = 20480`. For comparison, the transfer relation has
   `3 | chi(b_tr)` and gives nothing.
4. **(B16) Up to level sixteen.** `A = Gamma(4)/Gamma(16) = Sym_4(Z/4)` is abelian of order `4^10`.
   For each of its `4^10 - 1` nontrivial characters `f`, `H_1(M_4; Z_(3)[i]_f) = 0`. Hence, for
   every `Gamma'` with `Gamma(16) <= Gamma' <= Gamma(4)`:
   - `b_1(Lambda(Gamma')) = 54`;
   - `ker(H_1(Lambda(Gamma')) -> H_1(M_4))` is finite of order prime to 3;
   - by (R), `A_+(Gamma') < infinity`, and every real character of `Lambda(Gamma')` comes from level four.
5. **(Codim-one check.)** For the index-2 preimage attached to one random hyperplane of
   `sp_4(F_2)` (seed 1 in `characters.py`), `H_1 = Z^54` is torsion-free. By (R)(c) its census is that of level four: 160 classes,
   rank of `W` 106, gcd 10, `d = 1/30`, positive minima 10 and 20.
6. **(I48) First torsion: Igusa level.** Let `Gamma(4,8)` be the Igusa group, cut out in
   `Gamma(4)/Gamma(8)` by `J X` alternating (codimension 4). Then
   `H_1(pi^(-1) Gamma(4,8)) = Z^54 (+) Z/2^k` with `1 <= k <= 4`. The evidence:
   - `dim H_1(-; F_2) = 55`;
   - all 15 nontrivial character components have `b_1 = 0` and only torsion `(Z/2)^53`;
   - so there is no odd torsion, and the torsion is cyclic;
   - the argument of (B8), with `|A| = 16`, bounds `k`.

   So (R)(c) fails here. The census at `Gamma(4,8)` has exactly one new cyclic torsion character
   group, of order `2^k`. Every positive relation there has augmentation divisible by 10, so
   `A_+(Gamma(4,8))` lies in `{10, 20, 40, 80, 160}`.

## What this changes

Beyond level four, `A_+` was known to be finite only through the transfer relation. That relation
dies as soon as 3 divides the index, which already happens at `Gamma(4)`. Along the 2-adic
interval from `Gamma(4)` to `Gamma(16)`, (B8) and (B16) show:
- no new rational homology appears;
- no new real characters appear;
- the level-four positive relation survives (up to a 2-power multiple).

The only things that can lower `D` there are torsion characters of 2-power order. By (I48) such
characters do occur, already at the Igusa level `Gamma(4,8)`, so the census is not frozen
integrally. So on this
interval the target `mod-s2-torelli-positive-relations-have-bounded-mass` reduces to one question:
does the exponent of `ker i` stay bounded? Or, in the finer form, does the level-four mass-10
relation itself die? The divisibility failure mode (3-torsion in `ker i`) is excluded here.
Divisibility can re-enter only through steps of odd index, for example `Gamma(4) cap Gamma(3)`, which
this claim does not touch.
