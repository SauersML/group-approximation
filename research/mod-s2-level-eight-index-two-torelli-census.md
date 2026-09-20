---
rg: 2
id: mod-s2-level-eight-index-two-torelli-census
kind: claim
title: Relations push forward to equal block sums over the ten level-two splittings, and all 1023 index-two subgroups of Gamma(4) keep d = 1/30 with a transversal relation, one orbit carrying the first 2-torsion character
distinct_from:
  mod-s2-gamma4-torelli-census-is-one-thirtieth: that computes the principal level Gamma(4) only; this computes every index-two subgroup of Gamma(4) (the first layer of Gamma(4)/Gamma(8)), finds the first torsion character of the 2-adic tower, and proves the block-sum constraint for every subgroup of Gamma(2).
  mod-s2-torelli-abelian-census-limit-is-positive: that asks for d_inf > 0 over all levels; this settles 1023 new subgroups and gives a structural constraint (BS) on all of them, but does not bound the limit.
  mod-s2-induced-torelli-characters-have-positive-relation-floors: that gives a positive transfer relation of mass 5 [M : M'] in every subgroup; this shows that positive relations below Gamma(2) have mass in 10 Z, and that mass 10 (a transversal) is reached at every index-two subgroup of Gamma(4).
  mod-s2-torelli-positive-relations-have-bounded-mass: that asks whether the minimal positive mass is bounded; (BS) here shows it lies in 10 Z below Gamma(2), and the census shows it equals 10 on this layer.
  mod-s2-maslov-line-is-optimal-for-torelli-characters: that concerns characters on the Maslov line aug(W) = 5 m Z; below Gamma(2) aug(W) lies in 10 Z by (BS1), and every subgroup computed here has aug(W) = 10 Z and d = 1/30.
artifacts:
  - experiments/mod-s2-level-eight-transversal-2026-09-17/level8_index2.py
  - experiments/mod-s2-level-eight-transversal-2026-09-17/level8_purebraid.py
  - experiments/mod-s2-level-eight-transversal-2026-09-17/level8_lattice.py
  - experiments/mod-s2-level-eight-transversal-2026-09-17/run_all.py
  - experiments/mod-s2-level-eight-transversal-2026-09-17/level8-results.json
---

**ESTABLISHED** through `mod-s2-level-eight-index-two-torelli-census-proof`. (BS) is a proof from
established nodes. The census is an exact integer computation that is validated against the
`Gamma(2)` and `Gamma(4)` nodes. Unreviewed. No novelty is claimed.

Notation follows `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`:
- `M = Mod(S_2)` and `pi : M -> Sp_4(Z)`;
- `v_c` is the class of `g_c t_s g_c^(-1)` in `H_1(pi^(-1) Gamma')`;
- `W(Gamma')` is the relation lattice on the distinct classes, and `d(Gamma')` is the lattice distance.

A **level-two splitting** is one of the 10 decompositions `F_2^4 = P + P^perp` into nondegenerate
planes. A **transversal relation** is a 0/1 vector in `W` with exactly one entry `1` over each
splitting. `A_+(Gamma')` is the least augmentation of a nonzero `w >= 0` in `W(Gamma')`.

## Statement

- **(BS) Block sums, for every finite-index `Gamma' <= Gamma(2)`.** For `w` in `W(Gamma')`, the ten
  sums of `w` over the classes lying over each splitting are equal.
  - **(BS1)** `aug(w)` is in `10 Z`.
  - **(BS2)** If `3` does not divide `aug(w)`, then `||w||_1 >= 10`. Equality holds only for `+-` a
    transversal relation.
  - **(BS3)** `A_+(Gamma')` is in `10 Z`. It equals 10 if and only if a transversal relation
    exists, and then `d(Gamma') = 1/30`.
- **(L0) The layer.** `H_1(Gamma(4); Z) = (Z/4)^6 + (Z/8)^4`. So every index-two subgroup of
  `Gamma(4)` contains `Gamma(8)`, and these subgroups are the kernels of the 1023 nonzero
  functionals on `Gamma(4)/Gamma(8) = sp_4(F_2)`. Under `Sp_4(Z)` they fall into 15 conjugacy
  classes, of sizes `15, 60, 45, 20, 180, 180, 60, 60, 90, 120, 15, 90, 72, 10, 6`.
- **(L1) Census of the layer.** Let `M'' = pi^(-1)(Gamma'')` for index-two `Gamma'' <= Gamma(4)`.
  - *14 classes (978 subgroups).* `H_1(M'') = Z^54`. There are 160 classes, 16 over each splitting,
    exactly as at `Gamma(4)`. `W` has rank 106 and is saturated.
  - *One class of 45 subgroups.* `H_1(M'') = Z^54 + Z/2`. There are 192 classes: 32 over each of
    two splittings, and 16 over each of the other eight. `W` has rank 138, and `Z^192 / W` contains
    `Z/2`. This is the first torsion character of the 2-adic tower (`Gamma(4)` has none).
  - *All 1023.*
    - `aug(W) = 10 Z`, and the block-sum identity holds on a basis.
    - A transversal relation exists, so `A_+ = 10`.
    - `d(Gamma'') = 1/30`, attained at `theta = 3/10` on every class.
    - The best certificate has `||w||_1 = aug = 10`.
  - `H_1(Gamma'')` is `(Z/4)^7 + (Z/8)^3` for the class of size 15 containing `f = (1,0,...,0)`.
    It is `Z/2 + (Z/4)^5 + (Z/8)^4` for the other 14 classes.
- **(L2) Method.** Abelian Reidemeister-Schreier runs over Artin's 10-generator presentation of
  `PMod(S_(0,6)) = PB_5/<Delta^2>`, with 1024 cosets per subgroup. The earlier approach used
  122880 cosets of `B_5/<<Delta^2>>`, and that run did not fit in 16 GB. The new pipeline
  reproduces the `Gamma(2)` and `Gamma(4)` nodes exactly.

## Reading

- By (BS3), below `Gamma(2)` the conjecture `d_inf = 1/30` of the census node is equivalent to this:
  *every level has a relation that is transversal, or else a better non-sparse certificate.* The
  quantity to track along the tower is `A_+`, which is `10` or at least `20`.
- On the whole first layer above `Gamma(4)`, the sparse transversal lift survives in every
  subgroup. That includes the one class where new classes and a 2-torsion character appear. So the
  2-adic tower shows no decay at depth `Gamma(4) -> Gamma(4) cap ker f`.
- (BS1) puts every subgroup of `Gamma(2)` off the Maslov line with `m = 1`. There `aug(W) = 5 Z` is
  impossible, and `10 Z` is forced.
- Open: `Gamma(8)` itself has 524288 cosets of `PB_5/<Delta^2>`. It is not computed.
