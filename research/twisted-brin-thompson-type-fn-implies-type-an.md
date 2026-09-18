---
rg: 2
id: twisted-brin-thompson-type-fn-implies-type-an
kind: claim
title: If a twisted Brin--Thompson group SV_G is of type F_n, then G acting on S is of type [A_n], and likewise for FP_n and [HA_n]
distinct_from:
  twisted-brin-thompson-type-fn-criterion: that is the full Belk--Zaremsky characterization, whose new part is sufficiency for 3 <= n < infinity; this is the necessity half, which Fournier-Facio--Wu--Zaremsky proved for every n.
  twisted-brin-thompson-finite-presentation-criterion: that is the n = 2 characterization; this is necessity for every n, including n = 2.
---

**ESTABLISHED (literature import)** by `twisted-bt-type-fn-necessity-citation`.

Let a group `G` act on a non-empty set `S`, faithfully or not, and let `SV_G` be the
(abstract) twisted Brin--Thompson group. For `n ∈ N`:

1. if `SV_G` is of type `F_n`, then `G ↷ S` is of type `[A_n]`;
2. if `SV_G` is of type `FP_n`, then `G ↷ S` is of type `[HA_n]`.

**Definitions** (Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, Definition 1.3 and the
paragraph before Corollary 4.18). `G ↷ S` is of type `[A_n]` if
- (i) `G` is of type `F_n`;
- (ii) for every finite `T ⊆ S`, `Stab_G(T)` is of type `F_{n−|T|}`;
- (iii) the diagonal action of `G` on `S^n` has finitely many orbits.

Type `[HA_n]` is the same with `FP` in place of `F`. Condition (ii) is empty for
`|T| ≥ n`. For faithful actions these are types `(A_n)` and `(HA_n)`.

**Mechanism.** `Z ≀_S G` is a quasi-retract of `SV_G` (their Proposition 4.17). Alonso's
theorem then transfers `F_n` or `FP_n`. The wreath product `Z ≀_S G` is of type `F_n` iff
`G ↷ S` is of type `[A_n]` (de Cornulier; Bartholdi--de Cornulier--Kochloukova), and
similarly for `FP_n` and `[HA_n]`.
