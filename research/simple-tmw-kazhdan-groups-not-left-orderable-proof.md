---
rg: 2
id: simple-tmw-kazhdan-groups-not-left-orderable-proof
kind: route
title: The finite residual meets the embedded Janzen–Wise lattice in a subgroup containing its unique index-8 cyclic-quotient kernel, which carries a positive-cone UNSAT certificate
target: simple-titz-mite-witzel-kazhdan-groups-are-not-left-orderable
requires: [exotic-c2-tilde-simple-kazhdan-lattices-are-not-left-orderable]
artifacts:
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/bmw_sat.py
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/bmw_sat.out
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_2power.g
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_2power.out
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_2power.json
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_sub_sat.py
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_sub_sat.out
---

TMW = Titz Mite, Witzel, *Non-residually finite C~_2-lattices*, arXiv:2509.05054. Scripts in
`experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/`. Reproduce:
`gap -q jw_2power.g` (about 2 minutes, writes `jw_2power.json`), then
`python3 jw_sub_sat.py jw 3 4 6` and `python3 jw_sub_sat.py prod_jw 3 4`.

## Imported facts (TMW)

- (F1) Main theorem: `Γ^q_k = π_1(Y^q_k)` is a torsion-free uniform lattice on an exotic `C~_2`
  building with property (T); `[Γ^3_k : Γ̌^3_k] = 4` for `k = 1, 2` and `8` for `k = 3, 4`;
  `Γ^2_1` is its own finite residual.
- (F2) Corollary (with Lécureux–Witzel, Theorem A): each `Γ̌^q_k` is simple.
- (F3) Proof of Theorem `main_2`, Part 1, and §7: `π_1(S_R) ↪ Γ^2_1` and `π_1(S_JW) ↪ Γ^3_k`, by
  locally convex embeddings of subdivided square complexes (Lemma `locally_convex`,
  Bridson–Haefliger II.4.14).
- (F4) Proposition `JanzenWise`:
  `Γ_JW = ⟨a,b,x,y | axay, ax^{-1}by^{-1}, ay^{-1}b^{-1}x^{-1}, bxb^{-1}y^{-1}⟩`, and
  `π_1(S_JW)` is its type-preserving subgroup `K = ker(Γ_JW → Z/2 × Z/2)`, with `a, b ↦ σ_A` and
  `x, y ↦ σ_X` (TMW §2, BMW-complexes).

Only (F1) index values, (F3) and (F4) are used in the proof; (F2) is context.

## Case q = 2

`Γ̌^2_1 = Γ^2_1 ⊇ π_1(S_R)` by (F1) and (F3). `π_1(S_R)` is not left-orderable: complete
rewriting system and positive-cone UNSAT on `B_6`, `bmw_sat.out` (full argument in
`exotic-c2-tilde-kazhdan-lattices-not-left-orderable-proof`). A group with a
non-left-orderable subgroup is not left-orderable.

## Case q = 3

**Step 1 (reduction to `K`).** Fix `k` and the embedding `ι: K ↪ Γ = Γ^3_k` from (F3). Put
`M = ι^{-1}(Γ̌)`. Then `M ⊴ K` and `K/M ↪ Γ/Γ̌`, a group of order 4 or 8 by (F1). So `K/M` is a
2-group of order `2^j`, `j ≤ 3`.

**Step 2 (2-quotients of `K` are cyclic).** `jw_2power.g` builds `Γ_JW` from (F4), `K` as the
kernel of the map to `Z/2 × Z/2`, checks `[Γ_JW : K] = 4`, and computes
`AbelianInvariants(K) = [0, 3]`, i.e. `K^ab ≅ Z × Z/3`. Hence `Hom(K, F_2) = F_2`. Let `P` be a
finite 2-group quotient of `K`. Its Frattini quotient `P/Φ(P)` is an elementary abelian quotient
of `K`, so has rank at most 1, and by the Burnside basis theorem `P` is cyclic. A surjection
`K → Z/2^j` kills the torsion `Z/3` of `K^ab` and restricts to a surjection on the `Z` factor,
so its kernel is `N_j := ker(K → K^ab → Z → Z/2^j)`, independent of the choice. Therefore
`M = N_j` for some `j ≤ 3`, and `M ⊇ N_3`.

Cross-check in GAP: for `j = 1, 2, 3`, among the subgroups of `K` of index `2^j` exactly one is
normal with 2-group quotient, and that quotient is cyclic (`jw_2power.out`).

**Step 3 (membership).** `jw_2power.g` exports `FactorCosetAction(Γ_JW, N_j)` on the
`4 · 2^j` right cosets and checks that the stabiliser of point 1 is `N_j`. `jw_sub_sat.py` checks
that all four relators act trivially, and decides `w ∈ N_j` by `1^w = 1`, applying the letters of
the normal form in order.

**Step 4 (certificate).** Normal forms and multiplication come from `bmw_sat.make('jw')`, whose
rewriting system is complete (40 critical pairs, see the q = 2 reference proof). The clauses are
those of the positive-cone lemma on `N_3 ∩ B_L`: `p_g ⊕ p_{g^{-1}}`, and
`¬p_g ∨ ¬p_h ∨ p_{gh}` (or `¬p_g ∨ ¬p_h` if `gh = 1`) whenever `g, h, gh ∈ B_L`. The script
asserts that membership is closed under inverses and products on the ball, which is a consistency
check on the permutation data. A left order on `N_3` would satisfy the clauses. Results
(`jw_sub_sat.out`; CaDiCaL 1.5.3 and Glucose 4 agree):

| subgroup | L | `|B_L|` | `|N ∩ B_L| − 1` | clauses | result |
|---|---|---|---|---|---|
| `N_1` (index 2 in K) | 4 | 865 | 232 | 4808 | UNSAT |
| `N_2` (index 4) | 4 | 865 | 200 | 4456 | UNSAT |
| `N_3` (index 8) | 4 | 865 | 200 | 4456 | **UNSAT** |
| `N_3` | 6 | 11665 | 2152 | 185552 | UNSAT |
| calibration `prod_jw`, index 8 | 4 | 865 | 200 | 4456 | SAT |
| calibration `prod_jw`, index 2 | 4 | 865 | 384 | 15000 | SAT |

So `N_3` is not left-orderable, hence neither is `M ⊇ N_3`, hence neither is `Γ̌^3_k`. ∎

**Remark on the counts.** Elements of `K ∩ B_5` fall into only 5 of the 8 cosets of `N_3`
(counts 201, 76, 76, 16, 16): the homomorphism `K → Z` takes values in `[-2, 2]` on short words.
That is why `N_2 ∩ B_4 = N_3 ∩ B_4`.

**Calibration.** `prod_jw` keeps the letters but lets every square commute, giving `F_2 × F_2`.
Its subgroup "even/even length and horizontal exponent sum `≡ 0 mod 2^j`" is a subgroup of
`F_2 × F_2`, hence left-orderable, and the same encoder answers SAT at the same ball sizes.
