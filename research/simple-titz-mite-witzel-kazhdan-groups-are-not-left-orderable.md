---
rg: 2
id: simple-titz-mite-witzel-kazhdan-groups-are-not-left-orderable
kind: claim
title: None of the five simple CAT(0) Kazhdan groups of Titz Mite–Witzel is left-orderable
distinct_from:
  higher-rank-p-adic-lattices-are-not-left-orderable: that imports Deroin–Hurtado for lattices in algebraic p-adic groups; these five groups are simple lattices on exotic C~_2 buildings and not linear over any field, and the proof is a finite certificate on an embedded tree-product lattice
  irreducible-tree-product-lattices-are-not-left-orderable: that is the open general statement for products of trees; this certifies one explicit irreducible instance and its three 2-power-index normal subgroups, and uses them only as subgroups
artifacts:
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/bmw_sat.py
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/bmw_sat.out
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_2power.g
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_2power.out
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_2power.json
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_sub_sat.py
  - experiments/c2-tilde-simple-lattice-left-orders-2026-09-17/jw_sub_sat.out
---

**ESTABLISHED (computation with a complete rewriting system and GAP, plus the Titz Mite–Witzel
embeddings).**

**Statement.** Let `Γ̌^2_1, Γ̌^3_1, Γ̌^3_2, Γ̌^3_3, Γ̌^3_4` be the finite residuals of the
lattices `Γ^q_k = π_1(Y^q_k)` on exotic `C~_2` buildings of Titz Mite–Witzel (arXiv:2509.05054,
Main theorem). By their Corollary they are simple CAT(0) groups with property (T), among the
first known. None of them is left-orderable, so none embeds in `Homeo_+(R)`.

**Why this matters for Navas's Question 3.** An infinite *simple* Kazhdan group has no
nontrivial finite or abelian quotient and no linear representation to exploit, so the classical
obstructions (Witte Morris's nilpotent configurations, Deroin–Hurtado's boundary theory, finite
quotient arguments) do not reach it. This claim removes every explicit simple CAT(0) Kazhdan
group of TMW as a witness for `infinite-left-orderable-kazhdan-group`.

**Proof shape** (full proof in `simple-tmw-kazhdan-groups-not-left-orderable-proof`).

1. `q = 2`. TMW: `Γ^2_1` is its own finite residual, so `Γ̌^2_1 = Γ^2_1`, which contains
   `π_1(S_R)`. That subgroup is not left-orderable (node
   `exotic-c2-tilde-simple-kazhdan-lattices-are-not-left-orderable`, certificate `bmw_sat.py`).
2. `q = 3`. `K = π_1(S_JW)` embeds in `Γ^3_k` (TMW §7). `Γ^3_k / Γ̌^3_k` has order 4 or 8, so
   `M = K ∩ Γ̌^3_k` is normal in `K` with `K/M` a 2-group of order at most 8.
3. GAP: `K^ab = Z × Z/3`, so `H^1(K; F_2) = F_2`. By the Burnside basis theorem every finite
   2-group quotient of `K` is cyclic, hence factors through `K^ab → Z → Z/2^j`. So
   `M ⊇ N_3 = ker(K → Z/8)`, the unique normal subgroup of `K` with quotient of order 8.
4. Positive-cone SAT on `N_3 ∩ B_4` (200 elements, 4456 clauses) is UNSAT, and also on `B_6`
   (2152 elements, 185 552 clauses); CaDiCaL and Glucose agree. So `N_3`, hence `M`, hence
   `Γ̌^3_k`, is not left-orderable, for `k = 1, 2, 3, 4`.

**Calibration.** The commuting-square group `F_2 × F_2` on the same letters, with the
subgroup "even/even and horizontal exponent sum `≡ 0 mod 8`", gives SAT on `B_4` with the same
200 elements and 4456 clauses. The GAP script confirms for `j = 1, 2, 3` that exactly one normal
subgroup of `K` of index `2^j` has a 2-group quotient, that it is cyclic, and that the exported
coset action has stabiliser `N_j`.

**Scope.** Only these five groups and groups containing them. Nothing here covers other
lattices on exotic `C~_2` buildings.
