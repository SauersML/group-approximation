---
rg: 2
id: finite-cloning-groups-realize-every-lamplighter-over-thompson-f
kind: claim
title: "For every subgroup H of F, some properly graded pure cloning system on finite groups has T(G_*) containing a lamp t with C_F(t) = H"
artifacts:
  - experiments/zaremsky-2-16-lehnert-conjecture-2026-09-17/coset_tree_cloning_check.py
  - experiments/zaremsky-2-16-lehnert-conjecture-2026-09-17/coset_tree_cloning_check.out
---

**Claim.** Let `H ≤ F` be any subgroup of Thompson's group `F` (not necessarily finitely
generated), and let `A ≠ 0` be a finite abelian group. There is a properly graded pure
binary cloning system `(G_n, ι_{m,n}, ρ_n ≡ 1, κ^n_k)`, in the sense of Witzel–Zaremsky,
with every `G_n` finite, such that:

1. `T(G_*) ≅ A ≀_{D_∞} F = A^{(D_∞)} ⋊ F`, where the `F`-set `D_∞` has exactly two
   orbits, one of them `F/H`; so `T(G_*)` is finitely generated;
2. the element `t = [•, a, •]` (`a ≠ 0`, one-leaf trees) satisfies
   `[t, f] = 1 ⇔ f ∈ H` for `f ∈ F`;
3. if `A = ⟨a⟩` is cyclic, `⟨x_0, x_1, t⟩ = A ≀_{F/H} F`.

**Construction** (*coset-tree cloning system*):
- `D_n = ⊔_{j ≤ n} Trees_j/~_H`, where `W ~_H W'` iff the tree-pair element `[W,W']` lies
  in `H`;
- `G_n = A^{D_n}`;
- `ι` is extension by zero;
- `κ^n_k` is pushforward along the point-cloning map
  `[W]_j ↦ [W c_k]_{j+1}` (`k ≤ j`), `[W]_j ↦ [W]_j` (`k > j`).

Complete proof: route `finite-cloning-lamplighter-realization-proof`.

**Why it matters.** Every earlier finite-group cloning system in this graph (`S_n`, `Z/n`,
twisted direct powers `G^n`) carries group data along a fixed tree geometry. This one
instead encodes an arbitrary *subgroup of F* in the index sets `D_n`. The map
`H ↦ T(G_*)` is injective on marked data, which gives uncountably many finite-group
cloning systems and lets undecidability enter the Thompson-like group. The consequences
for Zaremsky Problem 2.16 are the routes `finite-cloning-group-with-undecidable-lamp-stabilizer`
(Q1 no) and `finite-cloning-undecidable-lamp-stabilizer-not-in-v` (Q2 no).
