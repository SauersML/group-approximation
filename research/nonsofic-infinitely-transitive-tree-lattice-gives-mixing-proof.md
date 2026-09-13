---
rg: 2
id: nonsofic-infinitely-transitive-tree-lattice-gives-mixing-proof
kind: route
title: Pass to H^(infinity), take vertex-stabilizer projections for a free product lattice, apply the product-tree mixing transfer, and co-induce to F2 x F2
target: nonsofic-infinitely-transitive-tree-lattice-gives-mixing
requires:
  - burger-mozes-infinitely-transitive-tree-groups
  - tree-product-lattice-nonsofic-gives-mixing-nonsofic-action
  - sofic-action-class-closed-under-commensurability
  - sofic-kernel-amenable-quotient-permanence
---

# Proof

Item numbers `BM1`–`BM5` refer to `burger-mozes-infinitely-transitive-tree-groups`.

**Step 1: the simple factors.** By BM1, `H_i` is non-discrete with 2-transitive,
hence quasiprimitive, local actions. By BM3, `G_i` is locally `∞`-transitive and
topologically simple, and by BM1 it is non-compact and 2-transitive on `∂T`. It is
closed of finite index, hence open. `G_i ∩ Aut(T)^+` is a closed normal subgroup of
index at most 2 and is non-compact, so by simplicity it equals `G_i`. So `G_i` is a
boundary-2-transitive simple tree group in the sense of
`product-of-tree-groups-has-factorwise-howe-moore`.

**Step 2: the lattice `Γ'`.** `Γ'` is the kernel of `Γ → (H_1/G_1) × (H_2/G_2)`, a map
to a finite group, so it has finite index. `Γ` is cocompact in the closed subgroup
`H_1 × H_2`. The map `(G_1 × G_2)/Γ' → (H_1 × H_2)/Γ` is injective, continuous and
open, and its image is open and closed in a compact space. So `Γ'` is a cocompact
lattice of `G_1 × G_2`. If `Γ'` were sofic, its normal core in `Γ` would be sofic of
finite index, and `Γ` would be sofic by `sofic-kernel-amenable-quotient-permanence`.
*Density.* Put `S_i = closure(p_i(Γ'))`. `p_i(Γ)` is a finite union of cosets
`p_i(γ_j) p_i(Γ')`, so `H_i` is a finite union of cosets of `S_i`. A closed subgroup
of finite index is open and contains its normal core, which is open of finite index, so
`S_i >= H_i^(∞) = G_i` by the definition in BM2. Also `S_i <= G_i`, so `S_i = G_i`.

**Step 3: a product of free groups.** Fix a vertex `v_2` of `T_q`. Put
`Γ_(v_2) = {γ ∈ Γ : p_2(γ) v_2 = v_2}` and `Λ_1 = p_1(Γ_(v_2)) <= H_1`. If `p_1(γ)`
fixes `v_1` with `γ ∈ Γ_(v_2)`, then `γ` fixes `(v_1, v_2)`, so it lies in a finite
group. So `Λ_1` has finite vertex stabilizers and is discrete. If `γ` maps `(v_1, v_2)`
to `(v_1', v_2)`, then `γ ∈ Γ_(v_2)`. So `Λ_1` has at most as many vertex orbits on
`T_p` as `Γ` has on `T_p × T_q`, finitely many. By Bass–Serre theory `Λ_1` is the
fundamental group of a finite graph of finite groups, hence virtually free. So is
`Λ_1 ∩ G_1`, of finite index in `Λ_1`. Choose a free subgroup `Λ_1'` of finite index
in it. It acts on `T_p` with trivial stabilizers: an inversion `g` has `g^2` fixing an
edge, so `g^2 = e` and then `g = e`. The quotient is a finite `p`-regular graph with
`V >= 1` vertices, so `Λ_1'` is free of rank `1 + V(p/2 − 1) >= 2`. Likewise
`Λ_2' <= G_2` is free of rank `n >= 2`. `Λ = Λ_1' × Λ_2'` acts freely on
`T_p × T_q` with finitely many orbits, so it is a cocompact lattice of `G_1 × G_2`.

**Step 4: mixing and nonsoficity.** Apply `tree-product-lattice-nonsofic-gives-mixing-nonsofic-action`
to `L = G_1 × G_2`, the nonsofic lattice `Γ'` with dense projections, and the lattice `Λ`.
Then `Λ ↷ W` is essentially free, mixing and not sofic.

**Step 5: co-induction to `F_2 × F_2`.** `F_2` contains `F_k` with index `k − 1`, so
`G = F_2 × F_2` has a finite-index subgroup `Δ ≅ F_m × F_n`. Let
`X = CoInd_Δ^G(W) = {f : G → W | f(gδ) = δ^(-1)·f(g)}`, identified with `W^T` for a
transversal `T ∋ e` of `G/Δ`, with product measure.

* *Not sofic.* Lemma B in `sofic-action-class-commensurability-proof` makes `W` a
  `Δ`-factor of `X|_Δ`. Lemma A there shows that a factor of a restriction of a sofic
  action is sofic. So `X` is not sofic.
* *Mixing.* Let `Δ_0 <= Δ` be the normal core, of finite index in `G`. For `δ ∈ Δ_0` and
  `t ∈ T`, `(δ·f)(t) = f(δ^(-1)t) = (t^(-1)δt)·f(t)`, and `t^(-1)δt ∈ Δ_0`. So
  `X|_(Δ_0)` is a finite product of copies of `W|_(Δ_0)` twisted by the automorphisms
  `Ad(t^(-1))` of `Δ_0`. Restrictions to infinite subgroups and twists by automorphisms
  of discrete groups preserve mixing. Finite products of mixing actions are mixing:
  check on products of functions, whose span is dense. For `g_k → ∞` in `G`, write
  `g_k = δ_k s_k` with `s_k` in a finite transversal of `G/Δ_0`. Along a subsequence
  `s_k = s` is constant, and `⟨g_k F, F'⟩ = ⟨δ_k (sF), F'⟩ → ∫F ∫F'`. So `G ↷ X` is
  mixing.
* *Free.* Let `g ≠ e`. If `g` moves a coset, `g^(-1)t'Δ = tΔ` with `t ≠ t'`, write
  `g^(-1)t' = tδ`. Then `g·f = f` forces `f(t') = δ^(-1)·f(t)`, a graph in two
  coordinates. It is null because `W` is non-atomic, being essentially free for an
  infinite group. If `g` fixes every coset, then `g ∈ Δ_0` and acts on coordinate `t` by
  `t^(-1)gt ≠ e`, essentially freely. Countably many `g` give a null union.

`F_2 × F_2` is residually finite, hence sofic. ∎
