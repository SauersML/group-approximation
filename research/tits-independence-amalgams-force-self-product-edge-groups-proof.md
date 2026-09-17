---
rg: 2
id: tits-independence-amalgams-force-self-product-edge-groups-proof
kind: route
title: Disjointly supported conjugates of the two independence factors nest inside each other
target: tits-independence-amalgams-force-self-product-edge-groups
requires: []
---

The notation is that of the target. Automorphisms of `T` are identified with
their actions, because the action is faithful.

**0. Basic facts.**

- `C` fixes `v` and `w`, so it preserves `T_v` and `T_w`.
- `V` and `W` are normal in `C`, being pointwise fixators of `C`-invariant sets.
- An element of `V` acts as the identity on `T_w`, and one of `W` acts as the
  identity on `T_v`. So `V` and `W` commute, and `V ∩ W` fixes `T` and is trivial.
- Hence `C = VW` means `C = V × W`.
- **Disjoint supports.** For `g ∈ Aut(T)`, let `supp(g)` be the set of vertices
  that `g` moves. Suppose subgroups `H_i` preserve pairwise disjoint vertex sets
  `S_i` and act trivially off `S_i`. Then they commute pairwise. A product
  `h_1 ... h_k` with `h_i ∈ H_i` acts as `h_i` on `S_i`. So it is trivial only if
  every `h_i` is trivial, and `⟨H_i⟩ = ⊕ H_i`.

**1. Both factors are nontrivial.** Suppose `W = 1`, so `C = V` fixes `T_w`
pointwise.

- Pick `b ∈ B ∖ C`, and let `e' = be = (bv, w)`, with `bv ≠ v`.
- `bT_w` is the component of `T ∖ e'` that contains `bw = w`. It contains `v`,
  hence all of `T_v ∪ e`.
- `bCb^{-1} = bVb^{-1}` fixes `bT_w` pointwise, so it fixes `T_v ∪ e`.
- `bv` is a neighbour of `w` other than `v`, so it lies in `T_w`. So `C` fixes
  `bv` and `w`, i.e. `C ≤ Stab(e') = bCb^{-1}`.
- Therefore `C` fixes `T_w`, `T_v` and `e`, which is all of `T`. So `C = 1`, a
  contradiction.

The case `V = 1` is symmetric, using some `a ∈ A ∖ C`.

**2. Nesting.** Let `a ∈ A ∖ C`, so `ae = (v, aw)` with `aw ≠ w`.

- `aT_v` is the component of `T ∖ ae` containing `av = v`. It contains `e` and
  `T_w`.
- `aT_w` is the other component. It lies inside `T_v ∖ {v}`.
- `W_x = aWa^{-1}` fixes `aT_v` pointwise and can move only vertices of `aT_w`.
  So `W_x ≤ Fix(T_w) ∩ Fix(e) = V`.
- `W_x` depends only on `x = aC`, because `W` is normal in `C`.
- For distinct cosets `x ≠ x'`, the sets `aT_w` and `a'T_w` are distinct branches
  at `v`, hence disjoint. By 0 the `W_x` with `x ≠ C` generate their direct sum
  inside `V`.
- The branch `T_w` of `W_C = W` is disjoint from all of these. So `D_A` is a
  direct sum.
- Every `W_x` fixes `v` and every edge at `v`, so `D_A` lies in the kernel of `A`
  acting on `A/C`.
- For `a' ∈ A`, `a' W_x a'^{-1} = W_{a'x}`. So `D_A` is normal in `A`.

The statements for `B` follow with the roles of `v` and `w` exchanged. Finally
`V = V_C ≤ D_B` and `W = W_C ≤ D_A`, so `C = VW ≤ D_A D_B ≤ C`.

**3. Self-products.**

- *Not both indices 2.* If `m = n = 2`, every vertex of `T` has degree 2. `T` is a
  line, and an automorphism of a line fixing an edge pointwise is trivial. So
  `C = 1`, a contradiction.
- *Case `m ≥ 3`.* Pick distinct `x_1, x_2 ≠ C` in `A/C`, so `W_{x_1} × W_{x_2} ≤ V`
  by 2. Since `n ≥ 2`, pick `y ≠ C` in `B/C`, so `V_y ≤ W` by 2, and `V_y ≅ V`.
  Conjugating, `W_{x_i}` contains a conjugate of `V`. The two conjugates commute
  and generate their direct product, so `V × V ↪ V`.
- *Case `m = 2`, `n ≥ 3`.* Here `V_{y_1} × V_{y_2} ≤ W` and `W_x ≤ V` for the one
  `x ≠ C`. A conjugate of `V × V` lies in `W_x ≤ V`.
- *Same for `W`.* In either case, `V ↪ W` (via `V_y ≤ W`) and `W ↪ V` (via
  `W_x ≤ V`). So `W × W ↪ V × V ↪ V ↪ W`.
- *Infinite.* If `V` were finite, `|V|^2 ≤ |V|` would force `V = 1`, which
  contradicts 1. The same holds for `W`.
- *Powers.* By induction `V^{2^j} ↪ V` for every `j`. The copies are conjugates
  of `V` acting on pairwise disjoint vertex sets, obtained by nesting 2 inside 2,
  and they commute. For `h ≠ 1` in `V`, the corresponding conjugates of `h` in `k`
  of these copies generate a subgroup isomorphic to `⟨h⟩^k`. The same argument
  works for `h ∈ W`, using `W × W ↪ W`.

**4. Corollary.** Let `h ≠ 1` in `V`, and replace `h` by a power so that either
`h` has infinite order or `h` has prime order `p`. By 3, `C` contains `Z^k` for all
`k`, or `(Z/p)^k` for all `k`. If `C ≤ H` and `H` bounds the orders of its finite
subgroups and the ranks of its free abelian subgroups, this is impossible. So
`C = 1`, and then `Γ = A * B` with `A, B ≠ 1` maps onto `A` with nontrivial kernel,
so `Γ` is not simple.

The listed classes satisfy both bounds:

- **Finite groups.** Clear.
- **Hyperbolic groups.** Finitely many conjugacy classes of finite subgroups, and
  no `Z^2`.
- **Finite vcd.** Let `H` have a torsion-free subgroup `H_0` of finite index with
  `cd H_0 = d`. A finite subgroup meets `H_0` trivially, so its order is at most
  `[H:H_0]`. For `Z^k ≤ H`, the subgroup `Z^k ∩ H_0` has finite index in `Z^k`, so
  it is free abelian of rank `k`, and `k = cd(Z^k ∩ H_0) ≤ d`.
- **Proper cocompact CAT(0) groups.** Bridson--Haefliger II.2.8 gives finitely
  many conjugacy classes of finite subgroups. The flat torus theorem gives an
  isometric `E^k` for `Z^k`, and a proper cocompact CAT(0) space has finite
  geometric dimension (Kleiner), which bounds `k`.

The remark on free edge groups is the finite vcd case. Discrete actions on locally finite
trees with finite stabilizers fall under the finite case. ∎
