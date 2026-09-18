---
rg: 2
id: aperiodic-tree-almost-automorphism-fg-subgroups-are-rf-proof
kind: route
title: Aperiodic branching forbids level shifts, so almost automorphisms live in an ascending union of profinite groups
target: aperiodic-tree-almost-automorphism-fg-subgroups-are-rf
requires: []
---

Direct proof. Notation as in the target.

**Step 1: cones are isomorphic only at equal levels.** Two spherically
homogeneous rooted trees are isomorphic iff their branching sequences agree,
since level sizes are isomorphism invariants and determine the tree. So
`T_u ≅ T_w` iff `s^{|u|} m = s^{|w|} m`. If `s^j m = s^k m` with `j < k`, then
`m_{i+j} = m_{i+k}` for all `i >= 1`, and `m` is eventually periodic with
period `k - j`. Under the hypothesis, `T_u ≅ T_w` iff `|u| = |w|`.

**Step 2: `AAut(T) = ⋃_K G_K`.** Let `h` be given by partitions `⊔ C(u_i)` and
`⊔ C(w_i)` with isomorphisms `T_{u_i} -> T_{w_i}`. By Step 1, `|u_i| = |w_i|`.

- Put `K = max_i |u_i|`. The cone `C(u_i)` is the union of the level-`K` cones
  below `u_i`.
- The isomorphism `T_{u_i} -> T_{w_i}` preserves relative depth. It therefore
  maps these onto level-`K` cones below `w_i`, through isomorphisms of level-`K`
  subtrees.
- So `h` permutes `L_K` and acts on each level-`K` cone by a tree isomorphism,
  that is, `h ∈ G_K`. Conversely `G_K ⊆ AAut(T)`.

An isomorphism between level-`K` subtrees permutes their level-`(K+1)` children
and induces isomorphisms of the level-`(K+1)` subtrees, so `G_K ⊆ G_(K+1)`.

Identify every level-`K` subtree with `T_(K)` through its canonical labelling.
Then `G_K = Aut(T_(K))^{L_K} ⋊ Sym(L_K)`. It is compact and totally
disconnected, since `Aut(T_(K))` is profinite and `Sym(L_K)` is finite.

**Step 3: each `G_K` is residually finite.** For `J >= K`, every element of
`G_K` permutes `L_J`. The kernel `N_J` of `G_K -> Sym(L_J)` therefore has
finite index. An element of `⋂_{J >= K} N_J` maps every cone of every level
`J >= K` to itself, so it fixes every point of `∂T`, and it is trivial because
`G_K` acts faithfully.

**Step 4: finitely generated subgroups.**
- Let `H = <h_1, ..., h_r> <= AAut(T)`. By Step 2, `h_j ∈ G_{K_j}`. The chain is
  increasing, so `H <= G_K` with `K = max_j K_j`, and `H` is residually finite
  by Step 3.
- A divisible abelian group `D` has only divisible quotients, and a finite
  divisible group is trivial. So `D` maps trivially to every finite quotient of
  `H`, and residual finiteness forces `D = 1`.
- For `n >= 2`, `(Q,+)` embeds in `GL_n(Q)` as the matrices `[[1,q],[0,1]]`.
- A residually finite simple group has a finite quotient that is injective on a
  chosen nontrivial element. By simplicity that quotient map is injective, so
  the group is finite. An infinite finitely presented simple group is finitely
  generated, so none lies in `AAut(T)`.

**Step 5: eventually periodic branching.** If `m_{i+r} = m_i` for all
`i >= i_0`, the `m_i` take at most `i_0 + r` values, and only the finitely many
primes dividing these values occur. A sequence divisible by infinitely many
primes is unbounded, hence not eventually periodic.
