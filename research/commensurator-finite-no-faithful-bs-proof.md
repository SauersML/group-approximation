---
rg: 2
id: commensurator-finite-no-faithful-bs-proof
kind: route
title: Map the graph of groups to the abstract commensurator, pull back a finite-index normal subgroup, and get a compatible normal subgroup that fixes the tree
target: commensurator-rigid-groups-lack-faithful-bs-members
requires: [arithmetic-lie-lattices-have-faithful-bs-members]
---

Let `H` be the fundamental group of a finite graph of groups over `Y`. It has vertex
groups `V_x` and edge groups `E_e`, with finite-index monomorphisms
`α_e : E_e → V_(o(e))` and `ω_e : E_e → V_(t(e))`. Fix a maximal tree `Y_0 ⊆ Y`
and a base vertex `x_0`. For an edge `e`, the relation in `H` is
`t_e α_e(a) t_e^{-1} = ω_e(a)`, with `t_e = 1` for `e ∈ Y_0`.

**Step 1 (no virtual center).** Let `V` be torsion-free and commensurable with `G`,
and let `U ≤ V` have finite index, with `U` isomorphic to a finite-index subgroup
`U'` of `G`.
- An element of `U` centralizes a finite-index subgroup of `V` if and only if it
  centralizes one of `U`. So `VZ(V) ∩ U = VZ(U) ≅ VZ(U') ⊆ VZ(G) = 1`.
- So `VZ(V)` meets `U` trivially and is finite. Being torsion-free, it is trivial.
- Hence `κ_V : V → Comm(V)`, `v ↦ [conj_v]`, is injective. Its kernel is `VZ(V)`.

**Step 2 (functoriality; standard).** A finite-index inclusion `U ≤ V`, or more
generally an isomorphism `φ` between finite-index subgroups, induces an
isomorphism of abstract commensurators. It is compatible with `κ`. If `φ` is a
commensuration of `V` itself, the induced automorphism of `Comm(V)` is conjugation
by `[φ]`.

**Step 3 (a homomorphism ρ : H → C).** Put `C = Comm(V_(x_0))`.
- **Identifications.** Transporting along the path in `Y_0` from `x_0` to `x`,
  through the isomorphisms `Comm(V_(o(e))) ≅ Comm(E_e) ≅ Comm(V_(t(e)))` induced by
  `α_e` and `ω_e`, gives isomorphisms `ι_x : Comm(V_x) → C`.
- **On vertex groups.** Put `ρ(v) = ι_x(κ_(V_x)(v))` for `v ∈ V_x`.
- **On stable letters.** For `e ∉ Y_0`, transport along `Y_0` to `o(e)`, apply the
  edge commensuration `ω_e α_e^{-1}`, and transport back. This is a commensuration
  of `V_(x_0)`; let `ρ(t_e) = c_e` be its class.
- **Relations.** By Step 2,
  `ι_(t(e)) ∘ (ω_e α_e^{-1})_* = Ad(c_e) ∘ ι_(o(e))` on `Comm(V_(o(e)))`. So
  `ρ(ω_e(a)) = c_e ρ(α_e(a)) c_e^{-1}`, with `c_e = 1` on `Y_0`, and `ρ` respects the
  relations of `H`.
- **Injectivity.** `ρ` is injective on every `V_x`, by Step 1.

**Step 4 (a normal subgroup of finite index).** `V_(x_0)` is commensurable with `G`,
so `C ≅ Comm(G)`, and the image of `G` has finite index. The image of a finite-index
subgroup of `V_x` matches, under these identifications, the image of a finite-index
subgroup of `G`. So each `ρ(V_x)`, `ρ(α_e E_e)` and `ρ(ω_e E_e)` has finite index
in `C`.
- Let `P` be the normal core in `C` of the intersection of these finitely many
  subgroups. `P` is normal and of finite index in `C`.
- It is infinite, since `ρ(V_(x_0)) ≅ V_(x_0)` is infinite: a torsion-free
  nontrivial group.
- Put `P_x = (ρ|_(V_x))^{-1}(P)`. It is a nontrivial normal subgroup of `V_x`.

**Step 5 (compatibility).**
- **Inside the edge groups.** `P ⊆ ρ(α_e E_e)` and `ρ|_(V_(o(e)))` is injective, so
  `P_(o(e)) ⊆ α_e(E_e)`. Likewise `P_(t(e)) ⊆ ω_e(E_e)`.
- **Matching under edge maps.** For `a ∈ E_e`, `ρ(ω_e a) = c_e ρ(α_e a) c_e^{-1}`,
  and `P` is normal. So `α_e(a) ∈ P_(o(e))` exactly when `ω_e(a) ∈ P_(t(e))`.
- With `Q_e = α_e^{-1}(P_(o(e))) = ω_e^{-1}(P_(t(e)))`, this gives
  `α_e(Q_e) = P_(o(e))` and `ω_e(Q_e) = P_(t(e))`.

**Step 6 (a nontrivial normal subgroup fixing the tree).**
- **One subgroup.** For `e ∈ Y_0`, `α_e(a) = ω_e(a)` in `H`, so
  `P_(o(e)) = P_(t(e))` as subgroups of `H`. Since `Y_0` is a spanning tree, all
  `P_x` equal one subgroup `N = P_(x_0)`, which every `V_x` normalizes.
- **Normality.** For `e ∉ Y_0`,
  `t_e N t_e^{-1} = t_e α_e(Q_e) t_e^{-1} = ω_e(Q_e) = N`. So `N` is normal in `H`.
- **Fixing the tree.** `N ⊆ V_x` for every `x`, and `N` is normal, so it fixes
  every vertex of the Bass--Serre tree. It is nontrivial, so `H` is not faithful.

**Instances.**
- **Mostow--Prasad.** For `n >= 3`, an isomorphism between lattices in `PO(n,1)^0`
  is conjugation by an isometry. The same holds in `PU(n,1)`, `n >= 2`.
- **Uniqueness.** The isometry is unique, because the centralizer of a lattice is
  trivial. So `Comm(G) ≅ Comm_(Isom)(G)`.
- **Margulis.** For non-arithmetic `G`, the commensurator is discrete. A discrete
  group containing the lattice `G` contains it with finite index.
- **Virtual center.** `VZ(G) = 1`, because finite-index subgroups are Zariski dense
  in the adjoint group (Borel density).

**Trust surface.** Cited and not re-read:
- Mostow--Prasad rigidity;
- Margulis's commensurator theorem;
- Borel density;
- the functoriality of abstract commensurators in Step 2;
- the Bass--Serre presentation of `H`.
