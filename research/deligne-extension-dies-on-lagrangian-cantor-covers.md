---
rg: 2
id: deligne-extension-dies-on-lagrangian-cantor-covers
kind: claim
title: Deligne's central extension becomes trivial on every Cantor Sp_2n(Z)-space covering the real Lagrangian Grassmannian, so Deligne's lattice is an odometer lift over such spaces
distinct_from:
  deligne-lattice-satisfies-boone-higman: that is the open embedding question; this gives the lift half of one route to it (an explicit faithful action of the lattice on Z_2 x Y by odometer-cocycle maps), and leaves finite presentation of a host open.
  odometer-lift-central-extensions-of-v-subgroups-into-2v-tau: that lifts extensions of subgroups of V into 2V_tau; Sp_2n(Z) is not in V (property (T) against Haagerup), so this uses a different base action, the real Lagrangian Grassmannian.
  groupoid-lifts-of-central-extensions-need-no-invariant-measure: that is the matching necessary condition (no invariant probability measure); the spaces here satisfy it.
---

**ESTABLISHED** (lane proof, elementary topology, not reviewed). No priority claimed.

## Setting

- `n ≥ 2`, `Γ = Sp_{2n}(Z)`, `Γ̃` is its preimage in the universal cover of
  `Sp_{2n}(R)` (Deligne's lattice; `deligne-lattice-satisfies-boone-higman`), and
  `z` generates `ker(Γ̃ → Γ) ≅ π_1(Sp_{2n}(R)) ≅ π_1(U(n)) ≅ Z`.
- `Λ = Λ_n(R) = U(n)/O(n)` is the Lagrangian Grassmannian, with
  `π_1(Λ) ≅ Z` via `det^2 : U(n)/O(n) → S^1` (Arnold, textbook). `p : Λ̃ → Λ` is
  its universal cover, and `T` generates the deck group.

## Statement

1. **Equivariant Cantor covers exist.** For every compact metrizable `Γ`-space `M`,
   there is a Cantor set `Y` with a `Γ`-action and an equivariant continuous surjection
   `Y → M`. The action on `Y` is faithful if the action on `M` is.
2. **The lift.** Let `Y` be a Cantor set with a faithful `Γ`-action and a
   `Γ`-equivariant continuous map `f : Y → Λ`. Then there is a locally constant
   `k : Γ̃ × Y → Z` such that

       Φ(γ̃)(x, y) = (x + k(γ̃, y), γ y)      on Z_2 × Y

   is a faithful action of `Γ̃`, with `Φ(z)(x,y) = (x + 2, y)`. Equivalently, Deligne's
   class dies in `H^2(Γ; C(Y, Z))`.
3. **Such `Y` exist.** Apply item 1 to `M = Λ × S^{2n−1}` with the diagonal action,
   and compose with the projection to `Λ`. The action on `M` is faithful: the kernel
   of `Sp_{2n}(R)` on `Λ` is `{±I}`, and `−I` is the antipodal map on `S^{2n−1}`.

So `Γ̃` embeds in the full group of `O_τ × (Γ ⋉ Y)`: homeomorphisms of `Z_2 × Y`
that are, piecewise on finitely many clopen rectangles, of the form
`(x, y) ↦ (τ^{n_i} x, γ_i y)`. Here `O_τ` is the odometer groupoid (the first
coordinate of `odometer-2v-is-fp-simple-and-contains-bs12`).

## Proof

1. Let `K` be a Cantor set and `π : K → M` a continuous surjection with perfect
   fibres. Such a `π` exists: compose a surjection from the Cantor set with the
   projection `K × K → K`. Put

       Y = {κ ∈ K^Γ : π(κ(γ)) = γ · π(κ(1)) for all γ},   (δ·κ)(γ) = κ(γδ).

   Then `Y` is closed in the Cantor set `K^Γ`, since `Γ` is countable. The map
   `κ ↦ π(κ(1))` is equivariant and onto. `Y` is perfect, because a coordinate
   outside any finite window can be moved inside a perfect fibre.
2. Pull back: `Ỹ = Y ×_Λ Λ̃` is a covering space of `Y` with deck group `⟨T⟩`.
   Coverings of a compact totally disconnected space are trivial: take evenly
   covered clopen pieces of a finite clopen partition and choose a section on each.
   So there is a continuous section `s`. `Γ̃` acts on `Λ̃` by lifting the action of
   the connected group `Sp_{2n}(R)`, commuting with deck translations, and so acts on
   `Ỹ` by `γ̃·(y, L̃) = (γy, γ̃L̃)`. This is well defined because `f` is
   equivariant. Define `k` by `γ̃ · s(y) = T^{k(γ̃,y)} s(γy)`. It is continuous into
   `Z`, hence locally constant, and satisfies `k(γ̃γ̃', y) = k(γ̃', y) + k(γ̃, γ'y)`.
   So `(m, y) ↦ (m + k(γ̃, y), γy)` is an action on `Z × Y`, and it extends to
   `Z_2 × Y` by the same formula.
   - **The central element.** `z` is the loop `diag(e^{2πit}, 1, …, 1)` in
     `U(n) ⊂ Sp_{2n}(R)`. Under the orbit map to `Λ`, followed by `det^2`, it winds
     twice. So `z` acts on `Λ̃` as `T^{±2}`; orient `T` so that it is `T^2`.
   - **Faithfulness.** An element acting trivially maps to the kernel of the
     faithful action of `Γ` on `Y`, so it lies in `⟨z⟩`. There `z^j` translates by
     `2j`. ∎

## What remains for Boone–Higman of `Γ̃`

Item 2 reduces `deligne-lattice-satisfies-boone-higman` to finding a Cantor
`Γ`-space `Y` of this kind for which the full group of `O_τ × (Γ ⋉ Y)`, or a
subgroup containing `Φ(Γ̃)`, embeds in a finitely presented simple group. The
natural candidate is a *Lagrangian Thompson group*: `Y` a Cantorization of `Λ`
along the rational Maslov cycles `{L : L ∩ L_0 ≠ 0}`, `L_0 ∈ Λ(Q)`. Their finite
arrangements cut `Λ` into finitely many cells, indexed by inertia indices; for two
cycles the complement is a set of symmetric matrices with an invertibility
condition. The full group of piecewise-`Sp_{2n}(Z)` maps on that `Y` is the
higher-rank analogue of `T ≤ V` acting on the Cantorized circle.
- Its finite presentation is open.
- It is the same kind of question as survey Remark 5.5 (Thurston's PIP groups).
- By `groupoid-lifts-of-central-extensions-need-no-invariant-measure`, no host of this
  lift form can be built over an action with an invariant probability measure, so
  the non-amenable boundary behaviour of `Λ` is essential.

**Not a route through circles.** An action of `Γ̃` on `R` commuting with
translation, with `z` a translation, is an action of `Γ` on `S^1` with Euler class
`c`. Actions of higher-rank lattices on the circle have finite image (Ghys;
Burger–Monod; Witte Morris; textbook, not read here). So the Lagrangian
Grassmannian, of dimension `n(n+1)/2`, cannot be replaced by a circle.
