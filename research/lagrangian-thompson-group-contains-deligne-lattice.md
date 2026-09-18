---
rg: 2
id: lagrangian-thompson-group-contains-deligne-lattice
kind: claim
title: The odometer Lagrangian Thompson group on the Maslov Cantorization of the Lagrangian Grassmannian contains Deligne's lattice for every odd n >= 3, with its centre acting as the odometer
distinct_from:
  deligne-extension-dies-on-lagrangian-cantor-covers: that gives a lift over an abstract Cantor cover and a full group of an unspecified groupoid; this fixes one geometric Cantor model (the Maslov Cantorization), defines the host group explicitly, and for odd n makes the whole centre act as the odometer itself.
  lagrangian-thompson-group-is-finitely-presented: that is the open finiteness question for this host; this is the established containment.
  odometer-2v-is-fp-simple-and-contains-bs12: that host is 2V_tau, the full group of the odometer groupoid times the Cuntz groupoid; this replaces the Cuntz factor by the transformation groupoid of PSp_2n(Z) on the Maslov Cantorization.
---

**ESTABLISHED** (lane proof, not reviewed; textbook inputs on the Lagrangian
Grassmannian flagged). No priority claimed.

## Construction

Fix `n ≥ 2` and `Λ = Λ_n(R)`, the Lagrangian subspaces of `(R^{2n}, ω)`.
- **Walls.** For rational `L_0 ∈ Λ_n(Q)` the **Maslov cycle** is
  `Σ(L_0) = {L : L ∩ L_0 ≠ 0}`, a closed nowhere dense real-algebraic hypersurface.
  `Γ = Sp_{2n}(Z)` permutes the Maslov cycles.
- **Cells.** For a finite `A ⊂ Λ_n(Q)`, the cells of `A` are the finitely many
  components of `Λ ∖ ∪_{L_0 ∈ A} Σ(L_0)`. The complement `Λ^0` of all rational
  Maslov cycles is comeager, hence dense.
- **Maslov Cantorization.** `Y_Λ` is the closure of
  `{(cell_A(L))_A : L ∈ Λ^0}` in the countable product `∏_A {cells of A}` of finite
  discrete sets. `Γ` acts by `γ·(c_A)_A = (γ c_{γ^{-1}A})_A`.
- **Hosts.**
  - `V_Λ` is the topological full group of `PSp_{2n}(Z) ⋉ Y_Λ`: homeomorphisms
    agreeing with some element of `PSp_{2n}(Z)` on each piece of a finite clopen
    partition.
  - `V_Λ^τ` is the topological full group of `O_τ × (PSp_{2n}(Z) ⋉ Y_Λ)`: the
    homeomorphisms of `Z_2 × Y_Λ` that, on the pieces `C(p_i) × U_i` of a finite
    clopen partition, have the form `(p_i x, y) ↦ (p'_i τ^{m_i} x, γ_i y)`.
    Here `τ` is the binary odometer and `O_τ` its Katsura groupoid, as in
    `odometer-2v-is-fp-simple-and-contains-bs12`.

For `n = 1` the walls are the rational points of `RP^1`, and `V_Λ` is the
piecewise-`PSL_2(Z)` model of Thompson's `V`, via the Farey tree (textbook).

## Statement

1. **Cantor model.** `Y_Λ` is a Cantor set. The map `π : Y_Λ → Λ`, sending a cell
   system to the unique point in the intersection of the closures of its cells, is a
   well-defined, continuous, `Γ`-equivariant surjection. So `PSp_{2n}(Z)` acts
   faithfully on `Y_Λ`.
2. **Deligne's lattice inside.** Let `n ≥ 3` be odd and `Γ̃` the preimage of `Γ` in
   the universal cover of `Sp_{2n}(R)`. Then `Γ̃` embeds in `V_Λ^τ`, and a generator
   `c` of its centre goes to the odometer `τ × id`.

## Proof

1. **Separation.** Let `L ≠ L'`. Choose a rational `L_∞` transverse to both, and
   identify Lagrangians transverse to `L_∞` with symmetric matrices, so `L = S`,
   `L' = S'`, `D = S − S' ≠ 0`. If `D` is not negative definite, take `B` rational
   near `S' + εI`; otherwise take it near `S' − εI`. With `ε` small and generic,
   `S − B` and `S' − B` are invertible and have different signatures. The rational
   Lagrangian `graph(B)` has Maslov cycle `{det(· − B) = 0}` in this chart. So the
   arrangement `{L_∞, graph(B)}` puts neighbourhoods of `L` and `L'` into disjoint
   unions of cells.
   - **`π` is well defined.** If two sequences in `Λ^0` with the same limiting cell
     system converged to different points, the separating arrangement would give
     them different cells eventually. So `π` is well defined. It is continuous by
     the same argument, and onto by compactness.
   - **Cantor set.** `Y_Λ` is compact, metrizable and totally disconnected. It is
     perfect because every cell is cut by further rational Maslov cycles, which are
     dense.
   - **Faithful.** The kernel of `Sp_{2n}(R)` on `Λ` is `{±I}`, so `PSp_{2n}(Z)` acts
     faithfully on `Λ`, hence on `Y_Λ`.
2. **The lift.** Let `e` be the endpoint of the lift of the path `e^{iπt} I_n`,
   `t ∈ [0,1]`, in `U(n) ⊂ Sp_{2n}(R)`, and `z` the generator of `π_1(Sp_{2n}(R))`.
   Then `e` is a central lift of `−I`, and `e^2 = z^n`, since `π_1(U(n)) ≅ Z` via
   `det`. On the universal cover of `Λ` (deck group `⟨T⟩`, `π_1(Λ) ≅ Z` via
   `det^2`; textbook), `e` acts as `T^n` and `z` as `T^2`.
   - For odd `n`, put `c = e z^{-(n-1)/2}`. Then `c` acts as `T`, `c^2 = z`,
     `e = c^n`, and `ker(Γ̃ → PSp_{2n}(Z)) = ⟨e, z⟩ = ⟨c⟩ ≅ Z`.
   - As in `deligne-extension-dies-on-lagrangian-cantor-covers` (items 2 and its
     proof), pulling back the universal cover along `π` and choosing a continuous
     section over the Cantor set `Y_Λ` gives a locally constant `k` with
     `Φ(γ̃)(x,y) = (x + k(γ̃,y), γy)` and `Φ(c) = τ × id`.
   - `Φ` is faithful: an element acting trivially maps into the kernel of the
     faithful `PSp_{2n}(Z)`-action, so it lies in `⟨c⟩`, which acts freely.
   - Each `Φ(γ̃)` has the form defining `V_Λ^τ`, with `p_i` empty and `γ_i = γ`. ∎

## Scope

- For even `n`, `e` acts as `T^n` and `z` as `T^2`, and `d = e z^{-n/2}` is a central
  involution acting trivially. So this model carries `Γ̃/⟨d⟩`, with `z ↦ τ^2`. A
  faithful copy of `Γ̃` needs an extra factor on which `−I` acts, for example a
  Cantorized sphere `S^{2n−1}`, as in `deligne-extension-dies-on-lagrangian-cantor-covers`.
- Nothing is claimed about finite generation, finite presentation or simplicity of
  `V_Λ` or `V_Λ^τ`; see `lagrangian-thompson-group-is-finitely-presented`.
