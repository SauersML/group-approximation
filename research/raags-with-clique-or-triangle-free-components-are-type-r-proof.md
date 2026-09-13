---
rg: 2
id: raags-with-clique-or-triangle-free-components-are-type-r-proof
kind: route
title: Type R for RAAGs with complete or triangle-free components, by free-product closure
target: raags-with-clique-or-triangle-free-components-are-type-r
requires:
  - rips-complexes-of-integer-lattices-are-contractible
  - triangle-free-raags-are-rips-type-r
  - rips-type-r-closed-under-finite-edge-group-splittings
---

Let `Γ_1, …, Γ_k` be the connected components of `Γ`.

1. **Splitting.** `A_Γ = A_{Γ_1} * ⋯ * A_{Γ_k}`, and the standard generating
   set is the disjoint union `V(Γ) = V(Γ_1) ⊔ ⋯ ⊔ V(Γ_k)`. There are no
   relations between vertices in different components, so the presentation
   is the free product of the component presentations.
2. **Components.**
   - If `Γ_i` is the complete graph on `m` vertices, then
     `(A_{Γ_i}, V(Γ_i)) = (Z^m, standard basis)`. Its word metric is `d_1`, so it
     is of type R with `r_0 = m^2(2m − 1)`
     (`rips-complexes-of-integer-lattices-are-contractible`).
   - If `Γ_i` is triangle-free, `(A_{Γ_i}, V(Γ_i))` is of type R
     (`triangle-free-raags-are-rips-type-r`).
   - An isolated vertex is complete (`Z`), and a single edge is complete
     (`Z^2`), so both rules agree on the overlap.
3. **Induction.** Put `G_j = A_{Γ_1} * ⋯ * A_{Γ_j}` with generating set
   `S_j = V(Γ_1) ⊔ ⋯ ⊔ V(Γ_j)`. `G_1` is of type R by step 2. If `(G_j, S_j)` is of
   type R, apply the amalgam clause of
   `rips-type-r-closed-under-finite-edge-group-splittings` with `C = 1`. Its
   hypothesis that the generating sets contain the non-trivial elements of `C`
   is vacuous. So `(G_j * A_{Γ_{j+1}}, S_j ⊔ V(Γ_{j+1})) = (G_{j+1}, S_{j+1})` is
   of type R. At `j = k` this is `(A_Γ, V(Γ))`.

Scope: the constant `r_0` depends on `Γ` through the imported theorems. The
closure theorem was imported from an unrefereed preprint, so this corollary
carries that dependence.
