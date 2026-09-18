---
rg: 2
id: central-extension-untwisting-over-boundaries
kind: claim
title: A finite central extension can be realized over a boundary action with the kernel acting freely only if its class dies on every point stabilizer, and stabilizing by the Cuntz groupoid cannot remove this obstruction
distinct_from:
  cocompact-tree-product-lattices-lie-in-type-a-class: that handles faithful lattices; this isolates what blocks the finite central kernels left in Attempt 9 of product-of-trees-lattices-satisfy-permutational-boone-higman.
  stabilized-kgraph-full-groups-have-type-a-actions: that uses the Cuntz groupoid to make clopen sets comparable; this shows the same stabilization does not trivialize groupoid twists.
---

**ESTABLISHED** (lane proof, elementary; not independently reviewed). This is
negative guidance for the finite-kernel case. It does not decide that case.

**Setting.** A group `C̄` acts on a compact totally disconnected space `Y`.
`1 -> A -> C -> C̄ -> 1` is a central extension with `A` finite abelian and class
`ω ∈ H²(C̄; A)`. `C` acts on `Y` through `C̄`, so `A` acts trivially.

1. **Untwisting criterion.** `C` acts on `Y x A` by
   `γ̃(y, a) = (γ̄y, a + κ(γ̃, y))`, with `κ` continuous and `κ(z, y) = z` for
   `z ∈ A`, if and only if `ω` maps to `0` in `H²(C̄; C(Y, A))` under the constants
   `A -> C(Y, A)`. In that case `A` acts freely, and the action is faithful when `C̄`
   acts faithfully on `Y`.
2. **Stabilizer obstruction.** If such a `κ` exists, then `κ(·, y)` restricted to
   `Stab_C(y)` is a homomorphism to `A` that is the identity on `A`. So `ω` restricts
   to `0` on `Stab_(C̄)(y)` for every `y ∈ Y`.
3. **The Cuntz groupoid does not help.** Let `𝒢` be an étale groupoid and `𝒦` any
   ample groupoid with a unit `t_0` (for example the Cuntz groupoid `O_2`). The maps
   `g ↦ (g, t_0)` and `(g, k) ↦ g` make the continuous cohomology `H^*(𝒢; A)` a
   retract of `H^*(𝒢 x 𝒦; A)`. So a twist of `𝒢` by `A` pulled back to `𝒢 x O_2` is
   trivial only if it was already trivial.
   - **Pitfall.** Matui's homology of `𝒢 x O_2` vanishes (Künneth, and
     `H_*(O_2) = 0`), but that does not imply vanishing of the continuous cohomology
     that classifies twists. The dual of `C_c(W, Z)` consists of finitely additive
     `A`-valued measures on the compact open subsets of `W`, not continuous `A`-valued
     functions, so no universal coefficient theorem links the two.
4. **Tree products.** Let `C̄` be a faithful cocompact lattice on a product of trees
   and `Y = ∂X`. Suppose `Z² = <g, h> ≤ C̄` stabilizes a periodic flat
   `F = L_1 x L_2`. Then `Z²` fixes the boundary points of `F`, and item 2 forces
   `ω|_(Z²) = 0`, that is, lifts of `g` and `h` commute in `C`. With the phase
   coordinate of `tree-lattice-kgraph-power-phase-proof` (`Y = ∂X x (Z/N)^k`), the
   stabilizer of a phase point is the sublattice of `Z²` with lags `≡ 0 mod N`. The
   condition becomes `ω = 0` on each such sublattice. For flats whose translation
   lengths are all divisible by `N`, that is the full `Z²`.
5. **Test case.** Let `Λ` be a finitely presented simple Burger--Mozes lattice on
   `T_(2m) x T_(2n)` acting simply transitively on vertices, with quotient the
   one-vertex square complex `K` (`m + n` loops, `mn` squares).
   - `H_1(Λ) = 0` and `χ(K) = (m-1)(n-1)`, so `H_2(Λ; Z) = H_2(K)` is free of rank
     `(m-1)(n-1) - 1`.
   - `H²(Λ; A) = Hom(H_2(K), A)`, and `ω` gives a perfect extension exactly when it
     is onto. So nontrivial perfect finite central extensions `Λ̃` exist as soon as
     `(m-1)(n-1) >= 2`.
   - By item 4, the boundary route reaches `Λ̃` only if `ω` vanishes on the torus
     class of every periodic flat whose lags are `≡ 0 mod N`. Whether some `ω ≠ 0`
     does so, and whether that suffices, is not decided here.
