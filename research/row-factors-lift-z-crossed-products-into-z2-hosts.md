---
rg: 2
id: row-factors-lift-z-crossed-products-into-z2-hosts
kind: claim
title: If a Z^2-subshift X factors along rows onto a Z-subshift Y, then LC(Y,K) ⋊ Z embeds unitally in LC(X,K) ⋊ Z^2; so gate U over Z^2 splits into a one-dimensional unit problem over an effective Y and a realization problem for G2
distinct_from:
  subshift-languages-give-monomial-algebras-in-crossed-products: that realizes monomial algebras of languages; this transfers every construction over a Z-subshift (units, matrices, Leavitt tensors) to Z^2 hosts at once.
  translation-like-inputs-embed-in-full-groups-over-a-fixed-group: that embeds translation-like inputs in full groups over a fixed group; this is the ring-level lifting that lets any one-dimensional unit construction be used over a Z^2 SFT.
---

**ESTABLISHED** (lane proof, bh-algebra, elementary, not reviewed).

**Setting.** `Y ⊆ Σ^Z` is a subshift with shift `σ`. `X` is a `Z^2`-subshift with a continuous surjection
`ρ : X -> Y` such that `ρ(e_1 · x) = σ(ρ(x))`, where `e_1 · x` denotes translation by `e_1`. For example,
`ρ(x)` reads the row through the origin of one layer, and every sequence of `Y` occurs as such a row.

**Claim.** The map
`Φ(Σ_n f_n u^n) = Σ_n (f_n ∘ ρ) u_(n e_1)`
is an injective unital ring homomorphism `LC(Y, K) ⋊ Z -> LC(X, K) ⋊ Z^2`. Consequently:
1. `Φ ⊗ id` embeds `(LC(Y, K) ⋊ Z) ⊗ L` in `(LC(X, K) ⋊ Z^2) ⊗ L`, and every `GL_n`, every unit group and
   every full group over `Y` embeds in the corresponding object over `X`.
2. **Gate U decouples.** If an input `G` embeds in `((LC(Y, F_2) ⋊ Z) ⊗ L)^x` for an effective `Y`, then it
   embeds in `((LC(X, F_2) ⋊ Z^2) ⊗ L)^x` for every `Z^2`-SFT `X` that factors along rows onto `Y`. The
   one-dimensional simulation theorems (Durand--Romashchenko--Shen, Aubrun--Sablik; cited, not read
   here) supply such SFTs.
   - The embedding problem lives entirely in one dimension, with no finiteness or rigidity requirement on
     `Y`.
   - Finite presentation and simplicity of the host are the G2 requirement, which becomes: a free minimal
     quantum-rigid `Z^2`-SFT with a row factor onto a prescribed effective `Y`.

**Proof.**
- `f ↦ f ∘ ρ` is an injective unital homomorphism `LC(Y) -> LC(X)`: it is injective because `ρ` is onto.
- Covariance: `u_(e_1) (f ∘ ρ) u_(e_1)^(−1) = (f ∘ σ^(−1)) ∘ ρ` (with the matching convention), because `ρ`
  intertwines translation by `e_1` with `σ`. So `Φ` respects the crossed-product relations.
- Injectivity: the `u_(n e_1)` are part of a basis of `LC(X) ⋊ Z^2` as a left `LC(X)`-module, and each
  `f_n ∘ ρ ≠ 0` when `f_n ≠ 0`. ∎

**Lesson for general BH.** On Track B the complexity and rigidity requirements live in different
dimensions and can be solved separately. Any unit-level embedding over a one-dimensional effective
subshift, where languages are freely programmable and nothing needs to be finitely presented, transfers
verbatim to a finitely presented host once G2 realizes that subshift as a row factor of a rigid SFT. So
gate U is really a one-dimensional problem: which groups sit in the units of `(LC(Y) ⋊ Z) ⊗ L` for
effective `Y`? Its full group is `[[𝒪_2 × (Z ⋉ Y)]]`, Thompson's `V` with an effective oracle. Its
non-permutational units are EL over language rings, and the Leavitt factor supplies the non-sofic part
(`amenable-crossed-product-units-are-linear-sofic`).
