---
rg: 2
id: artin-ordinary-foldings-are-retractions-proof
kind: route
title: Check each Artin relator under the folding, using the Garside identity Π(z,z';km') = Δ^k in the dihedral group of label m'
target: artin-ordinary-foldings-are-retractions
requires: []
---

Notation as in the target.

**1. Relators inside Λ.** An edge with both ends in `Λ` has `f(x) = x`, `f(y) = y`, and its relator is a relator of `A_Λ`.

**2. Case (a).** If `f(x) = f(y) = 1`, both sides map to `1`. If `f(x) = f(y) = z`, both sides map to `z^m`.

**3. Case (b), `m = 2k`.** Say `f(x) = z`, `f(y) = 1`. Then `Π(x,y;2k) = (xy)^k ↦ z^k` and `Π(y,x;2k) = (yx)^k ↦ z^k`.

**4. Case (c).** Put `m' = m_zz'`, `m = k m'`, and `Δ = Π(z,z';m')`. In `A_Λ` the relator gives `Δ = Π(z',z;m')`. The images of the two sides are `Π(z,z';m)` and `Π(z',z;m)`; we show both equal `Δ^k`.
- *`m'` even.* `Π(z,z';m) = (zz')^(km'/2) = ((zz')^(m'/2))^k = Δ^k`, and likewise `Π(z',z;m) = (Π(z',z;m'))^k = Δ^k`.
- *`m'` odd.* An alternating word of length `km'` is the concatenation of `k` alternating blocks of length `m'`. Each block has odd length, so consecutive blocks start with different letters, and each block is `Π(z,z';m')` or `Π(z',z;m')`, i.e. `Δ`. Hence `Π(z,z';m) = Δ^k = Π(z',z;m)`.

**5. Retraction.** So `f` respects every defining relator of `A_Γ` and induces `ρ_f : A_Γ → A_Λ`. Let `ι : A_Λ → A_Γ` be induced by the inclusion `Λ ⊆ V`. Then `ρ_f ∘ ι` fixes every generator of `A_Λ`, so it is the identity. Hence `ι` is injective and `ρ_f` is a retraction onto `ι(A_Λ)`.

**6. Cyclic case.** For `f ≡ v`, every edge is in case (a), and `A_{{v}} = <v | > ≅ Z`.

QED
