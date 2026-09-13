---
rg: 2
id: stallings-group-has-a-type-f-mapping-torus-proof
kind: route
title: "Explicit endomorphism of the Stallings group through F_2^3 with a type-F mapping torus"
target: stallings-group-has-a-type-f-mapping-torus
requires: []
---

**The group.** `F = F(a, b)` and `χ: F → Z` with `a, b ↦ 1`.
`SB_3 = ker(χ_1 + χ_2 + χ_3: F^3 → Z)`. It is finitely presented and not
`FP_3`: Stallings, *A finitely presented group whose 3-dimensional integral
homology is not finitely generated*, Amer. J. Math. 85 (1963); in general
`SB_n` is of type `F_{n-1}` but not `FP_n` (Bieri, *Homological dimension of
discrete groups*, QMC Notes).

**An embedding `F → ker χ`.** Use the transversal `{a^k : k ∈ Z}` for
`ker χ`, on which `χ` is a bijection to `Z`. By Reidemeister--Schreier,
`ker χ` is free on `b_k = a^k b a^{-(k+1)}` for `k ∈ Z`; the generators
`a^k a a^{-(k+1)}` are trivial. Define `ω: F → ker χ` by `a ↦ b_0 = b a^{-1}`
and `b ↦ b_1 = a b a^{-2}`. It sends a basis to part of a basis, so it is
injective.

**The endomorphism.** Let `ι: SB_3 → F^3` be the inclusion and
`ȷ = ω × ω × ω: F^3 → (ker χ)^3 <= SB_3`. Both are injective, and so is
`ψ = ȷι: SB_3 → SB_3`.

**Two descriptions.** The formal isomorphism written out in route
`fp-f-infinity-hosts-from-rp-fp-infinity-host`, Step 2, holds for any
injective `ι: A → B` and `ȷ: B → A`. It gives
`SB_3 *_{ȷι} ≅ F^3 *_{ιȷ}`, where `ιȷ = ω^3: F^3 → F^3` is injective.

**Type `F`.** Let `Y = (S^1 ∨ S^1)^3`, a finite aspherical complex with
`π_1 = F^3`, and let `f: Y → Y` be a cellular map inducing `ω^3`, the product
of maps of the wedge realizing `ω`. The mapping torus `M_f` is a finite
complex with `π_1(M_f) = F^3 *_{ω^3}`. It is aspherical: it is a graph of
aspherical spaces whose edge maps are `π_1`-injective (Scott--Wall, *Topological
methods in group theory*, 1979). So `SB_3 *_ψ ≅ π_1(M_f)` has a finite
`K(π, 1)`.
