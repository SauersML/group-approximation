---
rg: 2
id: wreaths-over-clopen-stabilizer-cosets-proof
kind: route
title: Push the lamps of each coset onto its finite orbit of clopen sets and apply the type (A) wreath closure for the clopen action
target: wreaths-over-clopen-stabilizer-cosets-lie-in-b-a
requires:
  - fp-clopen-transitive-full-cantor-groups-have-type-a-actions
  - type-a-actors-closed-under-type-a-lamp-wreaths
  - type-a-action-gives-boone-higman-for-subgroups
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

Direct proof (2026-09-18, lane bh-openq-papers). Not independently reviewed.
Conventions: `G` acts on `G/H` on the left, and on functions by
`(g·f)(x) = f(g^(-1) x)`. The product in `L ≀_X G` is
`(f, g)(f', g') = (f·(g·f'), gg')`.

**0. The actor.** Let `𝒮` be the set of proper nonempty clopen subsets of `Y`. By
`fp-clopen-transitive-full-cantor-groups-have-type-a-actions`, `D` acts on `𝒮` with type (A).

**1. Orbits of cosets.** For a coset `gH` put `O_{gH} = { g h U : h ∈ H } ⊆ 𝒮`. It depends only
on the coset.
- *Finite.* `|O_{eH}| = [H : Stab_H(U)] = [H : K] < ∞`, since `K ≤ H` gives `Stab_H(U) = K`.
  Translates have the same size.
- *Equivariant.* `g' O_{gH} = O_{g'gH}` for `g' ∈ G`.
- *Pairwise disjoint.* Suppose `g h U = g' h' U` with `h, h' ∈ H`. Then
  `(g'h')^(-1)(gh) ∈ Stab_G(U) = K ≤ H`, so `g'^(-1) g ∈ H` and `gH = g'H`.

**2. The lamp map.** Define `ι : L^(G/H) -> L^(𝒮)` by `(ι f)(s) = f(gH)` if `s ∈ O_{gH}`, and
`(ι f)(s) = 1` if `s` lies in no `O_{gH}`. By step 1, `ι f` is well defined and finitely
supported, and `ι` is an injective homomorphism (pointwise, with nonempty disjoint fibres).
It is `G`-equivariant: `s ∈ O_{g'gH}` exactly when `g'^(-1) s ∈ O_{gH}`, so
`(g'·ι f)(s) = (ι f)(g'^(-1) s) = f(gH) = (g'·f)(g'gH) = (ι(g'·f))(s)`, and both sides are
`1` off the orbits.

**3. The embedding.** `Φ(f, g) = (ι f, g)` is an injective homomorphism
`L ≀_{G/H} G -> L ≀_𝒮 D`, using `G ≤ D`:
`Φ((f,g)(f',g')) = (ι f · ι(g·f'), gg') = (ι f · (g·ι f'), gg') = Φ(f,g) Φ(f',g')`.

**4. Type (A).** If `L = 1` the wreath product is `G ≤ D`, which is in `B_A` by step 0.
Otherwise `L ≤ Λ` for some nontrivial group `Λ` with a type (A) action on a set `Z`, by the
definition of `B_A`. Then `L ≀_𝒮 D ≤ Λ ≀_𝒮 D`, and by
`type-a-actors-closed-under-type-a-lamp-wreaths` the group `Λ ≀_𝒮 D` has a type (A) action
on `𝒮 × Z`. So `L ≀_{G/H} G ∈ B_A`.

**5. Simple envelope.** A finitely generated subgroup of a group with a type (A) action
embeds in a finitely presented simple group (`type-a-action-gives-boone-higman-for-subgroups`).
When `L` and `G` are finitely generated, so is `L ≀_{G/H} G`, since `G` is transitive on
`G/H`. ∎
