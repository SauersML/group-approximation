---
rg: 2
id: double-swap-embeds-group-in-derived-subgroup
kind: claim
title: Every group embeds in the derived subgroup of its double extended by the swap, inside one commutator
distinct_from:
  rf-groups-lie-in-derived-subgroups-of-rf-groups: that is the residually finite statement proved through Ore's commutator theorem and a doubling of the finite quotients; this is a two-line construction valid for every group, and it transports along any class closed under finite direct products and index-two extensions, so it also covers sofic, hyperlinear, LEF and amenable inputs.
---

**ESTABLISHED (unreviewed).** Let `Γ` be a group, `Δ = (Γ × Γ) ⋊ C_2` with `C_2 = ⟨s⟩` acting by
the swap `s(a,b)s^(-1) = (b,a)`. Then

    ι : Γ -> Δ,   ι(γ) = (γ, γ^(-1)) = [(γ,1), s]

is an injective homomorphism whose image lies in `[Δ, Δ]`; in fact every element of the image is a
single commutator of elements of `Δ`.

Moreover:
- `Δ` is finitely generated if `Γ` is, and `|Δ : Γ × Γ| = 2`.
- If a class of groups is closed under finite direct products and under extensions by finite groups,
  then `Δ` belongs to it whenever `Γ` does. This covers residually finite, LEF, amenable, sofic,
  hyperlinear and linear sofic groups.

**Use.** For a ring `R` whose unit group contains `Δ`, the Whitehead identity
`diag(a,a^(-1),1) diag(b,b^(-1),1) diag((ab)^(-1),ab,1) = diag(1,[a^(-1),b^(-1)],1)` puts
`diag(1, u_(ι(γ)), 1)` in `E_3(R)`. So a group embeds in `EL_3(R)` as soon as its double sits in the
unit group, with no Ore theorem and no hypothesis on `Γ`.

**Firewall.** The map `a ↦ diag(a, a^(-1), 1)` is not a homomorphism on noncommuting units, so the
commutator form above is the point: it is what makes a single position of the diagonal available.

**Credit.** The identity `(γ, γ^(-1)) = [(γ,1), s]` is folklore; the wreath-product form
`Γ ≀ C_2` is standard in this role. No novelty is claimed. Bounded check: a grep of this graph on
2026-09-13 for derived-subgroup embeddings, which found only the residually finite route above.

Route: `double-swap-embeds-group-in-derived-subgroup-proof`.
