---
rg: 2
id: simple-group-in-fp-simple-iff-fp-just-infinite-host-proof
kind: route
title: A simple target is just-infinite; conversely the image of the simple group is an infinite simple subgroup, so the structure lemma applies
target: simple-group-in-fp-simple-iff-fp-just-infinite-host
requires: [just-infinite-over-simple-subgroup-gives-fp-simple-host]
---

**1 ⇒ 2.** Let `ι : S -> T` embed `S` in a finitely presented simple group `T`.
`T` is infinite because `S` is. Its only nontrivial normal subgroup is `T` itself,
which has index 1. So `Γ = T` and `ρ = ι` satisfy (2).

**2 ⇒ 1.** `ρ` is nontrivial, and its kernel is a normal subgroup of the simple
group `S`, so `ρ` is injective. Put `S' = ρ(S) ≅ S`, an infinite simple subgroup
of `Γ`. `Γ` is finitely presented, so it is finitely generated. By hypothesis,
every nontrivial normal subgroup of `Γ` inside `<<S'>>^Γ` has finite index. These
are exactly the hypotheses of `just-infinite-over-simple-subgroup-gives-fp-simple-host`.
That claim's proof uses finite generation only for `Γ` (its scope note, Step 4),
never for the simple subgroup. Its clauses 1 to 3 give a finitely presented
infinite simple group `T`, a finite-index normal `R ≅ T^k` of `Γ` containing
`S'`, and an injective coordinate projection `S' -> T`. So `S ≅ S'` embeds in
`T`. ∎

**Last sentence of the claim.** A residually finite group has no infinite simple
subgroup. For `s ≠ 1` in such a subgroup `S''`, take a finite quotient where `s`
survives. Its kernel meets `S''` in a proper normal subgroup, which is trivial,
so `S''` embeds in a finite group.
