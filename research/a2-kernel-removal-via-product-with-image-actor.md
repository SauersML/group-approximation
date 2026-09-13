---
rg: 2
id: a2-kernel-removal-via-product-with-image-actor
kind: route
title: Pass to the faithful quotient one way, and the other way let G x Λ act through Λ with G embedded along the graph of G → Λ
target: a2-kernel-removable-iff-image-in-type-a2-actor
requires:
  - fp-quotient-iff-kernel-finitely-normally-generated
---

Notation as in the target.

**(1 ⇒ 2).** Let `ι`, `G′ ↷ S′` and `K′` be as in item 1.
- **Finite presentation.** `G′/K′` is finitely presented, because `G′` is and
  `K′` is finitely normally generated
  (`fp-quotient-iff-kernel-finitely-normally-generated`).
- **Type (A_2).** The induced action of `G′/K′` on `S′` is faithful. Every point
  stabilizer in `G′` contains `K′`, so the stabilizer in `G′/K′` is its image and
  is finitely generated. The orbits of `G′/K′` on `S′ x S′` are those of `G′`,
  finitely many.
- **The embedding.** `ῑ(gK) = ι(g)K′` is well defined since `ι(K) ⊆ K′`. It is
  injective: if `ι(g) ∈ K′`, then `ι(g) ∈ ι(G) ∩ K′ = ι(K)`, so `g ∈ K` because
  `ι` is injective.

So `G/K` embeds in `G′/K′`, which admits the type (A_2) action on `S′`.

**(2 ⇒ 1).** Let `j: G/K → Λ` be injective, where `Λ` acts on a non-empty set `Ω`
with type (A_2), and let `π: G → G/K` be the quotient map. Put

```text
G′ = G x Λ,   (g, λ) . ω = λ . ω   (ω ∈ Ω),   ι(g) = (g, jπ(g)).
```

- **Finite presentation.** `G′` is finitely presented, since `G` and `Λ` are.
- **Point stabilizers.** `Stab_(G′)(ω) = G x Stab_Λ(ω)` is finitely generated,
  since `G` and `Stab_Λ(ω)` are. Stabilizers of two or more points carry no
  condition at `n = 2`.
- **Orbits on Ω x Ω.** They are the `Λ`-orbits, finitely many.

So `G′ ↷ Ω` is of type [A_2].
- **Kernel.** `Λ` acts faithfully, so the kernel is `K′ = G x {1}`. Let `X` be a
  finite generating set of `G`. The normal closure in `G′` of `{(x, 1) : x ∈ X}`
  contains every `(gxg^(-1), 1)`, hence all of `G x {1}`. So `K′` is finitely
  normally generated.
- **The embedding.** `ι` is a homomorphism, injective because its first
  coordinate is the identity. Moreover `(g, jπ(g)) ∈ G x {1}` iff `jπ(g) = 1`
  iff `g ∈ K`, since `j` is injective. Hence `ι(G) ∩ K′ = {(k, 1) : k ∈ K} = ι(K)`.

This is item 1 with `S′ = Ω`. `∎`
