---
rg: 2
id: a2-kernel-removal-iff-image-pbh-proof
kind: route
title: Pass to the quotient for one direction, and multiply by a faithful actor acting through the second factor for the other
target: a2-kernel-removal-iff-image-satisfies-pbh
requires: []
---

Terminology is as in the claim: "type [A_2]", "type (A_2)", "embeds" for pairs,
and "removable".

**Lemma 1 (standard).** Let `G` be finitely presented and `K ⊴ G`.
1. If `K` is the normal closure of finitely many elements, `G/K` is finitely
   presented.
2. If `G/K` is finitely presented, `K` is the normal closure of finitely many
   elements.

*Proof.* Fix a finite generating set `X` of `G` and the surjection
`p: F(X) → G`, with `ker p` the normal closure of a finite set `R`.

(1) If `K` is the normal closure of `k_1, ..., k_m`, pick words `w_i` with
`p(w_i) = k_i`. Then `G/K = ⟨X | R ∪ {w_1, ..., w_m}⟩`.

(2) A finitely presented group has a finite presentation on every finite
generating set. Let `Q = ⟨Y | T_0⟩` be finite and let `X` be another finite
generating set of `Q`. Write each `y` as a word `u_y` in `X`, and each `x` as a
word `v_x` in `Y`. Put `Q_1 = ⟨X | T_0(u), x^-1 v_x(u) (x in X)⟩`.
- The natural map `Q_1 → Q` is surjective and well defined.
- `y ↦ u_y` defines a homomorphism `Q → Q_1`, because the relators `T_0(u)` hold
  in `Q_1`.
- The two maps are mutually inverse on generators: the relators `x = v_x(u)` do
  this on `X`, and on `Y` it is immediate.

Apply this to `Q = G/K` with generating set the image of `X`. The kernel of
`q = π∘p : F(X) → G/K` is the normal closure of a finite set `T`. Since `p` is
surjective, `p(ker q) = p(p^-1(K)) = K`, and `p` maps normal closures onto
normal closures, so `K` is the normal closure of `p(T)` in `G`. □

**Lemma 2.** Let `G′ ↷ S′` be of type [A_2] with kernel `K′` finitely normally
generated. Then the induced action `G′/K′ ↷ S′` is of type (A_2).

*Proof.* The induced action is faithful by the definition of `K′`, and `G′/K′`
is finitely presented by Lemma 1(1). Since `K′ ≤ Stab_(G′)(s)` for every `s`,
the stabilizer `Stab_(G′/K′)(s) = Stab_(G′)(s)/K′` is finitely generated. The
orbits of `G′` and of `G′/K′` on `S′ x S′` coincide, so there are finitely many.
□

**(1) ⇒ (2).** Let `ι: G → G′` be injective with `ι(G) ∩ K′ = ι(K)`, where
`G′ ↷ S′` is of type [A_2] and `K′ = ker(G′ ↷ S′)` is finitely normally
generated. The composite `G → G′ → G′/K′` has kernel
`ι^-1(K′) = ι^-1(ι(G) ∩ K′) = ι^-1(ι(K)) = K`, using injectivity of `ι`. So
`G/K` embeds in `G′/K′`, which has a type (A_2) action by Lemma 2. □

**(2) ⇒ (1).** Let `Λ ↷ T` be of type (A_2) and let `j: G/K → Λ` be injective.
Write `q: G → G/K`. Put `G′ = G x Λ`, acting on `T` by `(g, λ).t = λ t`.
- `G′` is finitely presented, as a direct product of two finitely presented
  groups: take both presentations and the commutators of the two generating
  sets.
- `Stab_(G′)(t) = G x Stab_Λ(t)` is finitely generated, because `G` is.
- The `G′`-orbits on `T x T` are the `Λ`-orbits, so there are finitely many.

So `G′ ↷ T` is of type [A_2]. Its kernel is `K′ = G x {1}`, since `Λ` acts
faithfully. `K′` is normal in `G′` and generated, hence normally generated, by
`(x, 1)` for `x` in a finite generating set of `G`.

Define `ι: G → G′` by `ι(g) = (g, j(q(g)))`. It is a homomorphism, injective
because its first coordinate is the identity. Moreover
`ι(g) ∈ K′ ⟺ j(q(g)) = 1 ⟺ q(g) = 1 ⟺ g ∈ K`, so `ι(G) ∩ K′ = ι(K)`, and the
action is removable. □

**Corollary (a).** If `G/K` is finitely presented, Lemma 1(2) makes `K` finitely
normally generated in `G`, so the identity embeds `(G,K)` in itself, with
`G′ ↷ S′ = G ↷ S`. □

**Corollary (b).** Apply the Theorem to each type [A_2] action. The first part of
FFWZ Question 5.9 says every such action is removable, which by the Theorem says
every action image embeds in a group admitting a type (A_2) action. □
