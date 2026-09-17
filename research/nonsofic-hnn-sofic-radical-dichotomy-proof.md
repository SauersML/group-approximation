---
rg: 2
id: nonsofic-hnn-sofic-radical-dichotomy-proof
kind: route
title: Ultraproduct of base-free models, local soficity of the largest sofic quotient, Serre freeness, and the contrapositive of amplification
target: nonsofic-hnn-sofic-radical-dichotomy
requires: [random-labeling-hnn-soficity-criterion]
---

Written proof, 2026-09-17. Not Lean-checked. The notation is that of
`research/random-labeling-hnn-soficity-criterion-proof.md`.

## 1. `G/N` is sofic

Let `F ⊂ G/N` be finite, with lifts `g_1..g_k`. For `i != j`, `g_i g_j^(-1)`
is not in `N`, so some homomorphism `ψ_(ij)` to a sofic group `Λ_(ij)`
does not kill it. The product `∏ ψ_(ij)` factors through `G/N`, lands in a
finite product of sofic groups, which is sofic, and is injective on `F`. A
group that is locally embeddable into sofic groups is sofic, so `G/N` is
sofic. Also `N = 1` iff `G` is sofic.

## 2. (I) iff `N ∩ H = 1`

(⇐) Suppose `N ∩ H = 1`. Let `Z` be a sofic approximation of `G/N` at scale
`(R, ε)`, viewed as a model of `G` through `G -> G/N`. A word trivial in `G` is
trivial in `G/N`, so it fixes `(1-ε)|Z|` points. A word in `S` that is
nontrivial in `H` is nontrivial in `G/N`, so it fixes at most `ε|Z|` points.
That is (I).

(⇒) Suppose (I). Take models `X_n` at scales `(R_n, ε_n) -> (∞, 0)`, and a
nonprincipal ultrafilter `ω`. Let `U = ∏_ω Sym(X_n)`, the metric ultraproduct
with normalized Hamming distance. Relator words are trivial in `U`, so the
assignment defines a homomorphism `Ψ : G -> U`. If `h in H` is nontrivial, then
`d(Ψ(h), 1) = 1` by (I), so `Ψ` is injective on `H`. Every countable subgroup of
`U` is sofic, so `Ψ(G)` is sofic. Hence `N ⊂ ker Ψ`, and `N ∩ H ⊂ ker Ψ ∩ H = 1`.

## 3. Case (i)

This is the negation of (I) together with §2. The equivalent forms follow:
* **Every sofic image kills a base element.** Any homomorphism to a sofic group
  has kernel containing `N`, and so kills `N ∩ H != 1`.
* **No approximate model is free on `H`-words.** Such models would give (I).

Soficity of `H` does not interfere, because (I) concerns models of `G`, not of
`H`.

## 4. Case (ii)

Assume `G` is not sofic and `N ∩ H = 1`.

**`N` is free.** `N` is normal, so `N ∩ gHg^(-1) = g(N ∩ H)g^(-1) = 1`, and
every vertex stabilizer of `T` meets `N` trivially. An HNN extension acts on
its Bass--Serre tree without inversions. So `N` acts freely on `T`, and by
Serre's theorem `N` is free. It is nontrivial because `G` is not sofic.

**`Q`.** `H -> Q` is injective because `N ∩ H = 1`. `Q` satisfies the images
of the HNN relations. A nontrivial element of `N` has a Britton-reduced form,
and it is not in `H`. So its `t`-length is at least 1, and it dies in `Q`.

**(II) fails.** By §2, (I) holds. If (II) also held, the criterion would make
`G` sofic. So (II) fails. By §4 of the criterion proof (amplification), (II)
holds as soon as every `h` in `(H \ A) ∪ (H \ B)` has some `δ_h > 0` such
that, at every scale `(R, ε)`, some partitioned `(R, ε)`-model separates `h` on
at least `δ_h` of its points. Negating this gives the stated `h`.

**Amenable quotients.** Let `ψ : G ->> Γ` with `Γ` amenable. If `ψ(h)` were not
in `ψ(A)`, the Følner model of §5 of the criterion proof would separate `h` at
every interior point, at every scale. Its density is at least `1 - ε > δ`,
which is a contradiction. The `B`-side is the same.

**`Q` is not amenable.** Otherwise apply the previous paragraph to
`ψ : G -> Q`. Here `ψ` is injective on `H`, so `h` not in `A` gives `ψ(h)` not
in `ψ(A)`, and the same holds on the `B`-side. That is a contradiction.

**Free-by-sofic.** `1 -> N -> G -> Q -> 1`, with `N` free and `Q` sofic.

## 5. The one-relator reduction

Two standard inputs are used.
* **Torsion.** One-relator groups with torsion are hyperbolic and virtually
  special (Wise), hence linear and sofic.
* **Magnus--Moldavanskii.** A torsion-free one-relator group with at least two
  generators is, or embeds into, an HNN extension of a one-relator group with a
  shorter hierarchy, over free Magnus subgroups.

Soficity passes to subgroups. So if the witness embeds into such an HNN
extension, the extension is also nonsofic. A witness minimizing hierarchy length
therefore has sofic base `B_0`, and §§3–4 apply to that splitting.
∎
