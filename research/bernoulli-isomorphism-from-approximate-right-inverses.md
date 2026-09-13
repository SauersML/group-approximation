---
rg: 2
id: bernoulli-isomorphism-from-approximate-right-inverses
kind: claim
title: Two Bernoulli shifts that factor onto each other are isomorphic when every endomorphism of each has approximate right inverses among its endomorphisms
distinct_from:
  iid-density-iff-collapse-and-endomorphism-density: that proves density of generating i.i.d. partitions is collapse plus density of automorphisms among endomorphisms; this proves that a weaker property, approximate right inverses by endomorphisms, already produces the isomorphism.
  iid-generators-not-dense-at-positive-rokhlin-supremum: that proves factor joinings are not dense in the space of joinings at positive supremum; this runs the category argument inside the closures of the factor joinings of both directions, and shows that property fails at positive supremum.
  bernoulli-infinite-power-iff-approximate-half-absorption: that characterizes total collapse by approximately positioned half-splittings; this derives an isomorphism between two given shifts from an approximate section property of each shift separately.
---

**ESTABLISHED (unreviewed)** by [[bernoulli-isomorphism-from-approximate-right-inverses-proof]].

**Setting.** `G` is countably infinite. Notation of `iid-density-iff-collapse-and-endomorphism-density`:
`X_κ = (K^G, κ^G)`, `Fac_G`, `End_G`, `Aut_G`, and `d(φ, ψ) = µ{x : φ(x)(1_G) ≠ ψ(x)(1_G)}` for maps into a
Bernoulli shift. `J(X_λ, X_κ)` is the compact metrizable space of `G`-invariant probability measures on
`L^G × K^G` with marginals `λ^G` and `κ^G`. For `φ ∈ Fac_G(X_λ, X_κ)`, `graph(φ)` is the law of `(l, φ(l))`, and
the **transposed graph** of `ψ ∈ Fac_G(X_κ, X_λ)` is the law of `(ψ(k), k)`.

**Definition.** `X` has **approximate right inverses** (ARI) if for every `φ ∈ End_G(X)` and `ε > 0` there is
`ζ ∈ End_G(X)` with `d(φ ∘ ζ, id) < ε`. The topology of `d` is intrinsic (item 2 of the node above), so ARI is an
isomorphism invariant.

1. **Joining form.** `X_λ` has ARI iff every endomorphism graph is a weak* limit of transposed endomorphism
   graphs. Equivalently, the weak* closure of the endomorphism graphs in `J(X_λ, X_λ)` is invariant under
   transposition.
2. **Transfer.** Suppose `X_κ` has ARI and `Fac_G(X_κ, X_λ) ≠ ∅`. Then every `φ ∈ Fac_G(X_λ, X_κ)` has approximate
   right inverses `ψ ∈ Fac_G(X_κ, X_λ)`, with `d(φ ∘ ψ, id) < ε`. So every factor joining from `X_λ` to `X_κ` is a
   weak* limit of factor joinings from `X_κ` to `X_λ`.
3. **Theorem.** Suppose `X_κ` and `X_λ` both have ARI, and there are factor maps in both directions. Then
   `X_κ ≅ X_λ`. More precisely:
   - let `A ⊆ J(X_λ, X_κ)` be the joinings in which the `L`-coordinates determine the `K`-coordinates, and `B`
     those in which the `K`-coordinates determine the `L`-coordinates;
   - put `Y = cl(A) ∩ cl(B)`.

   Then `A ∩ B`, which is the set of graphs of isomorphisms, is a dense `G_δ` subset of `Y`.
4. **Place among the other conditions.** DENSE(`X`) implies ARI(`X`): take `ζ = T`. So, when
   `Fac_G(X_κ, X_λ) ≠ ∅`, density of generating partitions in `Ind_λ(X_κ)` implies ARI(`X_λ`).
5. **Positive supremum.** If `G` is nonamenable and `h^Rok_sup(G) > 0` (`∞` allowed), ARI fails for every
   finite-base Bernoulli shift with positive base entropy.
6. **Zero supremum.** Suppose `h^Rok_sup(G) = 0`.
   - If ARI holds for two finite-base Bernoulli shifts of different base entropy, they are isomorphic, and
     `D(G) ≠ {0}`.
   - If ARI holds for every finite-base Bernoulli shift, all finite-base Bernoulli shifts over `G` are isomorphic.

**Reading.**
- The perturbation lemma needed for collapse at zero supremum is weaker than partition-metric exactification.
  What is needed is approximate right inverses by endomorphisms, one shift at a time. The endomorphism `ζ` need not
  be invertible or close to anything; only `φ ∘ ζ` must be close to the identity. In words: every endomorphism
  has approximate equivariant sections that are themselves endomorphisms.
- Unlike DENSE, ARI takes no isomorphism as input. The two shifts each satisfy it separately, and the isomorphism
  comes out.
- ARI at zero supremum is posed as `zero-supremum-endomorphisms-have-approximate-right-inverses`.
- The category argument has to run in `Y`, not in the space of all (ergodic) joinings. On a nonamenable group with a
  proper finite-index normal subgroup `H`, one can average over `G/H` the graphs of coset-dependent right
  translations. That gives an ergodic self-joining of `X_λ` with a finite factor. Such a self-joining is not weakly
  contained in the Bernoulli shift, while every weak* limit of graphs is. So factor joinings are not dense among
  ergodic joinings there, at every supremum. This remark is a sketch and is not part of items 1–6.

**Model tests.**
- **`Z`, supremum `∞`.** ARI holds for Bernoulli shifts. Section 1 of arXiv:1804.05269v3 quotes the residual factor
  theorem of Burton–Keane–Serafin (2000): for a free ergodic `Z ↷ (A^Z, µ)` with entropy `H(L, λ)`, "within the space
  of ergodic joinings of µ with λ^Z, the set of joinings that come from graphs of factor maps ... is a dense G_δ set
  in the weak*-topology". Apply it with `µ = λ^Z` to the ergodic joining `law(φ(y), y)`, then use item 1 after
  transposing. Different base entropies are not isomorphic over `Z`, and the theorem is consistent with that:
  factor maps exist in one direction only.
- **`F_2`, supremum `∞`.** Item 5 applies. Bowen's Proposition 9.4 in arXiv:1804.05269v3 is a visible instance: a
  factor joining through the Ornstein–Weiss map has a neighbourhood without factor joinings the other way.
- **Without factor maps both ways** the theorem says nothing, as over `Z` with different entropies.

**Novelty (bounded).** A category argument restricted to the closures of both factor-joining sets was not found in
this graph, whose only joining-space node is the positive-supremum obstruction, or in Sections 1, 9 and 10 of
arXiv:1804.05269. No wider search was made.
