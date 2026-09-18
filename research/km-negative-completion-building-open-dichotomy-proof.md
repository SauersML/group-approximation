---
rg: 2
id: km-negative-completion-building-open-dichotomy-proof
kind: route
title: A Chevalley involution swaps the two halves of the twin building and carries the positive building-open results to the negative completion
target: km-negative-completion-building-open-dichotomy
requires:
  - km-building-open-subgroups-have-infinite-bi-index
  - km-building-open-subgroups-have-infinite-ht-orbits
---

**Source pins.** De Medts--Gramlich--Horn, *Iwasawa decompositions of split Kac--Moody
groups*, arXiv:0709.3466v2, TeX `iwasawa.tex`:
- **Definition, l.179--185.** A `σ`-twisted Chevalley involution is `θ ∈ Aut(G)` with
  "$\theta^2=\id$", "$U_\alpha^\theta=U_{-\alpha}$", and a local condition on
  `X_α = ⟨U_α, U_{−α}⟩`.
- **Proposition `chevalley-is-flip`, l.459.** "Any $\sigma$-twisted Chevalley involution
  $\theta$ of a group $G$ is a $BN$-flip." Its proof shows that `θ` stabilizes `T`, maps
  `B_+` to `B_-`, and acts trivially on `W = N/T`.
- **Lemma `chev-inv-existence`, l.468.** "Let $\F$ be a field with at least four elements,
  let $\sigma$ be an automorphism of $\F$ of order $1$ or $2$, let $G$ be a group with a
  $2$-spherical $\F$-locally split root group datum. Then $G$ admits a $\sigma$-twisted
  Chevalley involution."
  - The proof goes through the Abramenko--Mühlherr amalgam presentation, the same input as
    Lemma A of Attempt 6 on `fp-simple-kac-moody-lattices-are-highly-transitive`.

Take `σ = id` and let `θ` be the resulting involution.

**Step 1: an equivariant building isomorphism.** Define `φ : Λ/B_- → Λ/B_+` by
`φ(gB_-) = θ(g)B_+`. This is well defined and bijective, since `θ(B_-) = B_+` (from
`θ(B_+) = B_-` and `θ² = id`). It satisfies `φ(λc) = θ(λ)φ(c)`.

`φ` preserves Weyl distances. If `g^{-1}h ∈ B_- n B_-` with `nT = w`, then
`θ(g)^{-1}θ(h) ∈ B_+ θ(n) B_+`, and `θ(n)T = w` because `θ` acts trivially on `W`.

**Step 2: topologies and completions.** Let `F ⊂ X_-` be a finite set of chambers. Then
`g` fixes `F` pointwise if and only if `θ(g)` fixes `φ(F)` pointwise, so
`θ(Fix_Λ(F)) = Fix_Λ(φ(F))`. The pointwise fixators of finite sets of chambers form bases
at `1` for the building topologies. So `θ` is an isomorphism of topological groups
`(Λ, τ_-) → (Λ, τ_+)`, and a subgroup `M` is negatively building-open exactly when
`θ(M)` is positively building-open.

Conjugation by `φ` is an isomorphism of topological groups `Aut(X_-) → Aut(X_+)`, where
both carry the permutation topology on chambers. It sends the image of `λ` to the image of
`θ(λ)`. So it maps the closure `G_-` of the image of `Λ` onto the closure `G_+`, open
subgroups onto open subgroups, and closures onto closures.

**Step 3: transport.**
- `θ` preserves index and the number of double cosets, so (A−) follows from (A) applied to
  `θ(M)`.
- `Λ^† = ⟨U_α : α ∈ Φ⟩` is `θ`-stable because `θ` permutes the root groups. Hence
  `θ(Z_Λ(Λ^†)) = Z_Λ(Λ^†)`.
- So for `N ⊆ Z_Λ(Λ^†)`, `θ` induces an isomorphism `Λ/N → Λ/θ(N)` with
  `θ(N) ⊆ Z_Λ(Λ^†)`. It carries subgroups containing images of negatively open traces to
  subgroups containing images of positively open traces. That gives (A''−) from (A'').
- An action of `Λ/N` on `Ω` becomes an action of `Λ/θ(N)` when composed with this
  isomorphism. It keeps the transitivity degree, orbits and stabilizers, so (a)--(b') of
  the positive node transfer.
- (c) and (d) concern closures in the completion and openness there, which Step 2 carries
  across.
- For `S_q = Λ_q/Z(Λ_q)`: type `(2,4,6)` is irreducible, 2-spherical and infinite; the
  field is `F_q` with `q ≥ 4`; and `Z(Λ_q) ⊆ Z_Λ(Λ^†)`. So every hypothesis holds.
