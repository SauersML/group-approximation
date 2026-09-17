---
rg: 2
id: f-ea-calculus-certificates-force-f-prime-to-act-trivially
kind: claim
title: "Every action certified extensively amenable by the Juschenko–Matte Bon–Monod–de la Salle calculus from recurrent actions and F-free groups makes the commutator subgroup of every copy of F act trivially, so the calculus never reaches a nonabelian F-set and never feeds a twisted embedding for a group containing F"
distinct_from:
  f-functor-cocycles-need-an-exotic-recurrent-action: that kills the twisted-embedding step on unfaithful actions and on recurrent actions only; this proves that every action produced by the whole extensive-amenability calculus (extension principle, functor extensions, images, pullbacks, local-to-global) is unfaithful on F′, which that claim listed as not covered.
  f-free-groups-are-closed-under-recurrent-extensions: that is a group-level closure theorem (extensions, unions, recurrent extensions with F-free stabilizers); this is an action-level closure theorem whose stabilizer inputs may contain F.
  thompson-f-recurrent-f-sets-factor-through-the-abelianization: that is the base case, recurrent F-sets; this propagates it through every permanence operation of extensive amenability.
  thompson-f-amenable-iff-dyadic-action-extensively-amenable: that shows extensive amenability of the dyadic action is equivalent to the flagship; this shows that extensive amenability cannot be certified algebraically for the dyadic action or any other nonabelian F-set.
  thompson-f-dyadic-ea-witnesses-need-tower-size: that bounds the size of explicit witnesses; this excludes the structural certificates, whatever their size.
---

**ESTABLISHED** by `f-ea-calculus-certificates-force-f-prime-trivial-proof` (not yet refereed; no
priority claimed). It depends on the unrefereed `thompson-f-recurrent-f-sets-factor-through-the-abelianization`.

**Notation.** `F` is Thompson's group and `F′` its commutator subgroup. A *copy of `F`* in a group `G`
is a subgroup `Φ ≤ G` with an isomorphism `ψ : F → Φ`; then `Φ′ = ψ(F′)`. `𝓕` is the class of groups with
no copy of `F`. A pair `(G, X)` is a group with an action on a set. Say `(G, X)` has **property P** if
for every copy `Φ` of `F` in `G`, `Φ′` fixes every point of `X`. Equivalently, every copy of `F` acts on
every orbit through `F/F′ ≅ Z²`.

**The calculus.** `𝓟` is the smallest class of pairs that contains the bases and is closed under the
operations below.
- (B1) *Recurrent actions*, in the sense of JMBMdlS (paragraph before Theorem `T: recurrent`): for every symmetric finitely supported
  probability measure `μ` on `G` and every `x_0 ∈ X`, the induced walk on `G·x_0` is recurrent.
- (B2) *Every action of a group in `𝓕`.*
- (O1) *Pullback.* `(G, X) ∈ 𝓟` and a homomorphism `φ : K → G` give `(K, X)`, with `K` acting through `φ`.
  This includes restriction to subgroups.
- (O2) *Invariant subsets.* `(G, Z)` for a `G`-invariant `Z ⊆ X`.
- (O3) *Images.* `(G, Y)` for a surjective `G`-map `X → Y`.
- (O4) *Local-to-global.* If `(H, Y) ∈ 𝓟` for every finitely generated `H ≤ G` and every `H`-orbit
  `Y ⊆ X`, then `(G, X) ∈ 𝓟`. This includes directed unions and disjoint unions.
- (O5) *Extension principle.* For a `G`-map `q : X → Y`, if `(G, Y) ∈ 𝓟` and `(G_y, q^{-1}(y)) ∈ 𝓟` for
  every `y`, then `(G, X) ∈ 𝓟`.
- (O6) *Functor extension.* For a functor `𝔉 : 𝐈 → 𝐆𝐫𝐩` (finite sets with injections), extended to all
  sets by direct limits, with `𝔉(X) ∈ 𝓕`: `(G, X) ∈ 𝓟` gives `(𝔉(X) ⋊ G, 𝔉(X)) ∈ 𝓟`, with the affine
  action `(c, g)·d = c·𝔉(g)(d)`.

**Theorem.** Every `(G, X) ∈ 𝓟` has property P.

**Corollaries.**
1. *No nonabelian F-set.* If `(G, X) ∈ 𝓟` and `θ : F → G` is injective, then `F ↷ X` (through `θ`)
   factors through `F/F′`. In particular the dyadic action `F ↷ D`, every point orbit, and every exotic
   `F`-set lie outside `𝓟`, and no group containing `F` has a faithful action in `𝓟`.
2. *Twisted embeddings die at the kernel.* Let `(G, X) ∈ 𝓟` with `F ≤ G`, let `𝔉` be a functor with
   `𝔉(X) ∈ 𝓕`, and let `c : G → 𝔉(X)` be a cocycle, `c_{gh} = c_g·g(c_h)`. Then `F′ ⊆ ker c`. So
   `ker c` contains a copy of `F` (for example `F(1/4, 3/4)`), and the amenability input "`ker c` is
   amenable" of JMBMdlS Corollary `prop:functor:amenable:intro` already contains amenability of `F`.

**Why these are the known tools (JMBMdlS, arXiv:1503.04977, source read 2026-09-17).**
- Lemma 2.1: "Every action of an amenable group is extensively amenable". With `G` amenable, (B2)
  consists of extensively amenable actions.
- Theorem `T: recurrent`, "Theorem 1.2 in [JNS]": "Recurrent actions are extensively amenable."
  Lemma `L: recurrence inverted orbit`: for transitive actions of finitely generated groups, recurrence
  holds "if and only if $\frac 1n \mathbb E|\mathbf O_n|\to 0$". So the sublinear mean inverted-orbit
  criterion is (B1).
- Lemma 2.2 (`lemma=JSbis`), (i)⇔(ii): "For every finitely generated subgroup $H$ of $G$ and every
  $H$-orbit $Y \subset X$, the action of $H$ on $Y$ is extensively amenable." This gives (O2) and (O4);
  (O1) holds because the same mean is invariant under the image of `K`.
- Proposition 2.4 (`P: extension`): "If $G \acts Y$ is extensively amenable and if $G_y \acts
  q^{-1}(y)$ is extensively amenable for every $y \in Y$, then $G \acts X$ is extensively amenable. The
  converse holds if $q$ is surjective." This gives (O5) and (O3).
- Theorem 1.3 (`prop:functor:intro`): "If the action $G\acts X$ is extensively amenable, then the action
  $F(X) \rtimes G\acts F(X)$ is amenable. Moreover it is extensively amenable." Here `F` is a functor into
  amenable groups. This gives (O6).
- Corollary 2.6 (`lemma=wreath product`), products `G × H ↷ X × Y` and `H^X ⋊ G ↷ X × Y`, is derived there
  from Proposition 2.4. It is (O5) applied to pullbacks, so it is inside the calculus.

So the subclass of `𝓟` built from recurrent actions, actions of amenable groups in `𝓕`, and functors
into amenable groups in `𝓕` consists of extensively amenable actions. It contains every certificate
assembled from these results.

**What is killed.** Every proof that `F`, or any group containing `F`, is amenable of the form
"certify an extensively amenable action by the JMBMdlS calculus from recurrent actions and from actions
of known amenable groups with no copy of `F`, then apply a twisted embedding or a JNdlS germ cocycle with
amenable kernel".
- *Invariant:* property P, "the commutator subgroup of every copy of `F` fixes every point".
- *Where every member dies:* at the kernel step. By Corollary 2, `ker c ⊇ F′`, which contains `F`.
  Independently, the prerequisite `thompson-f-dyadic-action-is-extensively-amenable` of the route
  `thompson-f-amenable-via-dyadic-extensive-amenability` has no certificate in `𝓟` (Corollary 1).
- *Why the operations cannot escape:* each operation either keeps the copies of `F` of its inputs
  (pullback, images, local-to-global), or its stabilizer inputs contain the rigid copies `F[a,b]` inside
  `Φ′` and so already make `Φ′` act trivially on fibres (extension principle), or a nontrivial action of
  `Φ′` would embed `F′` in the functor value (functor extension).

**What survives.** Honest scope:
- *Analytic certificates of extensive amenability* that are not recurrence: the rare-event criterion of
  JMBMdlS Proposition `prop:inverted_orbit`, item (ii), "for every $\varepsilon>0$ we have $\mathbb
  P(|\mathbf O_n|< \varepsilon n) > e^{-\varepsilon n}$ for infinitely many $n$'s", on a nonabelian
  `F`-set. For `F ↷ D` this is `f-dyadic-inverted-orbit-is-subballistic-on-rare-events`, and it is
  equivalent to the flagship.
- *Inputs outside `𝓕`:* actions of an amenable group that contains `F`, or functors with a copy of `F` in
  their values. Either already contains amenability of `F`.
- *The converse half* of Theorem 1.3 ("amenable affine action and tight functor gives extensive
  amenability") takes amenability as input, so it is excluded.

So the paradigm reduces to one statement: a direct, non-algebraic proof of extensive amenability of a
nonabelian `F`-set, which by `thompson-f-amenable-iff-dyadic-action-extensively-amenable` is the flagship.

Proof route: `f-ea-calculus-certificates-force-f-prime-trivial-proof`.
