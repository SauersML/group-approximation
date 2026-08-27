# Gao–Kunnawalkam Elayavalli–Patchell, arXiv:2401.04945v3 — source-verified statement record

D. Gao, S. Kunnawalkam Elayavalli, G. Patchell, *Soficity for group actions
on sets and applications*, arXiv:2401.04945; published as
*Res. Math. Sci.* **12** (2025), 48, DOI `10.1007/s40687-025-00526-6`.

Provenance of this record: the arXiv listing gives v1 2024-01-10, v2
2024-01-20, v3 2025-08-27 ("final, published version"). The statements below
were read on **2026-08-17** from the **v3 PDF itself**, pages 4, 7, 8, 14 and
15, rendered page by page — not from a text summariser and not from the arXiv
HTML build. They are transcribed verbatim, with the paper's own numbering.
The Springer copy of record is behind an authorisation redirect and was not
read; the arXiv v3 numbering is the numbering cited in Kun–Thom and in this
graph, and it is what the DOI landing page's own metadata matches.

**Trust surface.** This is a refereed journal article, not a preprint — the
strongest external surface this graph carries. What it does *not* carry is
any statement about the existence of a non-sofic action; the paper says the
opposite (see "The sentence this graph's lane overturns", below). Nothing
here was formalised.

**One discard.** An automated HTML fetch of the same paper on the same day
returned, alongside correct material, a "footnote" reading *"it remains a
puzzling question whether G/N is sofic for G sofic and N is a finite normal
subgroup"*. No such sentence appears on the pages read, and as stated it is
not a question at all. It is recorded here only so that a later reader who
finds it in a chat log knows it was checked and rejected.

---

## Standing setting (Proposition 2.9, verbatim preamble)

> **Proposition 2.9.** Let `G` be a countable discrete group, `X` be a
> countable discrete set, `α : G ↷ X` be an action. The following are
> equivalent,
>
> 1. `α` is sofic;
> 2. There exists a free ultrafilter `𝒰` on `ℕ`, a group homomorphism
>    `φ : G → ∏_𝒰(S_n, d)`, and a map `π : X → 𝕏_𝒰` s.t.
>    `𝕊_𝒰(φ(g))(π(x)) = π(α(g)x)` for all `x ∈ X`, `g ∈ G` and s.t.
>    `d_𝒰(π(x), π(y)) = 1` for all `x ≠ y ∈ X`.

So the theory is about **countable** groups acting on **countable** sets, and
item (2) makes it visible that soficity of an action depends only on the
isomorphism class of the `G`-set: a `G`-equivariant bijection `X → Y`
transports `π` and leaves `φ` untouched.

## Definition 2.1(5) (finitary definition)

> `α` is called sofic if for all finite subsets `F ⊆ G`, `E ⊆ X`, and
> `ε > 0`, there exists a finite set `A` and a map `φ : G → Sym(A)` which is
> unital, `(F,ε)`-multiplicative, and an `(F,E,ε)`-orbit approximation of `α`.

(Transcribed from the HTML fetch and consistent with the definition used
throughout the proofs on pages 7–9; the finitary form is not load-bearing for
this graph's lane, which uses only Theorem 2.14, Proposition 2.15 and
Proposition 2.16.)

## Theorem 2.14 (verbatim, p. 7)

> **Theorem 2.14.** Let `G` be a sofic group, `N ≤ G` be a locally finite
> subgroup of `G`. Then the left multiplication action `α : G ↷ G/N` is
> sofic.

## Proposition 2.15 (verbatim, pp. 7–8)

> We record here some easy observations:
>
> **Proposition 2.15.**
>
> 1. *If `α : G ↷ X` is the composition of a quotient map `q : G → H` and a
>    sofic action `β : H ↷ X`, then `α` is sofic;*
> 2. *If `α : G ↷ X` is sofic, then the restriction of `α` to each of its
>    orbits is sofic;*
> 3. *If `α : G ↷ X` is sofic and `H` is a subgroup of `G`, then `α|_H` is
>    sofic;*
> 4. *If `G_1 ⊆ G_2 ⊆ ⋯` is an increasing sequence of subgroups of `G` whose
>    union is `G`, and `α : G ↷ X` restricted to each `G_i` is sofic, then
>    `α` is sofic.*

## Proposition 2.16 (verbatim, p. 8)

> The converse of item 2 of the above proposition is also true, which
> naturally reduces the study of sofic actions to transitive ones:
>
> **Proposition 2.16.** *If the restriction of `α : G ↷ X` to each of its
> orbits is sofic, then `α` is sofic.*

## The sentence this graph's lane overturns (verbatim, p. 8)

> Combining Theorem 2.14 and Proposition 2.16, we see that all actions by
> sofic groups with locally finite stabilizers are sofic. We are unable to
> settle the more general case of amenable stabilizers.
>
> It is still open whether all actions by sofic groups are sofic. However,
> this does hold for amenable groups and free groups.

Followed by **Theorem 2.17** (any action of an amenable group is sofic),
**Remark 2.18** (any action of any group on a finite set is sofic) and
**Theorem 2.19** (any action of a free group is sofic).

That paragraph is the state of knowledge at publication (August 2025). It was
overturned in August 2026 by Kun–Thom, see
`research/artifacts/kun-thom-2608-06222-verified.md`; the fact now lives in
this graph as `coordinate-action-not-sofic`.

## Theorem 3.6 (verbatim, p. 11)

> **Theorem 3.6.** Let `G, H` be sofic groups, `α : H ↷ X` be a sofic action.
> Then the generalized wreath product `G ≀_α H` is sofic.

(The graph's `coordinate-action-not-sofic-proof` cites this as "Theorem A =
3.6"; the numbering here is the v3 numbering.)

## Theorem 3.8 (verbatim, p. 14)

> **Theorem 3.8.** Let `(M,τ)` be a Connes-embeddable tracial von Neumann
> algebra, `H` be a hyperlinear group, `α : H ↷ X` be a sofic action. Then
> the generalized wreath product `M ≀_α H` is Connes-embeddable. In
> particular, if `G, H` are hyperlinear groups and `α : H ↷ X` is a sofic
> action, then the generalized wreath product `G ≀_α H` is hyperlinear.

## Section 4, verbatim in full (pp. 14–15)

> ### 4. Concluding remarks and open questions
>
> We document the following Proposition which places an aspect of our work in
> the context of Elek-Lippner's work [EL10b] defining soficity for equivalence
> relations and of Paunescu [Păl1]. We omit the proof because it is
> substantially similar to the arguments in the previous section. It is open
> whether the converse of the statement below holds.
>
> **Proposition 4.1.** Let `(Ω,μ)` be a standard probability space, `G` be a
> sofic group, `α : G ↷ X` be a sofic action. Then the induced generalized
> Bernoulli shift `G ↷ (Ω^X, μ^{⊗|X|})` is sofic in the sense of [Păl1].
>
> We ask the following two natural questions on the permanence of sofic
> actions which we are currently unable to answer:
>
> **Question 4.2.** Suppose we have actions `α_i : G_i ↷ X` which commute
> with each other and where `i` ranges over a countable index set. Then the
> actions naturally give rise to an action `α : ⊕_i G_i ↷ X`. `α` is sofic
> iff all `α_i` are sofic?
>
> **Question 4.3.** Suppose we have actions `α_i : G_i ↷ X` where `i` ranges
> over a countable index set. Then the actions naturally give rise to an
> action `α : ∗_i G_i ↷ X`. `α` is sofic iff all `α_i` are sofic?
>
> The forward directions of both conjectures follow from item 3 of
> Proposition 2.15. By item 4 of Proposition 2.15, it suffices to consider the
> case where there are only two groups `G_1` and `G_2`. We document one more
> natural question which is nothing but the converse of Theorem 3.6.
>
> **Question 4.4.** Let `G, H` be nontrivial countable groups,
> `α : H ↷ X` be an action. Then the generalized wreath product `G ≀_α H` is
> sofic iff `G` and `H` are sofic and the action `α` is sofic?
>
> A positive answer to Question 4.2 implies a positive answer to the above.
> Indeed, let `Γ` be a sofic group. Then the left multiplication
> `α_1 : Γ ↷ Γ` is sofic by Theorem 2.14. The right multiplication action
> `α_2 : Γ ↷ Γ`, `α_2(γ)η = ηγ^{-1}` is isomorphic to the left multiplication
> action, so as such is also sofic. `α_1` and `α_2` clearly commute, so the
> combined action `α : Γ ⊕ Γ ↷ Γ` is sofic assuming a positive answer to
> Question 4.2. Let `Δ : Γ → Γ ⊕ Γ` be the diagonal embedding, then by item 3
> of Proposition 2.15, `α ∘ Δ` is sofic. One can easily verify that `α ∘ Δ`
> is the conjugation action of `Γ` on itself. That is, the conjugation action
> of any sofic group on itself is sofic, assuming Question 4.2 has a positive
> answer.
>
> Now, if `G ≀_α H` is sofic, then the above applies to it, so its conjugation
> action on itself is sofic. By item 3 of Proposition 2.15, we have the
> conjugation action `β : H ↷ G ≀_α H` is sofic. Now, as `G` is nontrivial,
> we may fix `g ∈ G \ {1_G}`. For any `x ∈ X`, let `g_x ∈ G^{⊕X} ⊆ G ≀_α H`
> be the element that, as a function from `X` to `G`, takes value `1_G` at all
> elements of `X` except `x` and takes value `g` at `x`. Let the orbit of
> `g_x` under `β` be `𝒪(g_x)` and the orbit of `x` under `α` be `𝒪(x)`. Since
> `β(h)g_x = h g_x h^{-1} = g_{α(h)x}` and furthermore that `g_x ≠ g_y`
> whenever `x ≠ y` as `g ≠ 1_G`, we easily see that the map
> `𝒪(x) ∋ y ↦ g_y ∈ 𝒪(g_x)` is a bijection that identifies `β` restricted to
> `𝒪(g_x)` and `α` restricted to `𝒪(x)`. As `β` is sofic, this implies, via
> item 2 of Proposition 2.15, that `α` restricted to `𝒪(x)` is sofic. Since
> `x ∈ X` is arbitrary, `α` restricted to each of its orbits is sofic, whence
> `α` is sofic by Proposition 2.16.

## Why the last two paragraphs matter to this graph

They are the reason the counterexample in
`nonsofic-orbit-forces-commuting-counterexample` is short. The authors
already use the exact mechanism — take two commuting actions on a
homogeneous space, restrict the combined action to the **diagonal** subgroup,
read the answer off one orbit — with `Γ ≅ (Γ × Γ)/ΔΓ` and the two
multiplication actions. The counterexample replaces `ΔΓ` by `ΔH` for a
subgroup `H ≤ G`, which turns the diagonal orbit from a conjugacy class into
`G/H`. Nothing else changes.

What the authors could not do in 2025 was supply a sofic `G` with a nonsofic
`G ↷ G/H`, because — as the page-8 paragraph says in their own words — no
nonsofic action of a sofic group was known to exist. That, and only that, is
what Kun–Thom added in August 2026.
