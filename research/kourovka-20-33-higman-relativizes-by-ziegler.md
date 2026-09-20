---
rg: 2
id: kourovka-20-33-higman-relativizes-by-ziegler
kind: claim
title: Higman's embedding theorem relativizes as Kourovka 20.33 asks; the answer is yes, by Ziegler's generalized Higman embedding theorem
distinct_from:
  belyaev-associative-higman-theorem: that is the unrelativized Higman theorem for associative algebras; this is the oracle-relative Higman theorem for groups, with a universal f.g. group G_X for each oracle X.
artifacts:
  - research/artifacts/gq-bh-kourovka-scout-candidates-2026-09-19.md
---

**ESTABLISHED** as a literature answer. The key input is Ziegler's generalized Higman
embedding theorem, quoted below from its restatement in I. Scott, *On effective constructions
of existentially closed groups*, arXiv:2404.11524v1 (17 April 2024), §5.1–§5.2, pp. 14–16,
read at source. Ziegler's own paper was not read. The deduction (Lemmas 1 and 2 and the proof
of the Theorem) is a lane proof, not independently reviewed.

The Kourovka Notebook, arXiv:1401.0300v46 (1 September 2026), p. 152, still lists 20.33
among the unsolved problems, with no comment (read at source). No priority is claimed: the
observation that Ziegler's theorem answers 20.33 may well be known to experts.

## Statement

Kourovka 20.33 (A. Bauer; posed by J. Grochow), verbatim:

> Does Higman's Embedding Theorem relativize in the following way? Is it the case that for
> every subset X ⊆ ℕ, there is a finitely generated group G_X that has an X-computable
> presentation (that is, there is a finite generating set relative to which the set of
> relations is computably enumerable with an X oracle), and such that any finitely generated
> group has an X-computable presentation if and only if it can be embedded as a finitely
> generated subgroup of a quotient of a free product of finitely many copies of G_X by the
> normal closure of a finite subset?
> Higman's Embedding Theorem says that for computable X, one may take G_X = ℤ.

**Answer: yes.** For `X ⊆ ℕ` put `S = X ⊕ Xᶜ = {2n : n ∈ X} ∪ {2n+1 : n ∉ X}` and
`a_n = b^{-n} a b^{n}`. Let

- `H_S = ⟨a, b, t | [t, a_n] (n ∈ S)⟩`, and
- `G_X = H_S * ⟨z⟩`.

**Theorem.** `G_X` has an X-computable presentation (its relator set is even decidable in
`X`). A finitely generated group `Γ` has an X-computable presentation if and only if `Γ`
embeds as a finitely generated subgroup of `G_X^{*k}/⟨⟨R⟩⟩` for some `k ≥ 1` and some finite
`R ⊆ G_X^{*k}`.

## Inputs (Scott 2404.11524v1, read at source)

Notation: `W(G)` is the set of words on a finite generating tuple that are trivial in `G`,
and `≤_e` is enumeration reducibility (Definition 5.1.1).

- **Proposition 5.1.2**, second bullet: "Y is c.e. in X iff Y ≤e X ⊕ Xᶜ."
- **Proposition 5.1.9:** the enumeration degree of `W(G, ḡ)` "does not depend on the choice
  ḡ of generators of G".
- **Definition 5.2.1:** "We say F is a finitely presented extension of G, or F is finitely
  presented over G, if there is a finite tuple f̄ and a finite collection of words R(ḡ, f̄)
  such that F = ⟨ḡ, f̄ | W(G) ∪ R(ḡ, f̄)⟩ and ḡ generates a group isomorphic to G in F."
- **Theorem 5.2.2** (Generalised Higman's Embedding Theorem), attributed to Ziegler
  [Zie80, Theorem II.3.10]: "Let G and H be finitely generated groups. Then W(G) ≤e W(H) iff
  G embeds in a finitely presented extension F of H."

Only the forward direction of Theorem 5.2.2 is used.

## Lemma 1 (lane proof): `W(H_S) ≡_e S`

- **`S ≤_e W(H_S)`.**
  - In `K = F(a, b)`, the elements `a_n` (`n ∈ ℤ`) freely generate the kernel of
    `K → ℤ`, `a ↦ 0`, `b ↦ 1` (Reidemeister–Schreier).
  - So `A_S = ⟨a_n : n ∈ S⟩` is free on `{a_n : n ∈ S}`, and `a_m ∈ A_S ⟺ m ∈ S`.
  - `H_S` is the HNN extension of `K` with stable letter `t` acting as the identity on
    `A_S`.
  - If `m ∉ S`, the word `t^{-1} a_m^{-1} t a_m` contains no pinch `t^{-1} u t` with
    `u ∈ A_S`, so it is nontrivial by Britton's lemma. If `m ∈ S`, it is a defining relator.
  - So `m ∈ S ⟺ [t, a_m] ∈ W(H_S)`. The map `m ↦ [t, a_m]` is computable, and a computable
    many-one reduction is an enumeration reduction.
- **`W(H_S) ≤_e S`.** A word `w` lies in `W(H_S)` iff for some finite `D ⊆ S`, `w` is freely
  equal to a product of conjugates of `[t, a_n]^{±1}` with `n ∈ D`. For fixed `(w, D)` this is
  a c.e. condition, so it defines an enumeration operator.

Ziegler's theorem quoted as Scott's Theorem 5.1.10 ([Zie76]) gives some f.g. `H` with
`W(H) ≡_e S` directly; Lemma 1 just makes the group explicit.

**Consequence.** `W(G_X) ≤_e S`. A word in the free product is trivial iff it reduces to the
empty word by deleting syllables trivial in their factor, which is enumerable from positive
information about `W(H_S)`, and `W(ℤ)` is computable. By Proposition 5.1.2, `W(G_X)` is c.e.
in `X`. The displayed relator set `{[t, a_n] : n ∈ S}` is decidable in `X`.

## Lemma 2 (lane proof): extensions over `H_S` embed in quotients of `G_X^{*k}`

Let `F = ⟨ḡ, f_1, …, f_k | W(H_S) ∪ R⟩` be finitely presented over `H_S`, with `k ≥ 1`
(a dummy generator `f_1` with relator `f_1` allows this). Write `H^{(i)}` and `z_i` for the
factors of the `i`-th copy of `G_X`. Then

- `G_X^{*k} = A * B`, with `A = H^{(1)} * ⟨z_1⟩ * ⋯ * ⟨z_k⟩` and `B = H^{(2)} * ⋯ * H^{(k)}`;
- `A ≅ H_S * F(f_1, …, f_k)`, via `ḡ ↦ H^{(1)}` and `f_i ↦ z_i`.

Let `R'` be the image of `R` in `A`. For `R' ⊆ A`,

`(A * B)/⟨⟨R'⟩⟩ ≅ (A/⟨⟨R'⟩⟩_A) * B`

(universal property of free products). `A/⟨⟨R'⟩⟩_A ≅ F`, so `F` embeds in `G_X^{*k}/⟨⟨R'⟩⟩`.

## Proof of the Theorem (lane proof)

**(⇒)**
1. Let `Γ` be f.g. with an X-computable presentation `⟨ȳ | P⟩`, with `P` c.e. in `X`.
2. `W(Γ, ȳ)` is the normal closure of `P` in the free group, so it is c.e. in `X`. By
   Proposition 5.1.2, `W(Γ) ≤_e S`.
3. By Lemma 1 and transitivity, `W(Γ) ≤_e W(H_S)`.
4. By Theorem 5.2.2, `Γ` embeds in some `F` finitely presented over `H_S`.
5. By Lemma 2, `F` embeds in `G_X^{*k}/⟨⟨R'⟩⟩` with `R'` finite. The image of `Γ` is a
   finitely generated subgroup.

**(⇐)**
1. Let `Q = G_X^{*m}/⟨⟨R⟩⟩` with `R` finite, and let `Γ = ⟨u_1, …, u_r⟩ ≤ Q`.
2. `W(Q)` is the normal closure in the free group of `R` together with the copies of
   `W(G_X)`, so `W(Q) ≤_e W(G_X) ≤_e S`. Hence `W(Q)` is c.e. in `X`.
3. `W(Γ, ȳ) = {v : v(u_1, …, u_r) ∈ W(Q)}` is then c.e. in `X`.
4. So `⟨ȳ | W(Γ, ȳ)⟩` is an X-computable presentation of `Γ`. ∎

## Remarks

- **Why the answer is clean.** "c.e. in X" is enumeration reducibility to the total set
  `X ⊕ Xᶜ` (Proposition 5.1.2). Ziegler's theorem states Higman's theorem relative to an
  arbitrary enumeration degree, and 20.33 is its restriction to total degrees.
- **Computable X.** Then `S` is computable and `H_S` is recursively presented, so Higman's
  theorem also lets one take `G_X = ℤ`, as the problem notes. The construction above is
  uniform in `X`.
- **Decidable relator sets.** If "X-computable presentation" is read as "a relator set
  decidable in X", the class of groups is the same: Scott (p. 18, Remark) records "a
  relativisation of Craig's trick" to this effect.

## Credit

- M. Ziegler, *Algebraisch abgeschlossene Gruppen*, in *Word Problems II* (Adian, Boone,
  Higman, eds.), Stud. Logic Found. Math. 95, North-Holland, 1980, pp. 449–576 (Theorem
  II.3.10, as cited by Scott; not read at source).
- M. Ziegler, 1976 (Scott's [Zie76]), for Theorem 5.1.10.
- O. V. Belegradek, *Higman's embedding theorem in a general setting and its application to
  existentially closed algebras*, Notre Dame J. Formal Logic 37 (1996), no. 4, 613–624,
  proves the generalized Higman theorem for groups among other quasivarieties (abstract
  read only).
- I. Scott, arXiv:2404.11524v1, for the modern statement used here.
