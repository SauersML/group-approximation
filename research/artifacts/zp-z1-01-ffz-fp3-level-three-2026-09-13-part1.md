# Problem 1.1 at level three: the Fournier-Facio–Zaremsky source, verbatim (part 1)

Lane z1-01-ffz-fp3, 2026-09-13. Zaremsky Problem 1.1, positive side, `FP_3` / `F_3` level.

## Provenance

- Francesco Fournier-Facio and Matthew C. B. Zaremsky, *Finiteness properties and Higman's rope trick*,
  arXiv:2607.21727v1, submitted Thu 23 Jul 2026 18:22:06 UTC, 8 pages (arXiv abstract page).
- Source used: the arXiv e-print archive `https://arxiv.org/e-print/2607.21727`, downloaded 2026-09-13,
  gzip tar, SHA-256 `d732547b74b2c4b2169e6876159323f9b5bb072341d083419b4c9b2c3df54dd0`, containing
  `rope_trick.tex` (366 lines, SHA-256 `81f4396a232a70c5d172f2bde6c24c4ebba25ea7294c80859fb84a37c7bc1612`)
  and `rope_trick.bbl`.
- Numbering. `theorem`, `lemma`, `question`, `definition` and `remark` share one counter numbered within
  sections; Theorems A and B use a separate lettered counter. So the introduction has Theorem 1.1
  (Higman), Theorem 1.2 (Leary), Question 1.3, Question 1.4, Definition 1.5, Lemma 1.6; Section 2 has
  Lemma 2.1 and Remark 2.2; Section 3 has Remark 3.1, Lemmas 3.2–3.4 and Remark 3.5.

Quotations below are copied from the TeX source with macros expanded by hand
(`\FP` = `FP`, `\F` = `F`, `\higig` = `Hig_ι(G)`).

## Questions 1.3 and 1.4 (Introduction)

> **Question 1.3.** Does every finitely generated recursively presented group embed in a group of type F_3?
> In a group of type F_∞?

> **Question 1.4.** Does every finitely generated group embed in a group of type FP_3? In a group of type
> FP_∞?

The source cites these as open: "A fundamental open question (see [Bes, Q 8.7], [Kourovka, 21.146],
[Zaremsky list, 1.1], and the comments to [Agol]) is whether the theorems of Higman and Leary admit
higher-dimensional analogues." It adds: "Question 1.4 is open even if one replaces type FP_n with the
more permissive type FP_n(Q)."

## Theorem A and Lemma 2.1

> **Theorem A.** Let n ∈ N ∪ {∞}. If every finitely generated recursively presented group embeds into a
> recursively presented group of type FP_n, then every finitely presented group embeds into a group of
> type F_n.

> **Lemma 2.1.** If a finitely presented group G is of type FP_n, then it is of type F_n.

Proof of Theorem A, from the source: "we may assume that G is a universal finitely presented group. Let
ι: G → H be an embedding into a recursively presented group H of type FP_n. By the Higman embedding
theorem, there is an embedding ȷ: H → G. ... The composition ȷι is a self-embedding of G; let E be the
corresponding ascending HNN extension, with stable letter t. Being an ascending HNN extension of G, which
is finitely presented, E is finitely presented." Then E is shown to be an ascending HNN extension of
ȷ(H) ≅ H by [GMSW01, Lemma 3.1] (Geoghegan–Mihalik–Sapir–Wise, Bull. LMS 33 (2001)), checking
t ȷ(H) t^{-1} ⊆ ȷ(H), E = ⟨ȷ(H), t⟩ and t^n ∉ ȷ(H) for n ≠ 0. "Since H is of type FP_n, by
[Bie81, Proposition 2.12], its ascending HNN extension E is also of type FP_n. Thus E, being both finitely
presented and of type FP_n, is of type F_n by Lemma 2.1."

Observation (this lane). The proof only uses one embedding of the universal group `U` into a
recursively presented `FP_n` group. Conversely such an embedding implies the theorem's hypothesis,
because every finitely generated recursively presented group embeds in a finitely presented group
(Higman) and hence in `U`.

## The rope trick: Definition 1.5 and Lemma 1.6

> **Definition 1.5 (The group Hig_ι(G)).** Let G be a finitely generated group, written as F/R, where F is
> a finitely generated free group. Let L = F_1 *_R F_2 be the double, and let π: L → G be the surjection
> obtained by killing F_2. Let ι: L → P be an embedding into a finitely generated group.
> We denote by Hig_ι(G) the HNN extension with vertex group P × G and edge group L, conjugating the
> embeddings ι × 1 and ι × π.

> **Lemma 1.6 (Higman's rope trick).** Let G be a finitely generated group, written as F/R, where F is a
> finitely generated free group. Let Hig_ι(G) be as in Definition 1.5, and suppose that P is finitely
> presented. Then Hig_ι(G) is finitely presented.

Proof sketch in the source: "Given r ∈ R < L, the element (r, 1) is conjugate under the stable letter to
(r, r) ∈ P × F/R (considering r ∈ F_1) but also to (r, 1) (considering r ∈ F_2). This shows that the
finitely many relations given by those determining P, those saying the factors of the direct product
commute, and those determining the conjugation in the HNN extension, imply for all r ∈ R that
(r, r) = (r, 1) hence (1, r) = 1."

Remark 2.2 of the source: Leary's `FP_2` embedding [Lea18a] uses the same device; its first step
[Lea18a, Lemma 2.5] embeds the double into a group `P` of type `FP_2`, and "if we only assume P is FP_2,
then this is still enough to ensure that Hig_ι(G) is FP_2 [Lea18a, Lemma 2.2]". When `R` is recursively
enumerable the resulting host is recursively presented.

## Theorem B and its lemmas

> **Theorem B.** Let G = F/R, and let Hig_ι(G) be as in Definition 1.5. Suppose G is infinite and R ≠ 1.
> Then H_3(Hig_ι(G); Q) is infinite-dimensional; in particular Hig_ι(G) is not of type FP_3(Q).

> **Remark 3.1** (excerpt). "If G is finite, then R is a finite-index subgroup of F, hence L is of type
> F_∞. Similarly, if R = 1, then L is a free group ... these assumptions are equivalent to saying that the
> free group R is infinite rank."

> **Lemma 3.2.** If ker(H_2(L; Q) → H_2(G; Q)), the map induced by π, is infinite-dimensional, then
> H_3(Hig_ι(G); Q) is infinite-dimensional.

Its proof uses the Mayer–Vietoris sequence for HNN extensions [Bie81, Theorem 2.12]
`H_3(Hig_ι(G)) → H_2(L) --α--> H_2(P × G)` with `α = H_2(ι × 1) − H_2(ι × π)`, the Künneth surjection
`κ: H_2(P × G) → H_2(P) ⊕ H_2(G)` killing the finite-dimensional mixed term, and
`κ∘α = 0 ⊕ −H_2(π)`.

> **Lemma 3.3.** We have an isomorphism H_2(L; Z) ≅ ker(H_1(R; Z) → H_1(F; Z)). In particular, H_2(L; Q)
> is infinite-dimensional.

> **Lemma 3.4.** The induced map H_2(π): H_2(L; Q) → H_2(G; Q) has infinite-dimensional kernel.

Its proof identifies the integral kernel with `[F, R]/[R, R] ≤ R/[R, R]` and shows it has infinite rank
using disjoint translates of an embedded circuit in the covering space of a wedge of circles for `R`.

> **Remark 3.5** (excerpt). "It is important in all of this that F is a free group. ... the other part
> of the proof of these embedding theorems, for example Leary's proof that ⟨F, t | tr = rt for all r ∈ R⟩
> always embeds in a group of type FP_2, relies heavily on F being free."

## Where this leaves the level-3 question (lane summary)

- Theorem A and the observation above make three statements equivalent, and they are Cairn claims:
  `every-finitely-presented-group-embeds-in-an-f3-group` (`E_3`: the case n = 2 of Problem 1.1, part 1),
  "`U` embeds in a group of type `F_3`", and `universal-fp-group-embeds-in-an-rp-fp3-group`.
- Theorem B kills the untwisted rope trick over every finitely generated host `P`.
- Part 2 of this artifact (next landing) records two general obstructions proved in this lane, both
  complete: any finite graph of groups with vertex groups of finite rational `H_2` and an edge group of
  infinite rational `H_2`; and the rope trick with two different embeddings over a host with
  finite-dimensional `H_2(P; Q)`. It also records one candidate container that escapes every
  trivial-coefficient obstruction, left open.
