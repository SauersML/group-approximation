# Khanh, arXiv:2609.08428v1: general linear and Steinberg groups over L_(F_2)(1,2)

Read on 2026-09-11 by the literature-scout lane `lit-groups`, from the arXiv
abstract page and from text extracted (ghostscript `txtwrite`, on MSI) out of the
PDF of v1. The labelled statements below were checked against the PDF text, not
only the HTML render. The proofs have **not** been independently reviewed in this
repository.

**Source.** Huynh Viet Khanh, *General linear and Steinberg groups over the
Leavitt algebra L_{F_2}(1,2)*, arXiv:2609.08428v1, submitted 8 September 2026,
<https://arxiv.org/abs/2609.08428>.

**Ring.** The paper's `R = F_2<e,f,e*,f*> / (e*e = f*f = 1, e*f = f*e = 0,
ee* + ff* = 1)` is this repository's `L_(F_2)(1,2)` under `s_0 = e`, `s_1 = f`,
`t_0 = e*`, `t_1 = f*` (relations `t_i s_j = delta_ij`, `s_0 t_0 + s_1 t_1 = 1`).

## Abstract (verbatim)

> Let R=L_{F_2}(1,2). We prove that GL_r(R) is integrally acyclic for every r≥1
> and that the canonical map St_r(R)→GL_r(R) is an isomorphism for every r≥3.
> The homology calculation combines simultaneous extensions of ordered frames
> with scalar actions of the multiplicative groups of finite fields on their
> stabilizers. The presentation associated with the same frame complex defines
> a surjective section of the Steinberg map. An explicit finite presentation of
> R^× then follows from the theorem of Krstić and McCool. We formulate separate
> criteria for acyclicity and for the Steinberg comparison over other rings.

## Labelled statements (PDF v1)

- **Theorem 4.4.** "The unit group of R = L_F2(1,2) is integrally acyclic. More
  generally, H_n(GL_r(R), Z) = 0 for every n > 0 and r ≥ 1."
- **Lemma 5.3.** "For R = L_F2(1,2), one has GL_m(R) = E_m(R) for every m ≥ 2."
- **Theorem 5.4.** "For R = L_F2(1,2) and every r ≥ 3, the canonical map
  φ_r : St_r(R) → GL_r(R) is an isomorphism."
- **Theorem 6.1** (Section 6, an explicit finite presentation). "The group
  G = R^× is finitely presented." The text before it: finite presentability is
  a consequence of Theorem 5.4 and the Krstić–McCool theorem. The explicit
  presentation is **Proposition 6.2**.
- The introduction states that no assertion is made about the Steinberg kernel
  at rank two. The paper does not mention soficity, hyperlinearity, property
  (T) or simplicity.

## What it settles in this graph

- `fp-simple-nonsofic-group`: `R^×` is finitely presented (Theorem 6.1), simple
  (`binary-leavitt-unit-group-is-simple`) and nonsofic
  (`openai-leavitt-unit-nonsofic`). Route: `fp-simple-nonsofic-via-leavitt-unit-group`.
- `fp-simple-full-mf-radical-group`: the same group has full MF radical
  (`binary-leavitt-all-ranks-full-mf-radical`). Route:
  `fp-simple-full-mf-radical-via-leavitt-unit-group`.
- Attempt 1 recorded in `fp-simple-nonsofic-group` ("no finite presentation of any
  `EL_n(L_(F_2)(1,2))` is known here") is superseded.

## What it changes elsewhere (not wired by this lane)

- **Leavitt–Steinberg fork** (`leavitt-steinberg-hs-stability-fork`,
  `steinberg-hs-stability-equals-nonhyperlinearity`). Theorem 5.4 and Lemma 5.3
  make `U = St_5(L) → GL_5(L) = E_5(L)` an isomorphism, and prefix-code ring
  isomorphisms `M_n(L) ≅ L` give `GL_5(L) ≅ L^× ≅ GL_4(L) = E_4(L) = Q`. So the
  kernel called central in the fork's unstable branch is trivial, `U` is simple,
  and the fork reads: `L^×` is normalized-HS stable iff `L^×` is nonhyperlinear.
- `fp-simple-nonhyperlinearity-is-one-word-domination` now applies to `L^×` with
  the explicit relators of Proposition 6.2.
- Equations over `L^×` (`kl-violating-equation-over-leavitt-unit-group`): a
  relative presentation `<L^×, x | w>` becomes an ordinary finite presentation,
  and `H_2(L^×; Z) = 0`.

## Second pass: the proof chain, read in full (2026-09-11)

The whole PDF text of v1 (17 pages, primary class math.KT) was read after the
statements above were landed. Field, algebra and ranks are as stated: `R` is
the binary Leavitt algebra over `F_2`, Theorem 4.4 covers every rank `r >= 1`,
Theorem 5.4 every `r >= 3`, Theorem 6.1 the unit group itself. There are no
further hypotheses. What each result rests on:

- **Theorem 4.4** comes from the acyclicity criterion Theorem 2.2, whose two
  hypotheses are Proposition 3.2 and Corollary 4.3.
  - *Proposition 3.2* (standard inclusions are zero on positive homology) uses
    the published K-theory computation of Ara–Brustenga–Cortiñas (Münster J.
    Math. 2009, Theorem 7.6): all `K_i(R)` vanish, so `BGL_∞(R)^+` is
    contractible. The compression `c(u) = e u e* + f f*` satisfies
    `w c(u) w^(-1) = c(c(u))`, hence `c_*` is an idempotent that is locally
    nilpotent, hence zero.
  - *Corollary 4.3* (ordered frame complexes are highly connected) comes from a
    common transverse vector, Lemma 4.1 and Proposition 4.2, proved in the
    paper from Leavitt word reduction.
  - *Theorem 2.2* runs the stabilizer spectral sequence with scalar actions of
    `F_(2^m)^×` and Quillen's weight lemma, by induction on degree; the proof
    is given in full.
- **Theorem 5.4.**
  - At rank 4 it follows from the criterion Theorem 5.1, which uses Brown's
    presentation theorem (JPAA 1984) and lifts the relations into `St_4`. The
    criterion's hypotheses are Lemma 5.3, the five-term sequence with
    `H_2(GL_3) = 0` and perfectness of `St_3` together with the centrality
    Lemma 5.2, and simple connectivity of `|X_4(R)|` from Proposition 4.2.
  - The other ranks `r >= 3` follow by Voronetsky's refinement isomorphism
    (JPAA 225 (2021), §4 Proposition 1, used through arXiv:2004.08551v2), which
    this lane did not re-read.
- **Lemma 5.3** (`GL_m = E_m`) quotes Ara–Goodearl–Pardo and a remark of
  Menal–Moncasi. It is independently established here as
  `leavitt-gl-equals-el-and-perfect-unit-group`.
- **Theorem 6.1** uses Krstić–McCool (JPAA 141 (1999), Theorem 3: `St_n(B)` is
  finitely presented for every finitely presented ring `B` and every `n >= 4`),
  applied at rank 5 with Theorem 5.4. The same conclusion also follows at
  **rank 4**, from Theorem 5.1 alone together with the four-leaf coordinates;
  that path avoids Voronetsky.

References cited only for context are [7] (in press), [8] (Khanh–Thanh,
arXiv:2607.10351), [15] (Palmer–Wu, arXiv) and [16] (Preusser, arXiv). No step
of the proofs uses an unpublished result. Proposition 6.2's explicit
presentation has `20(4^195 - 1)/3` generators (`m = 194`); it is a proof of
existence, not a usable relator list.

**Verdict.** The quoted statements match the source. The proof chain is
complete, and its external inputs are all published theorems. No gap was found,
and the citation routes stand as direct imports. This is a reading, not a
refereeing: the spectral-sequence details of Theorem 2.2 were followed but not
re-derived line by line.

## Caveats

- v1 preprint, three days old when read, not refereed. The graph imports it
  through citation routes, the same practice as
  `kun-thom-nonsofic-wreath-citation`.
- Only the statements quoted above are imported.
