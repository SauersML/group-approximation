# Pestov 9.1: literature background, verified at source (part 1 of 4)

Lane `pc-lit-background` (PC swarm), 2026-09-13.
- Part 1: method; the question and its origin; Kirchberg, Thom, Ershov–Jaikin-Zapirain, Bekka–de la Harpe–Valette (§§1–6).
- Part 2 (`pestov91-literature-background-2026-09-13-part2.md`): Grigorchuk–Medynets, simplicity over any field,
  Dadarlat, the post-2008 open-status record, known simple Kazhdan groups, LEF/sofic credits, the subshift (§§7–13).
- Part 3 (`-part3.md`): corrections to landed text and docstrings; the bound of this pass.
- Part 4 (`-part4.md`): `formalization.yaml` source rows.

This pass builds on the novelty and credit record already on main and does not repeat it:
- `ex-novelty-pestov91-deep-pass-2026-09-12.md`;
- `ex-pestov91-second-review-2026-09-13.md` (R5, R6, N6, §C);
- `pestov-9-1-writeup-2026-09-13-part3.md` (§§8–10);
- `ex-open-status-2026-09-12.md` (row 4).

Those passes decided novelty. This one pins down each source that the Palomar surface and the yaml cite: full
citation, arXiv version, exact number, verbatim quote with page, and what the development uses it for.

## Method

- **arXiv.** Abstract pages of 20 identifiers were fetched on MSI for version histories, comments and author names.
- **Journal data.** Crossref records gave DOI, volume, issue and pages, one query per source.
- **Statements.** Read as page images in the arXiv PDF of the named version. Theorem numbers were checked by walking
  the LaTeX counters in the e-print source, where the source was on MSI.
- **Publisher PDFs,** fetched on MSI: Kirchberg 1994, Jacobs–Keane 1969, Elek–Szabó 2005.
- **Bekka–de la Harpe–Valette.** Read in the authors' preprint of the book (523 pp.), quoting its book page
  numbers. The printed Cambridge edition was not opened.

Tags:
- P: page image read in this pass;
- S: LaTeX source lines read in this pass;
- T: page located through the PDF text layer only;
- X: Crossref record;
- A: arXiv abstract page.

## 1. The question: Pestov, Open question 9.1

- **Citation.** V. G. Pestov, *Hyperlinear and sofic groups: a brief guide*, Bull. Symbolic Logic 14 (2008), no. 4,
  449–480, doi:10.2178/bsl/1231081461 (X). arXiv:0804.3968v8, 4 Aug 2008 (A). The arXiv comment reads: "This version
  incorporates minor corrections made in the Bulletin of Symbolic Logic galley proofs -- The Bulletin of Symbolic
  Logic 14 (2008), pp. 449-480." (A)
- **Location.** §9 "Some classes of groups to look at", v8 p. 21 (P); `hypsof.tex` lines 841–848 (S).
- **Verbatim** (P, p. 21):
  > The two candidates for a counter-example are mentioned in Questions 9.1 and 9.4.
  >
  > **Open question 9.1** (Cf. Ozawa [64]). Let G be an infinite simple group with Kazhdan's property (T). Can it be
  > hyperlinear (sofic)?
  >
  > For theory of groups with property (T), we refer to [22] and especially [7]. For a way to construct groups with a
  > combination of properties mentioned in Problem 9.1, see [37].
- **References.**
  - v8 p. 27 (P): "[64] N. Ozawa, About the QWEP conjecture, Internat. J. Math. 15 (2004), 501–530."
  - The source keys (S): `[7]` = `BdlHV`, Bekka–de la Harpe–Valette's book; `[22]` = `dlHV`, de la Harpe–Valette,
    Astérisque 175; `[37]` = `gromov87`, Gromov, *Hyperbolic groups*, MSRI Publ. 8 (1987).
- **Definitions behind the challenge block** (S; pages T):
  - Definition 3.1 (p. 6): "A group G is sofic if it is isomorphic to a subgroup of a metric ultraproduct of a
    suitable family of symmetric groups of finite rank with their normalized Hamming distances. In other words, there
    are a set A, an ultrafilter U on A, and a mapping α ↦ n(α) so that G < (∏_α (S_n(α), d_hamm))_U."
  - Definition 3.2 (p. 6): the same, with "unitary groups of finite rank, with their normalized Hilbert-Schmidt
    distances".
  - Theorem 3.3 (p. 7): "(Elek and Szabó [ES]) Every sofic group is hyperlinear." After its proof: "By contrast, the
    converse implication is unknown." This is Open question 3.4.
  - Theorem 3.5 (p. 8): "A group G is sofic if and only if for every finite F ⊆ G and for each ε>0, there exist a
    natural n and a mapping θ: F → S_n so that (1) if g,h,gh ∈ F, then d_hamm(θ(g)θ(h), θ(gh)) < ε, (2) if e ∈ F then
    d(θ(e), Id) < ε, and (3) for all distinct x,y ∈ F, d_hamm(θ(x),θ(y)) ≥ 1/4."
  - Theorem 3.6 (p. 9): the same criterion for hyperlinearity, with θ: F → U(n), ‖θ(g)θ(h) − θ(gh)‖_2 < ε,
    ‖θ(e) − Id‖_2 < ε, and ‖θ(x) − θ(y)‖_2 ≥ 1/4.
  - Numbering (S): §3 has Definitions 3.1–3.2, Theorem 3.3, Open question 3.4 and Theorems 3.5–3.6 on one counter.
    §6 is "Gottschalk Surjunctivity Conjecture", as the existing yaml row says.
- **Framing.** Pestov offers 9.1 as a likely source of a counterexample, so a positive answer goes against his framing.
- **Uses.**
  - `Palomar/Pestov91Challenge.lean` renders the statement.
  - Theorems 3.5–3.6 are the finite-set criteria that the block's `IsSoficGroup` and `IsHyperlinearGroup` imply
    (Part 3, E2).
- **Not reached.** The journal pages. The page of 9.1 in Bull. Symbolic Logic is not known here.

## 2. The origin: Ozawa, *About the QWEP conjecture*

- **Citation.** N. Ozawa, Internat. J. Math. 15 (2004), no. 5, 501–530, doi:10.1142/S0129167X04002417 (X).
  arXiv:math/0306067v2, 10 May 2004 (A).
- **Location.**
  - §7 "Groups with the Factorization Property", just after the proof of Theorem 7.4: v2 p. 26 (P), `main.tex`
    lines 2128–2132, 2138–2149 and 2190–2193 (S).
  - Thom cites the same passage as "[Oza04b, p. 527]" (arXiv:0810.2180 p. 4, P). That is the journal page; the
    journal PDF was not read.
- **Verbatim** (P, p. 26):
  > However, it is not that all groups have the property (F). Indeed, infinite simple groups with Kazhdan's property
  > (T) (for existence of such groups, see [Gr1]) do not have the property (F) as it was shown by Kirchberg [Ki3].
  >
  > **Theorem 7.4.** Let τ be a trace on the full C*-algebra C*Γ of a group Γ with Kazhdan's property (T). Then, τ is
  > liftable if and only if there is a sequence of *-homomorphisms π_n: C*Γ → M_k(n) such that
  > τ(a) = lim_n tr_k(n) π_n(a). In particular, a group Γ with the properties (F) and (T) is residually finite.
  >
  > It is unknown whether there exists a simple property (T) group Γ which is hyperlinear. By the above theorem, the
  > full C*-algebra C*Γ of such a group Γ cannot have the LLP.
- **Numbering** (S). §7 has Proposition 7.1, Definition 7.2, Proposition 7.3 and Theorem 7.4 on one counter. This
  matches Pestov, who cites "Ozawa [ozawa], Prop. 7.1" for "VN(G) embeds into R^ω if and only if G is hyperlinear"
  (`hypsof.tex` line 799).
- **Reading.** Ozawa's sentence does not say "infinite".
  - Its second sentence is false for finite groups, since their full C*-algebras are finite-dimensional and so have
    the LLP.
  - So the question concerns infinite groups, and Pestov's wording says so.
  - The witness is infinite, so it answers the question on either reading.
- **Uses.** The origin of 9.1. Also the consequence that C*(S) fails the LLP (writeup Part 3 §7.4), which is not
  formalized.

## 3. Kirchberg's theorem

- **Citation.** E. Kirchberg, *Discrete groups with Kazhdan's property T and factorization property are residually
  finite*, Math. Ann. 299 (1994), 551–563, doi:10.1007/BF01459798 (X; publisher PDF, P). Received 26 March 1992,
  revised 26 May 1993 (P, p. 551).
- **Verbatim** (P, p. 552):
  > **Theorem 1.1** A discrete group with property (F) and property T is residually finite.
  >
  > **Corollary 1.2** For a discrete group G with property T, the following properties are equivalent: (i) G has
  > property (F). (ii) There exists a faithful unitary representation from G into the hyperfinite II_1-factor. (iii)
  > There exists a faithful group homomorphism from G into a locally compact group H with nuclear universal group
  > C*-algebra C*(H). (iv) G is residually finite. (v) There exists a faithful group homomorphism from G into an
  > almost connected locally compact group.
- **Caveat.** Thom, arXiv:0810.2180v1 p. 4, Remark 1.6 (P): "E. Kirchberg claims in [Kir94, Corollary 1.2] that the
  three properties in Theorem 1.1 are equivalent to G being isomorphic to a subgroup of an almost connected locally
  compact group. However, our second example K of a group without factorization property arises as a subgroup of a
  connected finite dimensional Lie group and disproves this claim." Cite Theorem 1.1, or items (i), (ii) and (iv),
  and never item (v).
- **Uses.** An infinite simple group is not residually finite, so an infinite simple Kazhdan group lacks property
  (F). This is background for Ozawa's remark and for writeup §7.3. It is not formalized and not used by the Lean chain.

## 4. The nearest earlier object: Thom

- **Citation.** A. Thom, *Examples of hyperlinear groups without factorization property*, Groups Geom. Dyn. 4 (2010),
  no. 1, 195–208, doi:10.4171/GGD/80 (X; the year as in Pestov–Kwiatkowska's bibliography, S). arXiv:0810.2180v1,
  the only version (A).
- **Location.** §1, v1 pp. 2–4 (P for pp. 3–4); `main.tex` lines 78–130 (S). On the §1 counter: Theorem 1.1
  (Kirchberg), Definition 1.2, Theorem 1.3 (Mal'cev), Theorems 1.4 and 1.5, Remark 1.6 (S; P for 1.2–1.6).
- **Verbatim** (P):
  - Theorem 1.1, attributed in its heading to Kirchberg, items on p. 3: "For a Kazhdan group G, the following
    properties are equivalent: (i) G has the factorization property. (ii) G is residually finite. (iii) G is isomorphic
    to a subgroup of the unitary group of the hyperfinite II_1-factor."
  - p. 3: "There are two sources of simple groups with Kazhdan's property (T). Such groups appear for example as
    lattices in certain Kac-Moody groups, see [CR06]. Much earlier, it was also shown by Gromov ([Gro87]) that every
    hyperbolic group surjects onto a Tarski monster, i.e. every proper subgroup of this quotient is finite cyclic; in
    particular: this quotient group is simple and is a Kazhdan group if the hyperbolic group was a Kazhdan group."
  - p. 3: "In fact, we show that our example admits a surjective and non-injective endomorphism (i.e. it is
    non-hopfian)".
  - Theorem 1.4, p. 4: "There exists a finitely generated Kazhdan group G which is locally embeddable into finite
    groups (in particular sofic and hence hyperlinear) but does not have the factorization property."
  - p. 4: "This answers the question whether all hyperlinear groups could have the factorization property, see
    [Oza04b, p. 524]. As Ozawa points out (see [Oza04b, p. 527]), the maximal group C*-algebra of G cannot have the
    local lifting property."
- **Not simple.** A non-hopfian group has a surjective endomorphism with nontrivial kernel. That kernel is a proper
  nontrivial normal subgroup.
- **Uses.** The nearest earlier object: the witness strengthens "finitely generated LEF Kazhdan group without (F)"
  to an infinite simple such group.

## 5. Property (T): Ershov–Jaikin-Zapirain (formalized, not cited)

- **Citation.** M. Ershov, A. Jaikin-Zapirain, *Property (T) for noncommutative universal lattices*, Invent. Math.
  179 (2010), no. 2, 303–347, doi:10.1007/s00222-009-0218-2 (X). arXiv:0809.4095v2, 21 Dec 2009, comment "final
  version -- Inventiones Mathematicae 179 (2010), no. 2, 303-347" (A).
- **Location.** §1.1, Theorem 1.1, v2 p. 1 (P); `EL_n0909.tex` lines 405–410 (S, earlier lane).
- **Verbatim** (P, p. 1):
  > **Theorem 1.1.** Let R be a finitely generated (associative) ring with 1 and n ≥ 3. Let G = EL_n(R), that is, the
  > subgroup of GL_n(R) generated by elementary matrices. Then G has Kazhdan's property (T).
- **Prior results** (P, p. 2): "Prior to this paper property (T) for EL_n(R), n ≥ 3, was known when either R is
  commutative or the stable range of R is at most n – this has been established in the works of Shalom [Sh3] and
  Vaserstein [Va], with explicit Kazhdan constants provided by Ozawa [BO]."
- **Status here.** Proved in Lean, not assumed.
  - The theorem is `GroupApproximation.IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`
    ("EJZ, audited", PC RULES).
  - `GroupApproximation/Pestov91/Kazhdan.lean` consumes it.
  - The yaml and the docstrings should say "proved in this development", as the Bowen–Chapman EJZ row already does.
- **Uses.** Property (T) for `EL_3(R)` over the witness ring, and then for its central quotient.

## 6. Kazhdan pairs: Bekka–de la Harpe–Valette

- **Citation.** B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, New Math. Monogr. 11, Cambridge Univ.
  Press, 2008, doi:10.1017/CBO9780511542749 (existing yaml row). Read in the authors' preprint PDF, book pp. 32–33 (P).
- **Verbatim** (P):
  - p. 32: "A unitary representation of G in H is a group homomorphism π : G → U(H) which is strongly continuous".
  - Definition 1.1.1, p. 32: "Let (π, H) be a unitary representation of a topological group G. (i) For a subset Q of G
    and real number ε > 0, a vector ξ in H is (Q, ε)-invariant if sup_{x∈Q} ‖π(x)ξ − ξ‖ < ε‖ξ‖." ... "(iii) The
    representation (π, H) has non-zero invariant vectors if there exists ξ ≠ 0 in H such that π(g)ξ = ξ for all
    g ∈ G."
  - Definition 1.1.3, p. 33: "Let G be a topological group. A subset Q of G is a Kazhdan set if there exists ε > 0
    with the following property: every unitary representation (π, H) of G which has a (Q, ε)-invariant vector also
    has a non-zero invariant vector. In this case, ε > 0 is called a Kazhdan constant for G and Q, and (Q, ε) is called
    a Kazhdan pair for G. The group G has Kazhdan's Property (T), or is a Kazhdan group, if G has a compact Kazhdan
    set."
- **Fidelity of the challenge's `IsKazhdanPair`.**
  - For a discrete group, strong continuity is automatic and the compact sets are the finite ones.
  - For a unit vector and finite Q, "sup < ε‖ξ‖" reads `∀ q ∈ Q, ‖ρ q x − x‖ < ε`, and `0 < ε` is "ε > 0".
  - Scalars. p. 32 speaks of adjoints and of "the unit representation of G in C", so the Hilbert spaces are complex.
    The book's conventions page was not read.
  - The universe restriction `E : Type` is argued in the challenge docstring, not in the book.
- **Uses.** The definition rendered in `Palomar/Pestov91Challenge.lean` and `GroupApproximation/Pestov91/KazhdanUnitary.lean`.

*Continued in Part 2.*
