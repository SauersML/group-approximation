# Pestov 9.1: literature background, verified at source (part 2 of 4)

Lane `pc-lit-background`, 2026-09-13. Method and tags (P page image, S source, T text layer, X Crossref, A arXiv
abstract page) are in Part 1 (`pestov91-literature-background-2026-09-13.md`).

## 7. LEF by periodic approximation: Grigorchuk–Medynets

- **Citation.** R. Grigorchuk, K. Medynets, *On algebraic properties of topological full groups*, Sb. Math. 205
  (2014), no. 6, 843–861, doi:10.1070/SM2014v205n06ABEH004400 (X). arXiv:1105.0719v4 (A).
- **Location.** §2, Definition 2.5 and Theorem 2.6, v4 p. 5 (P). The same page says: "The proof of the following
  result is presented in Section 5."
- **Numbering** (S; P for 2.3–2.6). The §2 counter runs: Definition 2.1, Theorem 2.2, Theorem 2.3, Proposition 2.4,
  Definition 2.5, Theorem 2.6.
- **Verbatim** (P, p. 5):
  > **Definition 2.5.** A group G is called locally embeddable into finite groups (abbr. LEF) if for every finite set
  > F ⊂ G there is a finite group H and a map φ : G → H such that (a) φ is injective on F and (2) φ(gh) = φ(g)φ(h)
  > for every g, h ∈ F.
  >
  > The notion of an LEF group was introduced by Vershik and Stepin in 1980's as a group property equivalent to the
  > existence of uniform free approximations for group actions. We refer the reader to [VG] and [CSC, Chapter 7] for a
  > detailed exposition of the theory of LEF groups, see also references therein for complete historical information.
  >
  > **Theorem 2.6.** The topological full group of any Cantor minimal system is an LEF group.
- **Introduction** (S, `main.tex` line 69): "One of the main techniques in Cantor dynamics is the method of periodic
  approximation, which mimics the behaviour of (X,T) by periodic transformations."
- **Uses.** Credit for the mechanism.
  - The witness applies periodic approximation to a ring: periodic words of the subshift give matrix models of
    `LC(X, F_2) ⋊ Z` (lane pc-ring-lef).
  - Theorem 2.6 is about topological full groups and is not used.

## 8. Simplicity of the ring over any field (second review, note N6)

**8a. Complex coefficients: Brown–Clark–Farthing–Sims.**
- **Citation.** J. H. Brown, L. O. Clark, C. Farthing, A. Sims, *Simplicity of algebras associated to étale
  groupoids*, Semigroup Forum 88 (2014), no. 2, 433–452, doi:10.1007/s00233-013-9546-z (X). arXiv:1204.3127v2 (A).
- **Location.** §4 "Simplicity of Steinberg algebras", Theorem 4.1. The statement is at `main.tex` lines 430–433
  (S); the proof ends on v2 p. 7 (P). §4's first counter environment is 4.1 (S). Clark–Edie-Michell cite it as
  "[BCFS, Theorem 4.1]".
- **Verbatim** (S): "Let G be a locally compact, Hausdorff, étale groupoid such that G^(0) is totally disconnected.
  Then A(G) is simple if and only if G is both effective and minimal."
- **Scalars.** The abstract (S) says: "the complex *-algebra of its inverse semigroup of compact open bisections, as
  introduced by Steinberg, is simple if and only if G is both effective and minimal". `A(G)` is built from "the free
  complex module with basis W" (line 428). So the theorem is over C only.

**8b. Any field: Clark–Edie-Michell.**
- **Citation.** L. O. Clark, C. Edie-Michell, *Uniqueness theorems for Steinberg algebras*, Algebr. Represent. Theory
  18 (2015), no. 4, 907–916, doi:10.1007/s10468-015-9522-2 (X). arXiv:1403.4684v1 (A).
- **Verbatim** (P, v1 p. 7): "**Corollary 4.6.** Let G be a Hausdorff, ample groupoid and R a commutative ring with
  identity. Then A_R(G) is simple if and only if G is effective and minimal, and R is a field."
- **Introduction** (S, lines 150–152): "we generalize [BCFS, Theorem 4.1], which says a complex Steinberg algebra is
  simple if and only if G is effective and minimal. This result is not true for more general Steinberg R-algebras
  because ideals in R create ideals in A_R(G)."

**8c. Any field: Steinberg.**
- **Citation.** B. Steinberg, *Simplicity, primitivity and semiprimitivity of étale groupoid algebras with
  applications to inverse semigroup algebras*, J. Pure Appl. Algebra 220 (2016), no. 3, 1035–1054,
  doi:10.1016/j.jpaa.2015.08.006 (X). arXiv:1408.6014v2 (A).
- **Verbatim** (P, v2 p. 10):
  - "**Theorem 3.5.** Let G be an ample groupoid and k a field. If kG is simple, then G is effective and minimal. The
    converse holds if G is Hausdorff."
  - "**Corollary 3.6.** Let G be a Hausdorff ample groupoid and k a field. Then kG is simple if and only if G is
    effective and minimal."

**Application and verdict on N6.**
- The witness ring `LC(X, F_2) ⋊ Z` is the Steinberg algebra over F_2 of the transformation groupoid of the shift on
  X (writeup Part 3 §9; not re-derived here). That groupoid is Hausdorff and ample. It is effective because the action
  is free, and minimal because X is.
- So 8b and 8c give simplicity of the witness ring in one step. `GroupApproximation/Pestov91/RingSimple.lean` proves
  it directly, and nothing is imported.
- **N6.** A field-general source exists, and there are two. The credit line should read: "the complex case is BCFS,
  Theorem 4.1; the case of any field is Clark–Edie-Michell, Corollary 4.6, and Steinberg, Corollary 3.6". Writeup
  Part 3 §9 already says this. The landed `RingSimple.lean` docstring does not (Part 3, E3).

## 9. Dadarlat: MF and weak quasidiagonality

- **Citation.** M. Dadarlat, *Obstructions to matricial stability of discrete groups and almost flat K-theory*, Adv.
  Math. 384 (2021), 107722, doi:10.1016/j.aim.2021.107722 (X). arXiv:2007.12655v2, 18 Mar 2021, comment "Minor
  revision, to appear in Adv. Math" (A).
- **Verbatim.**
  - p. 1 (S line 148; T): "It is an open problem to find examples of discrete countable groups which are not MF."
  - p. 2 (P): "A group G is weakly quasidiagonal if there is a sequence {φ_n : G → M_k_n} of unital completely
    positive definite maps which satisfies the conditions (1) and (2), see also Definition 3.10."
  - p. 2 (P): "It is clear from definitions that MF ⇒ weak quasidiagonality and matricial stability ⇒ weak matricial
    stability." and "Quasidiagonal groups are weakly quasidiagonal."
  - Example 3.15(ii), p. 9 (S line 487; T): "Thom (cf. Yamashita) noted that infinite simple property (T) groups are
    not quasidiagonal, and in fact they are not weakly quasidiagonal, see Proposition 3.19."
  - p. 10 (P): "The following fact was essentially pointed out by Thom on MathOverflow [80]. It shows that an infinite
    simple property (T) group G is not weakly quasidiagonal."
  - p. 10 (P): "**Proposition 3.19** (Ozawa-Thom). If an infinite property (T) group G is weakly quasidiagonal, then G
    has an infinite residually finite quotient."
- **Numbering** (S, walk of §3). Definition 3.1, Proposition 3.2, Remark 3.3, Definition 3.4, Remark 3.5, Example 3.6,
  Propositions 3.7–3.9, Definition 3.10, Propositions 3.11–3.12, Remark 3.13, Proposition 3.14, Example 3.15,
  Proposition 3.16, Lemmas 3.17–3.18, Proposition 3.19. This agrees with the printed Lemma 3.18 and Proposition 3.19
  on p. 10 (P).
- **What the witness shows** (not formalized).
  - S is LEF, hence MF.
  - S is infinite, simple and Kazhdan, so by Proposition 3.19 it is not weakly quasidiagonal.
  - So the first clause of the p. 2 sentence fails for groups. The second clause and Proposition 3.19 stand (second
    review §C).
  - The Adv. Math. text was not compared with v2.
- **Uses.** Background only (writeup Part 3 §8). The Lean chain does not use Dadarlat.

## 10. The post-2008 open-status record

**10a. Pestov–Kwiatkowska.**
- **Citation.** V. G. Pestov, A. Kwiatkowska, *An introduction to hyperlinear and sofic groups*, in: *Appalachian Set
  Theory 2006–2012*, J. Cummings and E. Schimmerling (eds.), Cambridge Univ. Press, 2012, pp. 145–186,
  doi:10.1017/CBO9781139208574.006 (X: chapter pages, editors, book print year 2012). arXiv:0911.4266v4, 24 Apr 2012
  (A). The brief's "2009" is the date of arXiv v1.
- **Location.** §10 "Discussion and further reading", v4 p. 28 (P); `cornell.tex` line 1213 (S).
- **Verbatim** (P, p. 28):
  > **Theorem 10.2** (Kirchberg, Valette). If a group with property (T) embeds into the group U(R) (in particular,
  > into its subgroup [R]), then it is residually finite.
  >
  > It is in view of such results that Ozawa asked whether every finitely generated Kazhdan group that is sofic is
  > residually finite. A negative answer was announced by Thom [26]. Consequently, a hope to use property (T) in order
  > to construct non-hyperlinear groups is a bit diminished now, but surely not gone, as it remains in particular
  > unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic.
- **Reference** (S). `[26]` is source key `thom`: "A. Thom, Examples of hyperlinear groups without factorization
  property, Groups Geom. Dyn. 4 (2010), 195–208."
- **Correction.** `ex-novelty-pestov91-deep-pass-2026-09-12.md` (b) ends this quote with the reconstruction
  "[s can be hyperlinear]". The printed ending is "simple Kazhdan groups can be hyperlinear/sofic."

**10b. Capraro–Lupini.**
- **Citation.** V. Capraro, M. Lupini, *Introduction to Sofic and Hyperlinear Groups and Connes' Embedding
  Conjecture*, Lecture Notes in Math., Springer, 2015, doi:10.1007/978-3-319-19333-5 (X). arXiv:1309.2034v6 (A).
- **Keyword search of the v6 source** `AllTogetherLocal41.tex` (S). Every "property (T)" passage is one of:
  - the definition (line 2354ff);
  - "an infinite hyperbolic residually finite property (T) group K. (Examples of such groups are provided in
    [gromov_hyperbolic_1987].)" (lines 2369–2372);
  - de Cornulier's group Γ/Z, which "being finitely presented, property (T), and not Hopfian, is not LEA" (line 2544);
  - II_1 factors with property (T).
- **Simple groups.** The only "simple" within three lines of "property (T)" is an alternating group inside a
  permutation group (line 2397).
- **Status statement.** No passage found states Question 9.1 or its status. Bound: grep of one source file, not an end-to-end reading.

**10c. Cornulier.**
- **Citation.** Y. Cornulier, *A sofic group away from amenable groups*, Math. Ann. 350 (2011), no. 2, 269–275,
  doi:10.1007/s00208-010-0557-8 (X). arXiv:0906.3374v2 (A).
- **Location.** §1, v2 p. 2 (P).
- **Verbatim** (P): "Examples of isolated groups were provided in [CGP]. In that paper, examples of infinite isolated
  groups with Kazhdan's Property T were given [CGP, Paragraph 5.4], but it is not known if they are sofic. Also, some
  lattices in non-linear semisimple groups with finite center, are known to be isolated [CGP, Paragraph 5.8], but they
  appear as natural candidates to be examples of non-sofic groups (see the discussion in Section 2)."
- **Relevance.** The sentence does not call those groups simple, and the witness says nothing about them.

**10d. Alekseev–Thom.**
- **Citation.** V. Alekseev, A. Thom, *Centralizers of sofic approximations of Kazhdan groups*, arXiv:2608.05362v1,
  5 Aug 2026 (A). No journal version.
- **Abstract** (S): "We prove that a Kazhdan group admitting a sofic embedding into a metric ultraproduct of symmetric
  groups with a centralizer that acts ergodically on the associated Loeb probability space is locally embeddable in
  finite groups (LEF). In particular, every finitely presented Kazhdan group admitting such an embedding is
  residually finite."
- **§5, pp. 17–18** (P):
  > Let's review some of the known examples: First, the second author constructed a Kazhdan group which is locally
  > embeddable into finite groups, hence sofic, but not residually finite [15]. Since a discrete Kazhdan group is
  > finitely generated, this gives a finitely generated sofic Kazhdan group which is not residually finite. It is not
  > finitely presented: every finitely presented LEF group is residually finite, because the finite presentation turns
  > sufficiently good local embeddings into genuine finite homomorphisms. Second, de Cornulier constructed finitely
  > presentable non-Hopfian Kazhdan groups [4]. Since finitely generated residually finite groups are Hopfian, these
  > groups are not residually finite. Related examples are known to be hyperlinear by work of the second author [15],
  > but they are not known to be sofic. Third, Kar and Nikolov constructed finitely presented sofic groups which are
  > not residually finite [9]. These examples do not have Kazhdan's property.
- **Open problem 6.1, p. 18** (P): "Are there examples of finitely presented sofic groups with Kazhdan's property (T)
  that are not residually finite?" The source key of `[15]` is `ThomHyperlinear` (S).
- **Relation to S.**
  - S is sofic, Kazhdan and not residually finite, but it is not finitely presented (writeup Part 3 §7.2). So it
    leaves 6.1 open.
  - S is LEF, which agrees with their Theorem A.
  - Their list names no simple group.

## 11. The known infinite simple Kazhdan groups

- **Caprace–Rémy.**
  - **Citation.** P.-E. Caprace, B. Rémy, *Simplicity and superrigidity of twin building lattices*, Invent. Math. 176
    (2009), no. 1, 169–221, doi:10.1007/s00222-008-0162-6 (X). arXiv:math/0607664v2 (A).
  - **Abstract** (T): "We prove that these lattices are simple if and only if the corresponding buildings are
    (irreducible and) not of affine type (i.e. they are not Bruhat-Tits buildings). In fact, many of them are finitely
    presented and enjoy property (T)."
  - **Introduction** (T): Λ = G_A(F_q), "divided by its finite center, is an infinite finitely generated simple group".
  - **Relation to LEF.** A finitely presented LEF group is residually finite (Alekseev–Thom p. 18, above), so none of
    the finitely presented ones is LEF.
- **Gromov**, *Hyperbolic groups*, in *Essays in Group Theory*, MSRI Publ. 8, Springer, 1987, 75–263,
  doi:10.1007/978-1-4613-9586-7_3 (X). Not read here. Three sources cite it for infinite simple Kazhdan groups:
  - Ozawa ([Gr1], p. 26);
  - Pestov ([37], p. 21);
  - Thom ([Gro87], p. 3, quoted in Part 1 §4).

## 12. LEF ⇒ sofic ⇒ hyperlinear: credits

- **Elek–Szabó.** G. Elek, E. Szabó, *Hyperlinearity, essentially free actions and L²-invariants. The sofic
  property*, Math. Ann. 332 (2005), no. 2, 421–441, doi:10.1007/s00208-005-0640-8 (X; publisher PDF, P).
  - p. 422 (P): "It is known [8],[19],[6] that the LEF-groups are sofic."
  - p. 423 (P): "We shall prove that countable sofic groups are hyperlinear (Theorem 2)."
  - **Scope.** Their theorem is stated for countable groups. Pestov's Theorem 3.3 drops "countable".
    `GroupApproximation.isSofic_of_isLEF` and `isHyperlinear_of_isSofic` prove both steps for arbitrary groups in the
    finite-set forms.
- **Vershik–Gordon.** A. M. Vershik, E. I. Gordon, *Groups that are locally embeddable in the class of finite
  groups*, St. Petersburg Math. J. 9 (1998), 49–67.
  - The bibliographic data is as printed in Pestov's bibliography (S). There is no Crossref hit, and the paper was not
    read.
  - Grigorchuk–Medynets refer to it for LEF groups (§7 above).
- **Ceccherini-Silberstein–Coornaert**, Cor. 7.5.11: cited by Grigorchuk–Medynets for "LEF ⇒ sofic" (S, line 163).
  Not read here. Their book already has a yaml row.

## 13. The witness subshift

- **Jacobs–Keane.** K. Jacobs, M. Keane, *0-1-sequences of Toeplitz type*, Z. Wahrscheinlichkeitstheorie verw. Geb.
  13 (1969), 123–131, doi:10.1007/BF00537017 (X; publisher PDF, P).
  - **Summary** (P, p. 123): "0-1-sequences are constructed by successive insertion of a periodic sequence of symbols
    0, 1 and "hole" into the "holes" of the sequence already constructed. Assuming that finally all "holes" are filled
    with symbols 0, 1, an almost periodic point in shift space results."
  - **Introduction** (P, p. 123): "The sequences thus obtained are called Toeplitz sequences. They are all almost
    periodic (Theorem 4)."
- **Uses.** Background for pc-architect's decision D1: the period-doubling Toeplitz sequence
  `pd n = (padicValInt 2 n).bodd`. The Lean development proves aperiodicity and minimality of its orbit closure
  directly (blueprint part 2, D1).
- **Not checked.** Whether that sequence meets Jacobs–Keane's §3 definition of a Toeplitz sequence.

*Continued in Part 3.*
