# Novelty of the simple Kazhdan sofic group note: prior art, bound, verdicts (part 1)

Lane `sk-novelty`, 2026-09-13, about 18:40–19:10 CDT.
- **Subject.** `simple_kazhdan_sofic_group.tex`, disk version of 16:46 (340 lines, md5 7b3dc4ec…). Line numbers refer to
  that version.
- **Status.** Literature audit only. Nothing is proved here.
- **Scale.** NEW (bounded) / FOLKLORE / PRIOR, as in `un-novelty-2026-09-13-part1.md`.

## 0. Method and bound

**Earlier repo artifacts reused, read in full (tag R; their own source tags apply).**
- `ex-novelty-pestov91-deep-pass-2026-09-12.md`: 12 LaTeX sources grepped, 369 citing titles.
- `pestov91-literature-background-2026-09-13-part2.md` §§7–13, where sources were read at page level.
- `un-novelty-2026-09-13-part2.md`.
- `un-prior-art-2026-09-13-part1.md`.
- `un-stepanov-credit-2026-09-13.md`.
- `un-open-5-word-problem-degrees-2026-09-13.md`.

**New in this lane.**
- About 20 web searches (US engine, 13 Sep 2026).
- arXiv pages opened through the fetch tool (tag A): 2304.09307, 0810.2180 (abstract and ar5iv html), 0809.4095,
  2512.04531, 2312.11684, 1703.06092, 2604.19174 (html), math/0404117v3 (html), and 2512.09180 (PDF text).
- The fetch tool summarizes with a small model. So an A-quote is only as reliable as that summary, and each one needs a
  PDF check before it is printed in the note. W marks a search snippet only.

**Not done.**
- MathSciNet and zbMATH; journal versions.
- End-to-end reading of any paper.
- The Kac–Moody and Mimura literature beyond abstracts; the Brown–Ozawa book; the Russian normal-structure literature.

## 1. The headline theorem: the first infinite simple Kazhdan group that is LEF, sofic or hyperlinear?

**Verdict: NEW within the bound.** G_X answers the question in all three recorded forms:
- Brown 2001, §11 Question 7 (von Neumann algebra form);
- Ozawa 2003 (hyperlinear form);
- Pestov 2008, Open question 9.1 (adds the sofic form).
The disk note (l.38–42) names all three. Wording and pages are sk-citations' lane.

**Open-status record, in order.**
- **Ozawa,** math/0306067 (R: S): "It is unknown whether there exists a simple property (T) group Γ which is
  hyperlinear."
- **Pestov,** 0804.3968v8, Open question 9.1 (R: P, S): "Let G be an infinite simple group with Kazhdan's property (T).
  Can it be hyperlinear (sofic)?"
- **Thom,** 0810.2180 (R: S, P; A): "There are two sources of simple groups with Kazhdan's property (T)", namely
  Kac–Moody lattices and Gromov's Tarski-monster quotients of hyperbolic Kazhdan groups. His own LEF Kazhdan group is
  not simple (§1.2).
- **Pestov–Kwiatkowska,** *Appalachian Set Theory 2006–2012* (CUP 2012), arXiv v4 p. 28 (R: P): "it remains in
  particular unknown whether finitely generated simple Kazhdan groups can be hyperlinear/sofic."
- **Cornulier,** 0906.3374 (R: P): the infinite isolated Kazhdan groups of [CGP, 5.4] are "not known" to be sofic.
- **Dadarlat,** 2007.12655v2, Example 3.15(ii) and Prop. 3.19 (Ozawa–Thom) (R: S, P): infinite simple (T) groups are
  not weakly quasidiagonal. No simple MF example is given.
- **Alekseev–Thom,** 2608.05362v1 (5 Aug 2026), §5 (R: P): the list of known sofic non-RF Kazhdan groups names only
  Thom's group. No simple group is named. Their Open problem 6.1 asks for a *finitely presented* one.
- **This lane (Sep 2026).**
  - No search surfaced an answer or a claimed answer (W).
  - Ersoy, 2604.19174 (Apr 2026), does not discuss the question (A).
  - The fetched text of Fournier-Facio, 2512.09180, did not contain it (A; weak evidence).

### 1.1 Known infinite simple Kazhdan groups, and why none already answered the question
- **Caprace–Rémy twin building lattices,** Invent. Math. 176 (2009) (R: T). These are simple, and many are finitely
  presented with (T).
  - A finitely presented LEF group is RF (Vershik–Gordon; Alekseev–Thom p. 18, R: P). So the f.p. ones are not LEF.
  - No source found proves any of them sofic or hyperlinear.
- **Gromov's Tarski-monster quotients** of hyperbolic Kazhdan groups (Thom's summary, R). Every source found calls
  their soficity unknown.
- **Infinite simple Kazhdan groups in general.** A continuum of property (T) groups exists (Ioana–Tucker-Drob,
  2512.04531, A: "a continuum sized family … which have property (T)"). Those groups are not claimed to be simple.
  Coulon–Fournier-Facio (2312.11684, A) build continuum many infinite simple characteristic quotients of free groups;
  the fetched abstract does not mention (T). So I did not locate a verified source for "continuum many infinite simple
  Kazhdan groups" without LEF (§3).

### 1.2 Nearby constructions that are not answers
- **Thom, Theorem 1.4** (A, ar5iv, quoted as verbatim by the tool): "There exists a finitely generated Kazhdan group G
  which is locally embeddable into finite groups (in particular sofic and hence hyperlinear) but does not have the
  factorization property."
  - Construction (A): G = G'/C, where G' comes from a block upper-triangular group G_0(F_p[t,t^{-1}]) and C is part of
    its centre. Conjugation by diag(t,1,…,1) induces a surjective, non-injective endomorphism, so G is non-Hopfian.
  - Its kernel is a proper nontrivial normal subgroup, so G is not simple, as the note says (l.63–65).
  - The abstract adds: "an example of a sofic Kazhdan group which is not residually finite, answering a question of
    Elek and Szabo".
- **Ershov–Jaikin-Zapirain,** 0809.4095 (A abstract; R: S grep): property (T) for EL_n(R), n ≥ 3, R finitely generated
  associative. No application to simple groups. EJZK 1102.0031 (R: S) has simple groups only as finite quotients
  ("mother group" of the finite simple groups of Lie type).
- **Kassabov,** Invent. Math. 170 (2007) 297–326 (W): the Cayley graphs of SL_{3k}(F_p) "can be made expanders with a
  suitable choice of generators". These are finite groups.
- **Kionke–Schesler,** 2304.09307, *From telescopes to frames and simple groups* (A):
  - 2-generated infinite amenable simple groups;
  - embeddings of finitely generated residually finite amenable groups into finitely generated amenable LEF simple
    groups;
  - property (τ) appears only in Grothendieck pairs, and there is no (T).
- **Topological full groups** [[T]]' of minimal subshifts: infinite, finitely generated and simple (Matui, Internat. J.
  Math. 17 (2006)); LEF (Grigorchuk–Medynets 2014, Thm 2.6, R: P); amenable (Juschenko–Monod, Ann. of Math. 178
  (2013)), so never Kazhdan.
  - So infinite finitely generated simple LEF groups were known.
  - The combination with (T) is the new point.
- **EL_n over Steinberg or Leavitt algebras** (R: `un-prior-art` part 1 §1.4 and part 2):
  - no earlier Kazhdan simple group from a Steinberg algebra;
  - no normal-structure theorem for EL_n over noncommutative simple rings in general. Gerasimov's rings have E_n not
    normal in GL_n.

**Residual risk.** A soficity theorem for Kac–Moody lattices or Gromov monsters, or an unindexed 2026 preprint. Neither
surfaced within the bound.

## 2. What in the proof is prior

| Step of the note | Verdict | Source and credit |
|---|---|---|
| (T) of EL_3(R), R f.g. (l.97–99) | PRIOR, credited | EJZ, Invent. Math. 179 (2010), Thm 1.1 |
| R simple, Z(R) = F_2 (l.102–113) | PRIOR, credited | BCFS Thm 4.1 (over C); Clark–Edie-Michell Cor 4.6 and Steinberg Cor 3.6 (any field) (R: P). The note's direct argument is folklore |
| Z(G) = 1 from Z(R) (l.114–116) | FOLKLORE | standard |
| Periodic words with the same (2k+1)-words (l.123–129) | FOLKLORE | uniform recurrence; the "method of periodic approximation" of Grigorchuk–Medynets (GM intro, R: S) |
| Finite matrix models of R, so G is LEF (l.131–149) | NEW (bounded) as an application; routine given the mechanism | the ring counterpart of GM's periodic approximation for full groups. Ara–Claramunt embed the Z crossed product through rank functions, which is a different and weaker target (R) |
| LEF ⇒ sofic ⇒ hyperlinear (l.150–152) | PRIOR | the note cites Pestov's guide. Primary credits: Elek–Szabó, Math. Ann. 332 (2005) ("It is known [8],[19],[6] that the LEF-groups are sofic"; sofic ⇒ hyperlinear, Thm 2) (R: P) |
| Level ideal I_N two-sided, then N = G (l.223–227) | FOLKLORE / classical | the n ≥ 3 level-ideal step of normal-structure theory (Bass 1964; Hahn–O'Meara §4). The note does not credit it, and that is acceptable |
| Commutator localization into a finite simple tower group (l.175–221) | see part 2 | technique credit: Stepanov vs Matui |
| Word-problem degree and Turing corollary (l.229–262) | see part 2 | |

## 3. Flags for other lanes (recorded here; no messages sent)
- **sk-citations.** Thom's Theorem 1.4 states LEF + Kazhdan + no factorization property. "Not residually finite" is in
  his abstract; for Kazhdan groups it also follows from Kirchberg's theorem. The note's "[Thom, Theorem 1.4]" for "not
  residually finite" is defensible. The exact form would be "without Kirchberg's factorization property, hence not
  residually finite".
- **sk-universal-embedding-a/b.** Kionke–Schesler (2304.09307, A) already embed f.g. RF amenable groups into f.g.
  amenable LEF simple groups. The Kazhdan counterpart is the only new part.
- **sk-expanders-limits.** Kassabov (2007, W) already gives SL_{3k}(F_p) expanders from noncommutative universal
  lattices. "The finite models are expanders" is Kassabov-type prior art; only "they converge to an infinite simple
  Kazhdan group" can be new.
- **sk-operator-algebras.** Dadarlat 2007.12655v2 p. 2 prints "MF ⇒ weak quasidiagonality". G_X is LEF, hence MF, and
  by his Prop. 3.19 it is not weakly quasidiagonal. So G_X contradicts that printed arrow (ex-novelty tension, checked
  against the PDF by ex-verify-groups at 0efeac4106).

*Continued in part 2: technique credit, the Turing corollary, novelty statements.*
