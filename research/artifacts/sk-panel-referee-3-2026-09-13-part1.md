# sk-panel-referee-3, part 1: exposition, structure and impact (hostile top-journal referee)

Lane `sk-panel-referee-3`, 2026-09-13 ~19:25 CDT. Emphasis: exposition, structure and impact.
- **Objects reviewed:**
  - main's base note (bf961c128b, md5 7b3dc4ec…, 340 lines);
  - revision 1 as landed on main at 5b1890ce6c (md5 8e04b341…, 292 lines). Line numbers "r1 l.N" refer to it. They agree with the editor's draft through l.220; main's landing added the fixes marked APPLIED below.
- **Also read:**
  - main's decision log `sk/drafts/rev2-decisions.md`;
  - the proposals of sk-exposition, sk-citations, sk-stable-rank-a/b, sk-open-1/2/4/5, sk-generators, sk-characters, sk-lef-growth, sk-subgroups, sk-universal-embedding-a and sk-operator-algebras.
- **Mathematics:** I re-checked the rev1 simplicity and finite-models text line by line and found no error. The small-set refinement, the scalar step, k ∈ H through injectivity of ψ, and the covering step all hold. The referees own correctness; this part is about what a top-journal referee would block on and what would make the paper astonishing.

## 0. Verdict (as a referee for Inventiones / JEMS / Duke)
- **The mathematics is correct, and the construction is the right one.** Rev1 is a clean four-page answer to a question stated by Brown (2001), Ozawa (2003) and Pestov (2008). No one has reached this answer as far as the sk-novelty search went.
- **As written, rev1 is a strong short note for a very good journal, not yet an astonishing paper.** A hostile referee raises three points:
  1. **Novelty framing.** "The new step is simplicity" (r1 l.59) invites the reply that simplicity follows from a published normal-structure theorem (§1, B2).
  2. **The claimed answer to Brown's form** is asserted, but the bridge is not written (B1).
  3. **Why the question matters** is never said, so the reader cannot measure the result (B5).
- **What would make it astonishing:**
  - the universality corollary (every f.g. residually finite group is a subgroup of an infinite simple Kazhdan LEF group), if it passes review;
  - the operator-algebra consequences Ozawa asked about;
  - an intro that says in one screen why simple Kazhdan groups were the natural place to look for non-hyperlinear groups, and that this class is now closed.

## 1. Blocking issues (fix before any submission)

**B1. The answer to Brown's form is asserted without a bridge.**
- r1 l.41 says "answers all three forms", but Brown asks for an embedding into the unitary group of an R^ω-embeddable McDuff factor.
- The bridge is one sentence, and sk-operator-algebras verified its sources:
  - hyperlinear ⟺ L(G) ⊂ R^ω (Ozawa Prop. 7.1);
  - G is ICC, so L(G)⊗̄R is a separable McDuff factor that embeds in R^ω and whose unitary group contains G.
- Main's decision log item 17 already adopts this. I endorse it as a MUST, not an option: without it, an operator-algebra referee will write "the claim to answer Brown's question is not justified".

**B2. The novelty sentence is a credit risk.**
- r1 l.59 says "The new step is simplicity."
- sk-stable-rank-b (7ff75787cb, f5622522e1) proves simplicity through Stepanov's Theorem 4.4. Condition (b) there (linear dependence) is verified by a dimension count on one cylinder: any p, q ∈ R have (r,s) ≠ 0 with pr + qs = 0.
- **This route has PASSED review** (`sk-review-1-2026-09-13-part9.md` §1 and §3). The pass is conditional on the import node's quotation of Theorem 4.4 and its reading of p. 2152.
- So simplicity is an application of a 1997 theorem with a short verification. A referee who knows Stepanov will call the "new step" claim an overstatement.
- The pattern of the note's argument is also Matui's (r1 l.62-65 already credits him).
- **Recommendation:**
  - Drop "The new step is simplicity."
  - State what each property rests on, credit Matui for the localization pattern, and add one sentence (the route has passed review): "Simplicity also follows from Stepanov's normal-structure theorem [Stepanov, Theorem 4.4]."
  - Keep the self-contained proof. The reader-trade-off note in review part 9 applies: citing the theorem alone would ask the reader to trust a noncommutative normal-structure theorem the note does not prove.
  - The novelty is the group: the first infinite simple Kazhdan group shown to be LEF. That claim needs no qualifier; do not attach novelty to a step.

**B3. Credit locators and metadata.** Each is small, and together a referee reads them as carelessness.
- r1 l.66-67: `\cite[Theorem~1.4]{Thom}` for "not residually finite". Theorem 1.4 states the absence of the factorization property; non-residual finiteness is in the abstract and on p. 3 (sk-questions-ggt P1, decision log item 3). APPLIED on main in 5b1890ce6c: r1 l.67 now reads `\cite{Thom}`.
- r1 l.180-181: "the level $J$ … of $N$~\cite{Stepanov}". Citing a 1997 paper for the standard word "level" (Bass 1964) looks odd. Delete the citation here, and credit Stepanov where his theorem is used (B2).
- r1 l.134: the `[Example~4.5 and Theorem~3.3]{Pestov}` locators come from arXiv v8, and the journal numbering is unchecked (rev1 changelog G). The alternative is Elek–Szabó, Math. Ann. 332 (2005), p. 422 and Thm 2, as primary sources.
- Bibitems Matui and GMpres came through the fetch tool and are not Crossref-confirmed. VershikGordon has no DOI.
- r1 l.39 gives "Ozawa … in 2003", while the bibitem is the 2004 journal article. Either is defensible, but say "in 2003 (published 2004)" once, or match the bibitem.

**B4. The credit paragraph (APPLIED on main in 5b1890ce6c).**
- The draft said "Codex (OpenAI) shortened and edited this version."
- Main's landing now states the revision: r1 l.223 reads "Codex (OpenAI) shortened an earlier version, and Claude …".
- Resolved. Keep the paragraph in step with later revisions: the facts are not optional.

**B5. The paper never says why the question matters.**
- The intro states the question and the lineage, then the theorem. A top-journal reader outside operator algebras cannot tell whether this is a curiosity or a milestone.
- The sourced one-clause fix: Ozawa noted right after the question that the full C*-algebra of such a group cannot have the local lifting property [Ozawa, p. 527] (verbatim in sk-operator-algebras §1).
- A second, unsourced sentence ("simple Kazhdan groups were natural candidates for non-hyperlinear groups") should NOT be added unless a printed source is found. sk-questions-oa/ggt found none beyond Ozawa and Pestov's restatement in Pestov–Kwiatkowska (arXiv:0911.4266, p. 28).

## 2. Impact: what would make this astonishing (ranked, with budgets)

Rev1 is 291 source lines, about 4 pages. The budget that stays "short" for a top journal is about 5 pages (about 360 lines). The budgets below keep the paper under that.

| rank | addition | status | budget | verdict |
|---|---|---|---|---|
| I1 | Every f.g. residually finite group is a subgroup of an infinite f.g. simple Kazhdan LEF group (sk-universal-embedding-a 3bcc003284; without (T): Kionke–Schesler) | UNREVIEWED; with sk-verify-3/-4 | Corollary plus proof: at most 20 lines, plus a 6-8 line remark that Theorem 1's proof uses only a free minimal subshift with finite models over a f.g. group, plus 2 bibitems (Ore, Kionke–Schesler) | ADD after PASS. It is the single statement a non-specialist remembers: the class of simple Kazhdan sofic groups contains SL_n(Z), surface groups and Grigorchuk's group. Put it in the abstract. |
| I2 | Brown bridge plus the Kirchberg sentence (sk-operator-algebras Option B) | sources verified; nodes unreviewed with sk-referee-2 | +8 lines, +5 bibliography | ADD. The Brown bridge is B1. The factorization property and LLP answer why Ozawa asked. |
| I3 | Marked limits of finite simple groups SL_{3N}(F_2) with a uniform Kazhdan constant, hence expanders (node `finite-simple-groups-converge-to-simple-kazhdan-group` PASS twice; credit Kassabov) | reviewed; the Option A LaTeX is PASS+repair (`sk-review-2-2026-09-13-part2.md` §7b, repairs 7b.i-iii) | +8 lines (sk-expanders-limits Option A replaces r1 l.130-132) | ADD if the page budget allows after I1 and I2. It turns the LEF step into a sentence expander theorists will quote. Otherwise one sentence. |
| I4 | [[T]]' ⊂ G_X through g ↦ diag(w_g,1,1): the amenable simple group of X inside the Kazhdan simple group of X (sk-subgroups Corollary A) | UNREVIEWED | +4 lines (two identities) | One sentence in the intro after PASS. It shows the reader the mechanism behind the approximation. Keep the proof in Cairn if space is short. |
| I5 | Turing degrees and continuum many (r1 §2) | reviewed nodes; new continued-fraction route unreviewed | as in rev1 | KEEP, as the last section. |
| — | characters (partial), LEF growth, K-theory, generators (orders 7, 2, 2), hypotheses sharpness, subsystem sandwich, F_q remark, other acting groups beyond I1's remark, rigidity theorems | various | — | OUT. Each is true or partial but adds machinery without strengthening the headline. Rigidity survives only as Question 2 in §3. |

## 3. Structure (recommended plan; about 5 pages)
1. **Introduction** (about 40 lines):
   - the question and lineage, with Ozawa's LLP remark (B5);
   - Theorem 1 (rev1 statement);
   - a short paragraph with the corollaries in words (I1, I2, I5);
   - one method paragraph with credit (B2).

   The finite-presentation sentence and the open question at r1 l.67-70 move to §4.
2. **§1 Proof of Theorem 1:** rev1 l.72-186 unchanged in substance, plus I2 at the end of "Finite models", plus I3 if adopted.
3. **§2 Residually finite subgroups** (I1), after PASS.
4. **§3 Word problems** (rev1 §2).
5. **§4 Questions** (at most 15 lines; decision log item 18):
   - Q1: finitely presented infinite simple Kazhdan sofic or hyperlinear, with the Alekseev–Thom 6.1 credit;
   - Q2: rigidity, with the easy direction in one clause.
6. Origin and authorship (B4); bibliography.

## 4. Title and abstract
Main's sk-title-abstract lane owns the final call. My ranking, from the referee's chair:
- (T1) **"Sofic infinite simple groups with property (T)."** Plural, since the paper gives a family; the searchable keyword comes first; no adjective stack. Best if I1 is not adopted.
- (T2) **"Simple Kazhdan groups that are locally embeddable into finite groups."** States the stronger property. Good for a group-theory journal.
- (T3) **"Residually finite groups inside sofic simple Kazhdan groups."** Only if I1 is adopted and made the headline. Memorable, but it undersells the answer to Ozawa, so I rank it third.
- The current "An infinite simple Kazhdan sofic group" (singular) undersells a continuum family.

Abstract, if I1 and I2 are adopted (verbatim candidate; the lineage is the user's):
```latex
\begin{abstract}
For every infinite minimal subshift $X$, the group
$\EL_3(\LC(X,\F_2)\rtimes\Z)$ is an infinite, finitely generated,
simple group with property~\textup{(T)} that is locally embeddable into
finite groups, so it is sofic and hyperlinear. This answers the question
of Brown and Ozawa whether an infinite simple Kazhdan group can be
hyperlinear, and Pestov's sofic version of it. The word problems of these
groups realize every Turing degree, and every finitely generated
residually finite group is a subgroup of an infinite simple Kazhdan
group that is locally embeddable into finite groups.
\end{abstract}
```

## 5. Line-level fixes on rev1 (verbatim)

**F1. Opening (r1 l.37-41; B5).** +2 lines.
Before:
```latex
Can an infinite simple Kazhdan group be hyperlinear? Brown asked this
in its von Neumann algebra form in 2001~\cite[\S11, Question~7]{Brown},
and Ozawa in the hyperlinear form in 2003~\cite[p.~527]{Ozawa}.
Pestov's Open question~9.1 adds the sofic version~\cite{Pestov}.
The following construction answers all three forms positively.
```
After:
```latex
Can an infinite simple Kazhdan group be hyperlinear? Brown asked this
in its von Neumann algebra form in 2001~\cite[\S11, Question~7]{Brown},
and Ozawa in the hyperlinear form in 2003~\cite[p.~527]{Ozawa}, where he
noted that the full $C^*$-algebra of such a group cannot have the local
lifting property. Pestov's Open question~9.1 adds the sofic
version~\cite{Pestov}. The following theorem answers all three forms
positively.
```

**F2. Method paragraph (r1 l.56-70; B2, B3).** −2 lines; the last two sentences move to §4.
Before, r1 l.57-59 and l.65-67:
```latex
Jaikin-Zapirain~\cite{EJZ}. The finite models use periodic sequences
with the same short words as $X$, as in Grigorchuk and
Medynets~\cite{GM}. The new step is simplicity. A nontrivial normal
...
towers~\cite[Lemma~3.4 and Theorem~4.9]{Matui}. Thom constructed a
finitely generated Kazhdan LEF group that is not residually
finite~\cite{Thom}, but his example is not simple. A
```
After:
```latex
Jaikin-Zapirain~\cite{EJZ}. The finite models use periodic sequences
with the same words of a given length as $X$, as in Grigorchuk and
Medynets~\cite{GM}. In the proof of simplicity, a nontrivial normal
...
towers~\cite[Lemma~3.4 and Theorem~4.9]{Matui}. Thom constructed a
finitely generated Kazhdan LEF group that is not residually
finite~\cite{Thom}, but his example is not simple.
```
- "short words" is vague.
- "The new step" is the credit risk of B2.
- The Thom locator was already fixed on main.
- r1 l.67-70 ("A finitely presented LEF group … is sofic.") moves into §4 Questions.

**F3. Generating set (r1 l.99).** APPLIED on main in 5b1890ce6c (sk-generators P1).
Before: `So the matrices $e_{ij}(s)$ with $s\in\{1,u,u^{-1}\}\cup\{e_a:a\in A\}$`
After: `So the matrices $e_{ij}(s)$ with $s\in\{u,u^{-1}\}\cup\{e_a:a\in A\}$`
Reason: 1 = Σ_a e_a, so e_ij(1) = ∏_a e_ij(e_a). No later step uses 1 as a generator (r1 l.148 takes V = X, where e_X = 1 is a clopen indicator, not a generator).

**F4. Finite models, referent (r1 l.114-115).** 0 lines.
Before: `occurring in $x_{[0,m_\ell+2\ell)}$. This word begins and ends with`
After: `occurring in $x_{[0,m_\ell+2\ell)}$. The word $x_{[0,m_\ell+2\ell)}$ begins and ends with`
Reason: "This word" follows a sentence mentioning two words, so a reader stalls.

**F5. Finite models, quantifiers (r1 l.125-127).** 0 lines.
Before: `$PD_\ell(f)P^{-1}=D_\ell(f\circ T^{-1})$, for all $r,s\in R$ the identities`
After: `$PD_\ell(f)P^{-1}=D_\ell(f\circ T^{-1})$, for fixed $r,s\in R$ the identities`
Reason: the threshold for ℓ depends on r and s. "For all r, s … hold for large ℓ" can be read as uniform.

**F6. Level ideal (r1 l.180-181; B3).** 0 lines.
Before: `Finally, the level $J=\{r\in R:e_{pq}(r)\in N\text{ for all }p\ne q\}$` / `of $N$~\cite{Stepanov} is a two-sided ideal. It is additive`
After: `Finally, $J=\{r\in R:e_{pq}(r)\in N\text{ for all }p\ne q\}$` / `is a two-sided ideal. It is additive`
If the Stepanov bibitem becomes uncited, keep it for B2's sentence once that passes review; otherwise delete it.

**F7. Word problems, credit placement (r1 l.203-205).** 0 lines.
Move "For derived topological full groups, Grigorchuk and Medynets proved … \cite[Theorem~1.1(3)]{GMpres}." out of the proof, to directly after `\end{corollary}` (r1 l.194). Credit sentences inside proofs read as steps of the argument.

**F8. Word problems, "table on words" (r1 l.198).** 0 lines.
Before: `$\sum_jf_ju^j$, each $f_j$ a table on words, using $uf=(f\circ T^{-1})u$.`
After: `$\sum_jf_ju^j$, each $f_j$ given by a table on the words of some length, using $uf=(f\circ T^{-1})u$.`

**F9. Theorem, consistency (r1 l.50-53 vs abstract r1 l.28).** 0 lines.
- The abstract reads "infinite, simple, finitely generated" and the theorem "infinite, finitely generated, simple". Use one order everywhere.
- The abstract candidate in §4 uses the theorem's order.

## 6. Explicitly not recommended (a referee would call these padding)
- The explicit Kazhdan constant 1/727.
- The K-theory formula.
- The centre formula over F_q.
- The three torsion generators.
- The characters partial theorem.
- LEF growth.
- Sharpness of hypotheses.
- The subsystem sandwich.
- An F_q remark with "the same proof" (false for the binary simplicity text; decision log item 23).
- A Z² SFT question.
- "is C*_r(G_X) MF".

## 7. Phase 2
- At 19:23 only `sk/drafts/sk-draft-minimal/` holds files (minimal.tex and minimal-nocor.tex, in progress). The rich, general and ring directories are empty.
- I will rank them against §2-§5 when they appear (part 2), and review each revision main lands.
