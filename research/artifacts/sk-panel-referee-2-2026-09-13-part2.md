# sk-panel-referee-2, part 2: main's revision 2 and the four drafts ranked (operator algebras, credit, lineage)

Lane sk-panel-referee-2, 2026-09-13. Part 1 is e56b091582.

**What was reviewed.**
- Main at tip e2312fb7f1, as revision e80dcf20a. It is 386 lines and md5-identical to `sk/drafts/rev2.tex`. Line numbers "l." refer to it.
- The drafts: `sk-draft-minimal/minimal.tex` (288 lines), `sk-draft-rich/sk-draft-rich.tex` (448), `sk-draft-general/sk-draft-general.tex` (504) and `sk-draft-ring/sk-draft-ring.tex` (352), each with its changelog.
- panel-referee-1 parts 1 and 2 and panel-referee-3 part 1 were read first, so nothing is reviewed twice without reason.

**Checked independently by this lane today.**
- Crossref:
  - Kerr–Nowak: ETDS 32(5) (2012) 1585–1614, doi 10.1017/S0143385711000575.
  - Kionke–Schesler: "From telescopes to frames and simple groups", J. Comb. Algebra (2024), doi 10.4171/jca/103. Crossref gives no volume or pages.
  - Cortez–Petite: JLMS 78(1) (2008) 1–20, doi 10.1112/jlms/jdn002.
- arXiv abs 2608.05362: Alekseev–Thom, "Centralizers of sofic approximations of Kazhdan groups", submitted 5 Aug 2026.
- Review status, read from main: sk-review-1 parts 9 and 11, sk-review-3 parts 3 and 6, sk-review-4 part 1.

## 0. Verdict
**Main's revision 2 closes both findings of part 1.**
- The Brown bridge (l.168–177) includes sk-referee-2's repair 9c.i: G is shown not residually finite before Kirchberg is applied.
- The Ozawa bibitem carries arXiv:math/0306067 (2003), at l.361.
- The credit record on main is clean. §1 has one optional precision, and one conclusion about the title: the novelty risk of "limits of finite simple groups" reduces to that of the main answer.

**New fact for every draft that poses the LEF embedding question.**
- `lef-groups-embed-in-simple-kazhdan-lef-groups` is ESTABLISHED on main and reviewed PASS by sk-verify-3 (sk-review-3 part 6 §A). The route is by sk-universal-embedding-b (22e2749154), through lamplighter Bernoulli crossed products.
- Consequence: a finitely generated group is LEF iff it is a subgroup of an infinite finitely generated simple Kazhdan LEF group.
- So rich Q2 and general Q2 pose a question that main already answers.

**Ranking** on operator algebras, credit and lineage: (1) main revision 2; (2) general; (3) rich; (4) ring; (5) minimal.

## 1. Main revision 2 (e80dcf20a), line by line

| l. | Item | Verdict |
|---|---|---|
| 40–46 | Brown glossed at first mention as embeddings into unitary groups of McDuff factors embeddable in 𝓡^ω; Ozawa 2003; Pestov 9.1 sofic | VERIFIED; see the note below the table. Together with l.168–177 this resolves part 1 §1.1. |
| 64–68 | EJZ; [GM, Theorem 2.6]; "as in Kassabov's construction" | GM Thm 2.6 VERIFIED against arXiv v4 p.5, verbatim: "The topological full group of any Cantor minimal system is an LEF group" (sk-citations part 2 §5; journal numbering not seen). Kassabov credit accurate: sk-expanders-limits read arXiv:math/0502237, p.5 and Thm 9. |
| 69–72 | Stepanov Theorem 4.4 via pair dependence | SUPPORTED, see §1.1 |
| 72–77 | "Our proof is direct"; Matui Lemma 3.4 and Thm 4.9 | Metadata VERIFIED (part 1); content per sk-novelty's text-layer reading |
| 77–79 | Thom, not RF, not simple | VERIFIED (part 1) |
| 117 | LEF credited to Vershik–Gordon | VERIFIED as attribution (GM Def. 2.5; Pestov v8 l.481) |
| 163–164 | (T) of EL_3(F) ⇒ expanders [Kassabov] | Correct; optional precision in §1.3 |
| 165–166 | [Pestov, Example 4.5 and Theorem 3.3] | VERIFIED (part 1 §1.3) |
| 168–177 | L(G) ⊂ 𝓡^ω; ICC, so not residually finite; L(G)⊗̄𝓡 McDuff, containing G; Kirchberg Thm 1.1; no LLP [Ozawa, p.527] | VERIFIED. Every source is quoted verbatim in sk-operator-algebras §1 and sk-review-2 part 3 §9. `\mathcal R` avoids a clash with the ring R. |
| 247–249 | [GMpres, Theorem 1.1(3)] | VERIFIED (sk-review-2 part 1 §5) |
| 281–287 | Vershik–Gordon; Alekseev–Thom Open problem 6.1 | The paraphrase matches the verbatim problem "Are there examples of finitely presented sofic groups with Kazhdan's property (T) that are not residually finite?" (sk-questions-ggt). Metadata VERIFIED today. |
| 289–291 | GPS for strong orbit equivalence | Metadata per sk-open-5 (Crossref) |
| 293–297 | Origin and authorship | User decision (commit 2050a8eed). What it states is factual. |
| 357–361 | Ozawa bibitem with preprint line | Resolves part 1 §1.2 |

Note on the lineage at l.40–46:
- For an infinite simple group, Brown's form and hyperlinearity are equivalent.
- One direction is the bridge at l.168–177.
- Conversely, G ⊂ U(M) with M ⊂ 𝓡^ω gives G ⊂ U(𝓡^ω), which is hyperlinearity (Pestov's guide, `th:iff`, and Ozawa Prop. 7.1).
- So "Can an infinite simple group with property (T) be hyperlinear? Brown asked this …" is accurate.

### 1.1 The Stepanov sentence (l.69–72) is supported
**Sources.**
- Theorem 4.4 is quoted verbatim from the Springer page images in two independent readings: un-stepanov-credit, and sk-stable-rank-b §2.1, which includes the last lines of the proof on p.2152. panel-referee-1 also read pp.2150–2153.
- The route `subshift-elementary-group-simple-stepanov-proof` and its input `amenable-crossed-products-meet-stepanov-condition-b` are PASS (sk-review-1 part 9 §§1, 3), conditional on the import's quotation.

**The application, checked here.**
- For simple R the only proper ideal is I = 0.
- Condition (a) is trivial, because GL(n,R,0) = 1 = E(n,R,0).
- Condition (b) holds with b = 1, α = (0,r,s)^T and i = j = 1, where a_12 r + a_13 s = 0 comes from pair dependence.
- Part (3) of the conclusion, with I ∈ {0,R}, gives: a normal subgroup N of G lies in the centre of GL_3(R), hence is trivial by the note's scalar step, or N ⊇ E(3,R) = G.

**rev2-changelog open doubt I.3** asked whether E(3,R) must be normal in GL(3,R). It does not arise:
- Theorem 4.4's hypotheses are only (a) and (b) for proper ideals.
- Its conclusion "the normal structure is standard" includes the sandwich (3).
- The printed proof ends by proving (3) for every H normalized by E(n,R).

### 1.2 Title and abstract lead (l.22, l.30–32): no additional novelty risk
- "Limits of finite simple groups" adds finite SIMPLE targets and expanders to LEF.
- A marked limit of finite groups is LEF, because balls agree, and so it is sofic and hyperlinear.
- So any earlier infinite simple Kazhdan marked limit of finite simple groups would already have answered Ozawa's question. sk-novelty found no earlier answer within its bound (parts 1–2).
- The novelty of the title claim therefore reduces to the novelty of the main answer, and no new search is needed.
- The expander construction is credited to Kassabov at l.68 and l.164.
- The title drops the question's key words ("hyperlinear", "sofic"), while the abstract carries them. That is exposition (sk-title-abstract, panel-referee-3), not credit.

### 1.3 Optional precision (0 lines)
- l.163. Current: `groups, and $G$ is LEF. Since $\EL_3(F)$ has property~\textup{(T)}, their`. Replacement: `groups, and $G$ is LEF. Since $\EL_3(F)$ has property~\textup{(T)}~\cite[Theorem~1.1]{EJZ}, their`. It points the reader to the source of (T) for the free algebra. The step "(T) gives expanders for finite quotients" is standard, and Kassabov is credited for the construction.
- MSC (l.25): add 46L10, since l.168–177 now carries von Neumann algebra content.

### 1.4 Questions (l.279–291): both still open on main
- Q1, a finitely presented sofic or hyperlinear simple Kazhdan group: `hyperlinear-fp-infinite-simple-kazhdan-group` is OPEN.
- Q3, rigidity: `subshift-elementary-group-isomorphism-forces-orbit-equivalence` is OPEN. Only partial results have landed:
  - ring isomorphisms of M_m force strong orbit equivalence (sk-rigidity-ring, Theorem R);
  - EL_3 or GL_3 isomorphisms force it for odd q;
  - diagonal-preserving isomorphisms force flip conjugacy (sk-rigidity-intrinsic).

  The q = 2 standardness step is open, so Q3 as printed is accurate.
- **For later revisions:** if an embedding corollary enters the note, state the LEF version (`lef-groups-embed-in-simple-kazhdan-lef-groups`, PASS) and do not pose it as a question.

## 2. The drafts: credit and operator-algebra items only
Group theory belongs to panel-referee-1 and exposition to panel-referee-3.

### 2.1 sk-draft-general (rank 2)
- **G-OA1, 9c.i missing.** At l.181–184, after "which is Brown's formulation.", insert `Since $G$ is infinite and simple, it is not residually finite.` Without it, "So G does not have the factorization property" skips the reason.
- **G-C1, overclaim.** l.96 says "The new step is simplicity" with no Stepanov credit. Take main's l.69–72 sentence (§1.1) and keep the Stepanov bibitem.
- **G-C2, Kerr–Nowak (l.95–96).** "Kerr and Nowak studied residually finite actions and their crossed products" is vague but not wrong, and the metadata is VERIFIED today.
  - The sharper version would be "having finite models is residual finiteness of the action in the sense of Kerr and Nowak". It rests on main's node `rf-subshifts-are-periodic-window-approximable`.
  - No lane has read Kerr–Nowak's definition at source; sk-verify-3 part 1 lists it as unread.
  - Keep the vague sentence or drop it. Do not sharpen it without reading the source.
- **G-C3, answered question.** Q2 at l.381–386 asks whether every f.g. LEF group embeds in an infinite simple Kazhdan LEF group, and main already answers yes (§0).
  - Replace the question by the theorem: "A finitely generated group is LEF iff it is a subgroup of an infinite finitely generated simple Kazhdan LEF group."
  - Credit Kionke–Schesler for the residually finite case without (T).
  - The proof uses lamplighter Bernoulli crossed products, not Toeplitz subshifts. The drafter should measure the line cost.
- **G-C4, Kionke–Schesler bibitem (l.449–452).** Title and DOI are VERIFIED. The locator "Theorem 1.2" is arXiv numbering (= Thm 9.14 in arXiv v1), with journal numbering unchecked. Write "[arXiv:2304.09307, Theorem 1.2]" in the bibitem, or drop the number.
- **G-C5, Cortez–Petite credit (l.300–302).** Metadata VERIFIED, and the sentence is accurate. Krieger's work on Toeplitz subshifts over residually finite groups could be a second credit; its data are not verified here.
- **G-C6, level citation.** l.232, "of $N$~\cite{Stepanov}", credits only a word. Move the credit to the introduction (G-C1); panel-referee-1 G4 agrees.
- **G-C7, Origin paragraph.** l.393–399 predates main's 2050a8eed. Use main's paragraph verbatim.
- **G-C8, abstract (l.36).** "exactly over residually finite groups" should be "exactly over infinite residually finite groups", which matches Proposition (c) (panel-referee-1 G1).
- **Otherwise correct:** the operator-algebra paragraph l.174–185 and the Ore and Kionke–Schesler sentences.

### 2.2 sk-draft-rich (rank 3)
- **R-OA1, ERROR.** l.144–147 read `$R^\omega$` and `$L(G)\mathbin{\bar\otimes}R$`, while in this draft R names the crossed product ring. As printed, the Brown bridge is meaningless. Use `\mathcal R` and define it at first use ("where $\mathcal R$ is the hyperfinite $\mathrm{II}_1$ factor"), as main l.42 does. panel-referee-1 part 2 flagged the notation; I confirm it is an error, not a style choice.
- **R-OA2, 9c.i missing.** At l.149, same fix as G-OA1.
- **R-C1, overclaim.** "The new step is simplicity" at l.62–63 has no Stepanov credit. Same fix as G-C1.
- **R-C2, GM locator.** "[GM, Theorem 2.6]" at l.62 is VERIFIED (§1). This answers panel-referee-1 R2.
- **R-C3, answered question.** Q2 at l.335–336. Same fix as G-C3.
- **R-C4, Kionke–Schesler sentence (l.213–215).** It matches the verbatim abstract, "every finitely generated residually finite (amenable) group embeds into a finitely generated (amenable) LEF simple group". VERIFIED.
- **R-C5, Ore and Cortez–Petite.** Ore Theorem 1 was read from the scan (p.308) by sk-universal-embedding-a, with the DOI through Crossref. Cortez–Petite metadata VERIFIED today, and the credit sentence at l.236–237 is accurate.
- **R-C6:** Origin paragraph outdated (as G-C7), and the level citation at l.198 (as G-C6).

### 2.3 sk-draft-ring (rank 4)
- **N-C1, fine.** l.78–80, "The extraction … follows Stepanov [Lemma 4.3], and local annihilation supplies the noncentral commutators it starts from", is a fair credit. Lemma 4.3 is quoted verbatim in two readings, and un-stepanov-credit classifies the method as prior.
- **N-C2, missing remark.** Add, after Theorem 2 or in the introduction, the remark that for R_X simplicity also follows from Stepanov's Theorem 4.4 via pair dependence (§1.1). Local annihilation and Stepanov's condition (b) are different hypotheses, and whether either implies the other is open, so the remark adds information.
- **N-OA1, fine.** The Brown bridge at l.83–88 is correct, with `\mathcal R`. There is no Kirchberg or LLP sentence. That is acceptable for this architecture, but the reader loses why Ozawa asked.
- **N-C3, fine.** Dropping Matui is appropriate, since the tower pattern is not used.
- **N-C4:** Origin paragraph outdated (as G-C7), and the Ozawa bibitem lacks the preprint line (part 1 §1.2).

### 2.4 sk-draft-minimal (rank 5)
- **M-C1, the largest credit risk among the drafts.** l.57 keeps "The new step is simplicity", and the Stepanov bibitem is deleted. Theorem 4.4 covers simplicity (§1.1), so a referee who knows normal-structure theory will call this an overclaim. Restore main's l.69–72 sentence and the bibitem.
- **M-OA1, fine.** The Brown bridge at l.179–185 is correct (Option A, `\mathcal R`). It has no Kirchberg or LLP sentence, which suits this architecture.
- **M-C2:** Origin paragraph outdated (as G-C7), and the Ozawa bibitem lacks the preprint line.

## 3. Recommendation to main (credit and operator algebras only)
1. **Main revision 2 stands.** From this lane the only possible changes are the optional items in §1.3.
2. **Any draft material brought in** must take the fixes above: G-C1/R-C1/M-C1 (Stepanov), G-OA1/R-OA2 (9c.i), R-OA1 (𝓡), G-C3/R-C3 (no Q2), and G-C7 (Origin).
3. **If an embedding corollary enters the note,** use the LEF iff:
   - `lef-groups-embed-in-simple-kazhdan-lef-groups` (PASS, sk-verify-3);
   - the residually finite case `rf-groups-embed-in-simple-kazhdan-lef-groups` (PASS, sk-verify-3 and sk-verify-4).

   Credit Kionke–Schesler for the residually finite case without (T), and Ore. Credit Cortez–Petite only if the Toeplitz construction is printed.
4. **No further operator-algebra sentence.** The verdict table of sk-operator-algebras stands; C*_r MF and character rigidity remain open.

## 4. Not verified here
- Kerr–Nowak's definition of residually finite actions (no lane has read it at source).
- Journal numbering, all taken from arXiv: Kionke–Schesler Thm 1.2, GM Thm 2.6, Pestov Ex. 4.5 and Thm 3.3, Ozawa p.527. Ozawa is indirect, through Thom's citation.
- Krieger's Toeplitz references.
- The verdicts of sk-review-3 part 4 on Theorem R and Corollary R1 were not re-read. They affect only the partial results listed under Q3.
