# sk-panel-referee-2, part 1: operator algebras, credit and lineage (2026-09-13)

Lane sk-panel-referee-2: a hostile referee at the Annals/Inventiones/JEMS standard, with emphasis on operator algebras, credit and lineage.

- **Subject:** main's `simple_kazhdan_sofic_group.tex` at tip 596a737338, which is revision 1 (landed 5b1890ce6c), blob 68f85b3d78, md5 8e04b341…, 292 lines. Line numbers below refer to it.
- **Read:**
  - the landed tex;
  - sk-citations (proposal, parts 1–2);
  - the proposals of sk-operator-algebras, sk-questions-oa, sk-novelty and sk-questions-ggt;
  - sk-review-2 parts 1–3;
  - the rev1 changelog, rev2-decisions.md, and the sk-characters proposal (head).
- **Checked independently by this lane:**
  - Crossref for Matui: IJM 17(2) (2006) 231–251, doi 10.1142/S0129167X06003448, confirmed.
  - Crossref for Grigorchuk–Medynets 2018: J. Algebra 500 (2018) 46–68, doi 10.1016/j.jalgebra.2016.10.027, confirmed.
  - The arXiv e-print of Pestov 0804.3968v8, grepped on MSI (`hypsof.tex`).
- **Out of scope:** the group theory is re-derived by sk-panel-referee-1, and exposition belongs to sk-panel-referee-3.

## 0. Verdict
- **Errors:** no operator-algebraic, credit or lineage claim on main is false.
- **What blocks acceptance from this side:**
  - a GAP in a headline claim, Brown's printed form (§1.1);
  - one small citation inconsistency (§1.2);
  - residual lineage risk, which the text already words around (§1.4).
- **After the §1.1 fix:** "answers all three forms" is fully supported, and a top-journal referee will find the credit record clean.

## 1. Blocking or near-blocking

### 1.1 GAP: Brown's question as printed is not reached (l.37–41; abstract l.30–32)
Brown, §11 Question 7 (arXiv v1 and v3, verified by sk-citations): "Can an infinite, simple, discrete group with Kazdan's property T be embed into the unitary group of an R^ω-embeddable McDuff factor?"

The note proves hyperlinearity and then says (l.41) "answers all three forms". The reader has to supply four steps:
- hyperlinear ⇒ L(G) ↪ R^ω (Ozawa, Prop. 7.1);
- ICC ⇒ L(G) is a II_1 factor;
- L(G)⊗̄R is a separable McDuff factor embeddable in R^ω;
- G ⊂ U(L(G)⊗̄R).

"R^ω is McDuff" does not do it, because R^ω is not separable (sk-review-2 part 1 §2.i). An operator-algebra referee stops here.

**Fix: the Brown bridge.** Main decided this (rev2 item 17), and sk-referee-2 PASSed it with repair 9c.i. Proposed text, replacing l.133–134, with 9c.i applied and checked against the doctrine:
```latex
So $G$ is LEF. LEF groups are sofic, and sofic groups are
hyperlinear~\cite[Example~4.5 and Theorem~3.3]{Pestov}. Then $L(G)$
embeds in $R^\omega$~\cite[Proposition~7.1]{Ozawa}. As $G$ is infinite
and simple, its nontrivial conjugacy classes are infinite, so
$L(G)\mathbin{\bar\otimes}R$ is a McDuff factor. It embeds in $R^\omega$,
and its unitary group contains $G$, as Brown asked. An infinite simple
group is not residually finite, so by Kirchberg's
theorem~\cite[Theorem~1.1]{Kirchberg} $G$ does not have the
factorization property, and $C^*(G)$ does not have the local lifting
property~\cite[p.~527]{Ozawa}.
```
Bibitem. sk-review-2 part 1 confirmed the data through Crossref (issue 1, pp. 551–563) and part 3 read p. 552:
```latex
\bibitem{Kirchberg}
E.~Kirchberg, \emph{Discrete groups with Kazhdan's property~\textup{T} and
factorization property are residually finite},
Math. Ann. \textbf{299} (1994), 551--563.
\doi{10.1007/BF01459798}.
```
- **Checks, every sentence:**
  - Ozawa Prop. 7.1 is verbatim in sk-operator-algebras §1.
  - ICC holds for infinite simple groups (sk-review-2 2b).
  - ICC gives a II_1 factor, and a II_1 factor tensored with R is McDuff.
  - The tensor embedding is the one in sk-operator-algebras §2.1.
  - An infinite simple group has no nontrivial finite quotient, so it is not residually finite.
  - Kirchberg Thm 1.1 (verbatim, p. 552): "A discrete group with property (F) and property T is residually finite."
  - Ozawa after Thm 7.4 (verbatim): "By the above theorem, the full C*-algebra C*Γ of such a group Γ cannot have the LLP."
- **Length and trade-off:** +8 text lines and +5 bibliography lines. The headline claim becomes checkable, and the reader learns Ozawa's reason for asking, at the cost of one classical citation. Nothing in the proof of Theorem 1 changes.
- **No priority claimed:** Thom (arXiv:0810.2180, Introduction) already gave hyperlinear Kazhdan groups whose C*-algebra lacks the LLP. The text cites Ozawa's remark for the implication, so it claims no priority. The Thom sentence at l.65–67 should stay before it, as it does now.
- **Optional, +1 to +2 lines.** I lean toward including it, but it is main's call. After "as Brown asked", add: "By Kirchberg's Corollary~1.2 it does not embed in the unitary group of the hyperfinite factor $R$ itself." Support:
  - verbatim p. 552: "(iv) ⇒ (ii) ⇒ (i) are true in full generality";
  - (ii) ⇒ (i) together with Thm 1.1 excludes U(R) for every non-RF Kazhdan group;
  - this shows why Brown asked for a McDuff factor, and it answers his parenthetical comparison with Robertson.
- **MSC:** if §1.1 lands, add 46L10.

### 1.2 Ozawa: year and bibitem (l.39, l.264–267)
- **The inconsistency:** the text says "Ozawa in the hyperlinear form in 2003~\cite[p.~527]{Ozawa}", and the bibitem gives the 2004 journal.
  - The date 2003 is arXiv:math/0306067 v1, 3 Jun 2003 (sk-citations part 1).
  - The p. 527 locator refers to the journal, and is checked only indirectly, through Thom's citation of that page.
- **Fix** (0 text lines, +1 bibliography line): add the arXiv id so that the date can be traced.
```latex
\bibitem{Ozawa}
N.~Ozawa, \emph{About the QWEP conjecture},
Internat. J. Math. \textbf{15} (2004), 501--530.
\href{https://arxiv.org/abs/math/0306067}{arXiv:math/0306067} (2003).
\doi{10.1142/S0129167X04002417}.
```
- **Residual risk:** no lane obtained the IJM PDF. The question sentence is immediately followed by the LLP sentence Thom cites at p. 527, so the risk is low.

### 1.3 Pestov locator (l.133–134): VERIFIED, and a lane's contrary remark is wrong
- **The contrary remark:** sk-citations part 2 §3 says "The guide never mentions LEF." This is FALSE.
- **The source, arXiv v8 `hypsof.tex`, grepped on MSI today:**
  - l.481: "So is every {\em LEF group} $G$ in the sense of Vershik and Gordon \cite{VG}, defined by the property that one can embed every finite $F\subseteq G$ into a suitable finite group so as to preserve the partial multiplication."
  - l.483–484, right after it, in §4 "Examples": `\begin{example}` "Every \under{initially subamenable} group is sofic."
  - l.277: "\begin{theorem}[Elek and Szab\'o \cite{ES}] Every sofic group is hyperlinear."
  - The environments share the section counter (l.17–28). The number "4.5" follows sk-referee-2's count; I did not recount.
  - The v8 bibitem VG (l.1240) agrees with the note's Vershik–Gordon translation data.
- **Residual:** the BSL numbering was not seen. v8 "incorporates minor corrections made in the BSL galley proofs", so the risk is low.
- **No change recommended.** If a referee objects to citing a survey, the primary alternative is Elek–Szabó, Math. Ann. 332 (2005), p. 422 and Thm 2.

### 1.4 Lineage: residual risk, and how the text already words around it
- **Earliest formulation located:** Brown 2001. Not opened by any lane:
  - Kirchberg, Invent. Math. 112 (1993) 449–489 (the EUDML page timed out twice today);
  - Robertson, Math. Ann. 296 (1993) 547–555, paywalled. Brown compares Q7 with Robertson's non-embedding theorem, which suggests Robertson proved an obstruction rather than posing the question;
  - Brown's Mem. AMS expansion, and the Brown–Ozawa book (2008).
- **Wording:** l.37–38 says "Brown asked this … in 2001". That is true as stated and claims no priority, so keep it. Never write "first asked".
- **Optional:** Pestov–Kwiatkowska (arXiv:0911.4266, p. 28) restates the question for finitely generated simple Kazhdan groups (sk-questions-ggt). It is not needed.

## 2. Credit record on main: line by line

| l. | Claim | Verdict |
|---|---|---|
| 37–40 | Brown §11 Q7 (2001); Ozawa p. 527 (2003); Pestov Open question 9.1 adds sofic | VERIFIED. Pestov v8 wording: "Let G be an infinite simple group with Kazhdan's property (T). Can it be hyperlinear (sofic)?" Brown needs §1.1. |
| 56–57 | (T) from EJZ Thm 1.1 | VERIFIED: arXiv v2, finitely generated associative ring with 1, n ≥ 3. |
| 57–59 | periodic sequences "as in Grigorchuk and Medynets" | OK. It matches sk-citations P1: GM use periodic approximation to prove LEF (Thm 2.6), and the wording no longer assigns the technique to them. |
| 62–65 | Matui Lemma 3.4 and Thm 4.9, "in the same way" | Metadata VERIFIED here (Crossref). The content follows sk-novelty (text layer); I did not re-read it. |
| 65–67 | Thom: not RF, not simple | VERIFIED. The theorem number is dropped (sk-questions-ggt P1). |
| 67–70 | f.p. LEF ⇒ RF [VershikGordon]; the question | Attribution confirmed through Kionke–Schesler and Pestov v8 l.481; the VG paper itself was not opened. Optional credit: a positive answer would also answer Alekseev–Thom Open problem 6.1 (arXiv:2608.05362), quoted verbatim in sk-questions-ggt. |
| 107 | LEF [VershikGordon] | VERIFIED as attribution: GM Def. 2.5 and Pestov v8 l.481 both credit VG. |
| 133–134 | Pestov Example 4.5 and Theorem 3.3 | VERIFIED (§1.3). |
| 180–181 | "the level $J$ … of $N$~\cite{Stepanov}" | Acceptable. Stepanov uses "level" in this sense (sk-stable-rank-b quotes "full congruence subgroup of level I"). The argument is self-contained, so the citation only credits the term. |
| 203–205 | GMpres Thm 1.1(3) | VERIFIED: metadata here, statement by sk-review-2 part 1 §5 from arXiv:1508.04454. |
| 210 | Morse–Hedlund for Sturmian subshifts | Metadata VERIFIED; standard attribution. The note does not use the complexity bound that sk-open-3 dates to 1938. |
| 220–226 | Origin and authorship | Factual after main's fix: "Codex (OpenAI) shortened an earlier version, and Claude revised this one." |

## 3. What would make this astonishing (operator-algebra and credit view)
- **Where the note stands:** it answers a named question operator algebraists know (Ozawa 2003, Pestov 9.1), with a four-page proof. A referee will first ask whether that is enough for Inventiones or JEMS.
- **Two cheap sentences** raise it for the operator-algebra reader, and both are verified:
  - Brown's printed form, with an explicit McDuff witness, and optionally why that witness cannot be hyperfinite (§1.1);
  - the LLP consequence, which was Ozawa's own motivation.
- **Do not add:**
  - "L(G) is a (T) factor in R^ω": L(SL_3(Z)) already is one;
  - MF or quasidiagonal trace statements: they cost definitions and answer no printed question;
  - "C*_r(G) has a unique trace": routine.

  sk-operator-algebras' verdict table agrees.
- **Results that would change the paper.** Other lanes own them; state nothing unreviewed:
  - the RF embedding corollary, which needs Kionke–Schesler credit for the version without (T);
  - expanders converging to G_X, which needs Kassabov credit;
  - full character rigidity: open, with only the partial, unreviewed Theorem A of sk-characters.
- **Abstract lineage** (for sk-title-abstract). "the question of Brown and Ozawa whether an infinite simple Kazhdan group can be hyperlinear" attributes the word "hyperlinear" to Brown, whose printed form is the McDuff embedding. With §1.1 in the text this is an acceptable simplification, and my verdict is to keep it.

## 4. Phase 2
A watcher polls every 10 minutes, for up to 3 hours, on `sk/drafts/sk-draft-*/*.tex` and on main's tex blob. Part 2 will rank the drafts on operator algebras, credit and lineage, and review any new revision main lands.
