# sk-draft-minimal: the shortest complete answer (candidate paper, self-assessment)

Lane sk-draft-minimal, 2026-09-13. Architecture from ROSTER-D: theorem, proof, at most one corollary, at most 3 pages.

## The draft
- **Where:** `sk/drafts/sk-draft-minimal/minimal.tex` (coordinator scratchpad; not at the repo root), with `changelog.md` alongside.
- **Size:** 288 source lines, md5 d6b27d4a….
- **Compile:** MSI, pdflatex three passes. 3 pages, 0 errors, 0 overfull boxes, 0 undefined references or citations. There are 2 underfull boxes in the bibliography, badness 1132 and 1389.
- **Page 3 is full:** 627.5pt of 628.7pt are used. Any added line makes it 4 pages.
- **Base:** main's revision 1 (5b1890ce6c, 292 lines, 4 pages).

Content:
- **Theorem:** G_X = EL_3(LC(X,F_2)⋊Z) is infinite, f.g., simple, Kazhdan and LEF, so it is sofic and hyperlinear.
- **Proof:** EJZ; periodic words; one commutator inside a copy of GL_d(F_2); covering by translates.
- **Brown's printed McDuff form:** one paragraph after the proof, with a sentence on EL_n for n ≥ 3.
- **One corollary:** WP(G_X) ≡_T L(X). Every degree occurs, so there are continuum many pairwise nonisomorphic G_X.

## Changes against main (full list in changelog.md)
1. The intro sentence "The following construction answers all three forms positively." is deleted.
2. The EL_n clause moves from the theorem statement to one sentence after the proof. The proof remark for n = 3 is deleted.
3. The display of R is inlined.
4. "every word of X occurs in x_{[0,∞)}" (precision).
5. ε_ab = u^a e_V u^{-b}. The product rule is one line: e_V u^c e_V = e_V e_{T^cV} u^c = 0 for 0<|c|≤2w.
6. The level ideal J and the Stepanov citation are replaced by two commutators and the covering identity (sk-simplicity-short-b text). The Stepanov bibitem is deleted.
7. New: Brown's formulation. L(G) ⊂ R^ω; G is ICC; G ⊂ U(L(G)⊗̄R), and L(G)⊗̄R embeds in R^ω.
8. Word-problem repairs 4.i and 4.ii from sk-review-2 part 1: "There are continuum many degrees" is restored, and the cylinder-indicator wording is used.

Net: −4 source lines and −1 page against main.

## Strongest claim
An infinite, finitely generated, simple Kazhdan group that is LEF, for every infinite minimal subshift. The proof is two pages, self-contained apart from EJZ and the simplicity of GL_d(F_2). It answers Brown (2001), Ozawa (2003) and Pestov (2008) as printed, including Brown's McDuff formulation. It also gives continuum many examples, with every Turing degree as the word-problem degree.

## Weakest points
- **Novelty rests on a bounded search** (sk-novelty: about 20 web searches, arXiv and Crossref; no MathSciNet or zbMATH). The residual risk is a soficity theorem for Kac–Moody lattices or Gromov monsters, or an unindexed 2026 preprint.
- **The Brown paragraph uses three standard facts without a reference:**
  - infinite simple ⇒ ICC;
  - M⊗̄R is McDuff;
  - M ⊂ R^ω ⇒ M⊗̄R ⊂ R^ω.

  A referee may want a citation for the last one.
- **F_2 is essential to this proof text.** It uses the unit trick LC(X,F_2)^× = {1} and GL_d(F_2) = PSL_d(F_2). Nothing about F_q is claimed, so there is no error, but a generality-minded referee will ask. The F_q route with roots e_ij(e_C u) exists on main.
- **Page 3 has no slack.** A referee request for any extra sentence costs a fourth page.

## What a referee will attack
- **"LEF ⇒ sofic ⇒ hyperlinear" citations.** Pestov Example 4.5 is "initially subamenable ⇒ sofic"; the LEF case is the sentence just before it, from arXiv v8, and the journal numbering is not checked. Elek–Szabó (Math. Ann. 332) would be the primary source.
- **Unconfirmed locators.**
  - Matui Lemma 3.4 / Theorem 4.9 and GMpres Theorem 1.1(3): sk-novelty read them from the text layer, and the DOIs came through the fetch tool, not Crossref.
  - Ozawa Proposition 7.1: verified from the arXiv e-print; the journal version is not checked.
- **The Matui credit sentence** ("in the same way") may be read as overstating the analogy. The mechanisms are alternating groups on towers versus GL_d(F_2) on towers.
- **Word-problem proof.** "A table on words" is informal. The upper-bound algorithm is correct, but a computability referee may want the window bookkeeping spelled out.

## Review status of what the draft uses
- **PASS:**
  - the constant-tower simplicity text and the covering step (sk-review-1 parts 1 and 3);
  - LEF Replacement B (part 2);
  - sk-arbitrary A2 and A8 (part 7);
  - the Brown witness node (sk-review-2 part 3);
  - the continued-fraction claim and the word-problem LaTeX, with repairs applied (sk-review-2 part 1);
  - the GM word-problem citation (sk-review-2 part 1).
- **Not separately reviewed:**
  - this draft's wording of the Brown paragraph;
  - the reassembled simplicity paragraphs, whose pieces are PASSed but whose exact sentences are new;
  - the bibliographic locators listed above.

## Recommendation for main
Use this as the "short" end of the range. If main adds Option B (Kirchberg/LLP) or a questions paragraph, the note goes to 4 pages, and page count stops being the argument. Then the choice is the rich or general draft on reader merits.
