# Pestov 9.1: literature background, verified at source (part 3 of 4)

Lane `pc-lit-background`, 2026-09-13. Part 1 has the method and tags; Parts 1–2 have the sources.
This part covers:
- corrections to landed text and docstrings;
- the bound of this pass.

## C. Corrections to landed artifacts

- **C1. `ex-novelty-pestov91-deep-pass-2026-09-12.md` (b), Pestov–Kwiatkowska.** The quote ends in a reconstruction,
  "[s can be hyperlinear]". The printed text, arXiv:0911.4266v4 p. 28, is "...unknown whether finitely generated simple
  Kazhdan groups can be hyperlinear/sofic." The survey was published in 2012; 2009 is the date of arXiv v1.
- **C2. `pestov-9-1-writeup-2026-09-13-part1.md` §4.** It says property (T) was known "only for commutative R or
  under stable range conditions". The source condition is "the stable range of R is at most n" (EJZ v2 p. 2). This
  sharpens the wording and changes nothing else.
- **C3. `pestov-9-1-writeup-2026-09-13-part3.md` §9, row "LEF ⇒ sofic ⇒ hyperlinear".**
  - The precise sources are Elek–Szabó, Math. Ann. 332 (2005): p. 422, "It is known [8],[19],[6] that the LEF-groups
    are sofic", and p. 423, Theorem 2, stated for **countable** groups.
  - Pestov's Theorem 3.3 states it without "countable".
  - The Lean theorems need no countability.
- **C4. Kirchberg, Corollary 1.2(v).** Thom's Remark 1.6 disproves it, so cite only Theorem 1.1 (Part 1 §3). No
  landed text cites (v); this is a standing caution.
- **Confirmed as landed.** Thom Theorem 1.4 (p. 4); EJZ Theorem 1.1 (p. 1); Grigorchuk–Medynets Theorem 2.6 (p. 5);
  Clark–Edie-Michell Corollary 4.6 (p. 7); Steinberg Corollary 3.6 (p. 10); BCFS Theorem 4.1; Dadarlat p. 2,
  Example 3.15(ii) and Proposition 3.19 (pp. 9–10); Ozawa's quote (v2 p. 26, journal p. 527); Pestov 9.1 (v8 p. 21).

## E. Docstring corrections (sent to pc-palomar)

**E1. Pin the arXiv version.** Page numbers depend on the version, and v8 is the galley-corrected one.
- `Palomar/Pestov91Challenge.lean`, module docstring: "(arXiv:0804.3968), Section 9, page 21 of the arXiv PDF" →
  "(arXiv:0804.3968v8), Section 9, page 21 of the arXiv v8 PDF".
- `GroupApproximation/Pestov91/Assembly.lean`, module docstring: "(arXiv:0804.3968, Section 9, p. 21)" →
  "(arXiv:0804.3968v8, Section 9, p. 21)".
- `CrossedProduct`, `Kazhdan`, `KazhdanUnitary` and `LEFHyperlinear` already say v8.

**E2. `Palomar/Pestov91Challenge.lean`, the paragraph after the vocabulary list.**

Current text:

> Taking `F` to run over an increasing exhaustion and `ε → 0`, each of the two local forms produces an injective
> homomorphism into a metric ultraproduct of symmetric groups, respectively of unitary groups, which is Pestov's
> definition; so a group satisfying the block's definitions answers Question 9.1.

Problems:
- "an increasing exhaustion" presupposes a countable group, while `G : Type` is arbitrary.
- The paragraph cites no theorem.

Proposed text:

> Pestov defines sofic and hyperlinear groups as subgroups of metric ultraproducts of symmetric, respectively
> unitary, groups over an arbitrary index set and ultrafilter (arXiv:0804.3968v8, Definitions 3.1 and 3.2), and proves
> finite-set criteria (Theorems 3.5 and 3.6) that ask multiplicativity only when `g`, `h` and `g * h` lie in `F`, and
> separation `1/4`. The block's two local forms imply those criteria, so a group satisfying the block's definitions is
> sofic, respectively hyperlinear, in Pestov's sense and answers Question 9.1.

Why the block implies Theorems 3.5–3.6. Given ε, apply the block with ε' = min(ε²/2, 1/2).
- **Multiplicativity.** In the unitary case the defect is `hsDistSq ≤ ε'`, so ‖·‖₂ ≤ √ε' < ε. In the permutation
  case the Hamming defect is ≤ ε' < ε.
- **The identity.** Take g = h = e. By invariance of the distance, ‖σ(e) − I‖ equals the multiplicative defect at
  (e, e), which is below ε.
- **Separation.** `hsDistSq ≥ 2 − ε' ≥ 1`, and the Hamming distance is ≥ 1 − ε' ≥ 1/2. Both exceed 1/4, respectively
  1/16 squared.
- **Converse reductions.** The development also proves `isSofic_iff_productRestricted`, `isSofic_iff_weak_quarter`
  and `isHyperlinear_iff_productRestricted`. A positive answer does not need them.

**E3. `GroupApproximation/Pestov91/RingSimple.lean`, module docstring (owner pc-ring-simple).**
- **Current:** "a special case of the simplicity criterion of Brown, Clark, Farthing and Sims (arXiv:1204.3127)".
- **Why it is wrong.** BCFS Theorem 4.1 is about the **complex** Steinberg algebra (Part 2 §8a). The module works
  over any field `K`, and the witness uses `ZMod 2`, so it is not a special case of BCFS.
- **Proposed:** "the argument behind the simplicity criterion for Steinberg algebras of effective minimal ample
  groupoids: Brown, Clark, Farthing and Sims over ℂ (arXiv:1204.3127, Theorem 4.1), and Clark and Edie-Michell
  (arXiv:1403.4684, Corollary 4.6) and Steinberg (arXiv:1408.6014, Corollary 3.6) over any field".

**E4. Optional credits, not errors.**
- `Kazhdan.lean` and `CrossedProductFG.lean` name "the Ershov--Jaikin-Zapirain theorem" without a reference. Add
  "(Invent. Math. 179 (2010), arXiv:0809.4095v2, Theorem 1.1)".
- `LEFHyperlinear.lean` could credit Elek–Szabó (Math. Ann. 332 (2005)): LEF ⇒ sofic "is known" (p. 422), and
  countable sofic groups are hyperlinear (Theorem 2, p. 423). The Lean theorems need no countability.

**Checked, no change needed.**
- The verbatim 9.1 quote in the challenge (v8 p. 21).
- "Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Definition 1.1.3" in the challenge and in `KazhdanUnitary.lean`
  (book p. 33, with the strict inequality of Definition 1.1.1).
- "Bull. Symbolic Logic 14 (2008) 449–480" (Crossref: vol. 14, no. 4).
- The Solution docstring contains no literature claim.

## B. Bound of this pass

- **Read as page images:**
  - Pestov v8 pp. 21, 27;
  - Ozawa v2 p. 26;
  - Kirchberg pp. 551–552;
  - Thom v1 pp. 3–4;
  - EJZ v2 pp. 1–2;
  - Bekka–de la Harpe–Valette book pp. 32–33 (authors' preprint);
  - Grigorchuk–Medynets v4 p. 5;
  - BCFS v2 p. 7;
  - Clark–Edie-Michell v1 p. 7;
  - Steinberg v2 p. 10;
  - Dadarlat v2 pp. 2, 10;
  - Pestov–Kwiatkowska v4 p. 28;
  - Cornulier v2 p. 2;
  - Alekseev–Thom v1 pp. 17–18;
  - Elek–Szabó pp. 422–423;
  - Jacobs–Keane p. 123.
- **Read only in the LaTeX source or the text layer:**
  - Pestov Definitions 3.1–3.2 and Theorems 3.3–3.6;
  - BCFS Theorem 4.1 and its abstract;
  - Dadarlat Example 3.15 and p. 1;
  - Capraro–Lupini (grep of one file);
  - Caprace–Rémy abstract and introduction;
  - the Alekseev–Thom abstract.
- **Bibliographic data** from Crossref records, except Vershik–Gordon (no record).
- **Not reached:**
  - the Bull. Symbolic Logic, Internat. J. Math. and Adv. Math. journal texts;
  - the printed Bekka–de la Harpe–Valette and its conventions page;
  - Vershik–Gordon; Gromov 1987; Ceccherini-Silberstein–Coornaert Cor. 7.5.11;
  - Jacobs–Keane §3 against the period-doubling sequence;
  - `[CGP]` §5.4 behind Cornulier's sentence.
- **Novelty.** This pass did not redo the novelty search; see the files named in Part 1. Nothing read here names an
  earlier infinite simple sofic or hyperlinear Kazhdan group. The post-2008 texts that mention the question
  (Pestov–Kwiatkowska 2012) call it open. The August 2026 list of known examples (Alekseev–Thom) names no simple one.

*The yaml rows are in Part 4.*
