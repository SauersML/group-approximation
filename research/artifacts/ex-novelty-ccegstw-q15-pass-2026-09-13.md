# CCEGSTW Question 1.5: open-status and priority pass (2026-09-13)

Lane `ex-novelty`, at main's request.
- **Target:** `ccegstw-q15-amenable-factorial-ii1-has-gamma`. It is refuted, unreviewed, at d1913c9e9e by
  `amenable-factorial-ii1-tracially-complete-without-gamma`, landed by lane ex2-tw-unsplittable-tails.
- **Routes:** `q15-negative-via-toms` (route 1) and `q15-negative-via-bauer-pauli` (route 2).

## Verdict

- **Route 1 is not new mathematics.** The negative answer to CCEGSTW Question 1.5 follows at once
  from four ingredients:
  - Toms's Theorem 5 (arXiv:2606.12188v2; Theorem 6 in v1);
  - CCEGSTW's own Proposition 5.20;
  - their remark after Theorem 1.2 that tracial completions of nuclear algebras are amenable;
  - their Proposition 3.23(iv) and Definition 3.8.
- **No source we could reach records this consequence.**
  - CCEGSTW v5 (29 Jul 2026) and v6 (7 Aug 2026) were both posted after Toms v1 (10 Jun) and v2 (26 Jul).
    v6 still lists the class as "Open" and does not cite Toms.
  - Toms v1 and v2 claim STW Question XIX and never mention Question 1.5.
  - Kessinger–Toms (26 Jul 2026) does not mention it.
  - Semantic Scholar and OpenAlex list no works citing Toms's paper.
- **Exact status.** The answer is a consequence of Toms's theorem that, within the bound below, nobody has
  recorded. We cannot claim that nobody noticed: the authors of either paper may know it privately.
- **Route 2 is a separate question.** The Pauli completion (Bauer designated traces, no halving
  projection at all) is repo-built and unreviewed. Its priority status is the BBSTWW Question 3.14
  verdict in `research/artifacts/ex-novelty-r-fibre-w-bundle-pass-2026-09-13.md`.

## Sources read

MSI copies are under `/scratch.global/sauer354/ex/ex-novelty/q15/`. Each paper was downloaded as arXiv
source. The three main papers were also downloaded as PDF and converted to text with ghostscript, to
get their printed numbers.
- **CCEGSTW (Carrión, Castillejos, Evington, Gabe, Schafhauser, Tikuisis, White).** *Tracially
  complete C\*-algebras*, arXiv:2310.20594v6.
  - History: v1 31 Oct 2023, v2 21 Feb 2024, v3 23 Feb 2024, v4 15 May 2024, v5 29 Jul 2026,
    v6 7 Aug 2026.
  - Comment: "138 pages. Small edits made. Accepted to Memoirs of the AMS".
  - v6 is the latest version. v5 was not downloaded separately.
- **A. S. Toms,** *Schubert Calculus and uniform property Γ*, arXiv:2606.12188.
  - v1 10 Jun 2026; v2 26 Jul 2026, "substantially tightened and simplified final section".
- **E. Kessinger and A. S. Toms,** *Subquadratic growth and uniform property Γ*, arXiv:2607.23817v1
  (26 Jul 2026).
- **C. MacMahon,** *1-Bounded Entropy for C\*-Algebras*, arXiv:2608.15409 (15 Aug 2026).
- **Grepped, all posted before Toms v1:** the latest sources of arXiv:2604.24206 (Evington–Tikuisis),
  2604.24682 (Vaccaro) and 2605.21655.
- **Indexes:**
  - Semantic Scholar citations of 2606.12188: none. OpenAlex W7164321724: `cited_by_count` 0.
  - Semantic Scholar citations of 2310.20594: 12 rows. The newest is 2605.21655 (20 May 2026).
  - arXiv search, newest first, for "uniform property", "tracially complete" and "property Gamma".

## (a) The question and its printed status

- **Numbering.** The PDF prints "Question 1.5"; the source label is `Q:semidiscreteGamma`. A naive count of
  source environments gives 1.4, because it misses the `restatable` Theorem 1.4.
- **Verbatim** (v6, Section 1.4, p. 19): "Question 1.5. Does every amenable type II1 factorial tracially
  complete C∗-algebra satisfy property Γ?"
- **Just before it:** "Thus the following question is fundamental; by [CETW, Theorem 5.6] a positive
  answer would resolve the Toms–Winter conjecture."
- **Just after it** (p. 20):
  - "When the designated set of traces X is reasonably small, Question 1.5 has a positive answer; ... We
    give a positive answer when ∂eX is compact and zero dimensional as Proposition 5.28."
  - "... It remains mysterious whether one should expect a positive answer in general, or whether
    strict comparison for a C∗-algebra A would imply property Γ for its uniform tracial completion –
    which, if true, would establish the Toms–Winter conjecture."
- **Regularity table** (v6 p. 20), rows verbatim:
  - "Finite amenable von Neumann algebra | Automatic"
  - "Amenable factorial II1 tracially complete C∗-algebra | Open"
  - "Simple separable non-elementary nuclear C∗-algebra | Not automatic"
- **Toms is not cited in v6.** Grep of the whole v6 source: its bibliography has one Elliott–Toms item and
  five Toms items (To08, To09, TWW15, TW07, TW09). None is arXiv:2606.12188, and "Schubert" does not
  occur.

## Route 1 against the sources

**Toms**, printed numbers from the PDF text:
- **v2 Theorem 1:** "There is a unital simple separable nuclear non-elementary C∗-algebra without uniform
  property Γ."
- **v1 Theorem 1:** "There is a unital simple separable AH C∗-algebra without uniform property Γ."
- **v2 Theorem 5,** "The simple point-evaluation limit has no uniform property Γ": "Let B be the simple AH
  algebra obtained in Proposition 4. Then B does not have uniform property Γ. In particular, there is a
  simple, separable, unital, nuclear AH algebra without uniform property Γ."
  - Its proof begins: "By Proposition 4, the algebra B is a simple, separable, unital, nuclear,
    non-elementary AH algebra."
- **Numbering across versions.**
  - v1 numbers the same theorem 6. v1 Theorem 5 is "Simplicity from scheduled point evaluations".
  - v2 comments out v1's Proposition 2.
  - Kessinger–Toms cite the theorem as "[Theorem 6]", the v1 number.
- **Definition used.** Toms takes uniform property Γ from CETWW, Invent. Math. That is the same [26] as in
  CCEGSTW Proposition 5.20: "J. Castillejos, S. Evington, A. Tikuisis, S. White, and W. Winter. Nuclear
  dimension of simple C∗-algebras. Invent. Math., 224(1):245–290, 2021."

**CCEGSTW v6**, as printed:
- **Definition 3.8:** "A tracially complete C∗-algebra (M,X) is of type II1 if πτ(M)'' is a type II1 von
  Neumann algebra for every τ ∈ X."
- **Proposition 3.23(iv)** (source): "(A^X, X̃) is factorial if and only if X is a face in T(A)."
- **After Theorem 1.2:** "In particular, via Connes' theorem, the uniform tracial completion of a nuclear
  C∗-algebra is amenable as a tracially complete C∗-algebra."
- **Proposition 5.20:** "Let A be a separable C∗-algebra with T(A) compact. Then A has uniform property Γ
  as in [26, Definition 2.1] if and only if its tracial completion with respect to T(A) has property Γ
  in the sense of Definition 5.19."

**Assembly.** This is the lane's route, re-checked. Let B be Toms's algebra: it is unital and separable,
so T(B) is compact, and take the completion (B^u, T(B)).
- **Factorial:** by 3.23(iv), since T(B) is a face of itself.
- **Amenable:** by the remark after Theorem 1.2.
- **Type II1:**
  - A type I_n summand of πτ(B)'' composed with a character of its centre gives a unital
    representation B → M_n.
  - Its kernel is a proper ideal, so it is zero by simplicity, and then B would be finite-dimensional.
  - I re-derived this step and it holds.
- **No property Γ:** by Proposition 5.20 and Toms's Theorem 5.

Every step is either a quotation or a few lines of argument.

**Toms's own framing.**
- Toms's Section 6 already works inside the CCEGSTW framework. It says that "uniform property Γ" gives
  CPoU for the completion [CETW, Theorem 4.6], then compares projections in type II1 factorial tracially
  complete algebras with CPoU [CETW, CCEGSTW, ET].
- His obstruction is a pair of projections in M_k(B^u) with equal designated traces that are not
  equivalent, so it is a statement about the completion itself.
- He states the conclusion only as failure of uniform property Γ for B.

## (b) Has anyone drawn the consequence?

- **Toms v1.**
  - "This is laid out explicitly as Question XIX of [STW:99problems], which we resolve here."
  - "Tracially complete" appears only in Section 6's appeal to Evington–Tikuisis. The words "Question",
    "Connes" and "W*" occur only in historical or other senses, with no reference to Question 1.5 or to
    the table.
- **Toms v2.**
  - "... which we resolve negatively here".
  - Intro: "This at least suggests the presence of a 2-norm version of the Toms-Winter regularity
    framework in tracially complete C∗-algebras. We defer any finer prognostication for the time being."
  - CCEGSTW is cited 5 times: Definition 3.19, Kaplansky density, and projection comparison. It is never
    cited for Question 1.5 or Proposition 5.20.
- **Kessinger–Toms 2607.23817v1:** "The second author's recent construction of a simple unital separable AH
  algebra without uniform property Γ shows that the presence of uniform property Γ in simple separable
  nuclear C∗-algebras is not automatic and that its failure appears to depend on the presence of
  quadratic dimension growth [Theorem 6]." There are no other hits for "tracially complete", "Question"
  or "CCEGSTW".
- **CCEGSTW v6:** the table still says "Open", and there is no Toms citation.
- **MacMahon 2608.15409:** no hit for 2606.12188, "Schubert", "Toms" or "Question 1.5".
- **arXiv searches:** after 10 Jun 2026 the only uniform-Γ or tracially-complete papers found are Toms v2,
  Kessinger–Toms, CCEGSTW v5 and v6, and MacMahon.
- **Repo-internal record.**
  - The Toms plus Proposition 5.20 connection first landed at d1913c9e9e (09-13 10:39 CDT), then in
    `central-unit-division-without-gamma-exists-via-toms` at 6bfae2597 (10:50).
  - Earlier, `research/artifacts/toms-winter-tracial-ultrapower-comparison-2026-09-12.md` quoted Question
    1.5 and called CETW Question C "refuted since by Toms" without drawing the consequence.
  - Toms's counterexample itself was imported on 2026-08-30 (b5fd531f0,
    `toms-ah-counterexample-to-uniform-gamma`).

**Bound.**
- Web search budget exhausted, and Google Scholar, MathSciNet and zbMATH not reached.
- Memoirs AMS version not seen, and CCEGSTW v5 not downloaded.
- Citation indexes lag for July–August 2026 preprints.
- Talks and private communication are not searchable.

## (c) Credit a public statement should carry

**Suggested wording:**
"CCEGSTW Question 1.5 (arXiv:2310.20594v6) has a negative answer. This follows at once from Toms's simple
nuclear AH algebra without uniform property Γ (arXiv:2606.12188v2, Theorem 5) and CCEGSTW's Proposition
5.20. The tracial completion of Toms's algebra over its trace simplex is an amenable, factorial, type II1
tracially complete C∗-algebra without property Γ. The mathematics is Toms's and CCEGSTW's; we record the
consequence, which the sources we checked do not state."

**Rules for any statement:**
- Do not call route 1 a new theorem, a "first answer", or a solution by the repository or by Claude.
- Cite Toms in a version-stable way:
  - both versions' Theorem 1 for existence;
  - v2 Theorem 5 (v1 Theorem 6) for the explicit algebra.
- Credit CETWW [26, Definition 2.1] for uniform property Γ, and Connes, through CCEGSTW, for amenability.
- **What stays open, as the lane's node says:**
  - strict comparison implying Γ, which is Toms–Winter itself and untouched, since Toms's algebra fails
    strict comparison (`toms-gamma-counterexample-fails-strict-comparison`);
  - the modified Toms–Winter variant with tracial divisibility.
- Route 2 claims wait for review.
  - They are stronger in form. The designated traces form a Bauer simplex, where CCEGSTW Proposition 5.28
    gives positive answers for zero-dimensional ∂eX; the paragraph after Question 1.5 announces
    finite-dimensional ones.
  - The failure also happens already at S = {1}, k = 2. Toms's v1 introduction says his non-simple
    algebra has constant-trace projections for every dyadic value, so his failure is about centrality.

**Lane nodes checked, nothing blocking.**
- Printed numbers match: Question 1.5, Theorem 1.2, Definition 3.8, Proposition 3.23(iv),
  Definition 5.19, Proposition 5.20, Proposition 5.28, [26], and Toms v2 Theorem 5 and Proposition 4.
- Not checked: the negation claim's Definitions 3.4, 3.13 and 4.1.
- One optional edit: note that Toms v1 numbers the theorem 6.
