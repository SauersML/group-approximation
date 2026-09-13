# Atiyah base change in transcendence degree two: novelty and credit pass (2026-09-13)

Lane `ex-novelty`, at main's request.
- **Claim:** `atiyah-base-change-in-transcendence-degree-two-under-det`, from lane ex2-atiyah-base-change-td2,
  artifacts `research/artifacts/atiyah-two-variable-base-change-2026-09-13-part1.md` to `-part4.md`.
- **Review status:**
  - Items 1–2 were reviewed PASS by ex-verify2-quantum-l2
    (`research/artifacts/ex-review2-quantum-l2-2026-09-13-part5.md`).
  - Item 3 (Part 4, finite extensions) is unreviewed.
- **Where the files are:** all sources below were fetched on MSI (`/scratch.global/sauer354/ex/ex-novelty/atiyah/`).
  - The GAFA paper and the St Andrews survey came as publisher PDFs, through MSI's institutional access.
  - The others came as arXiv sources.

## Verdict

**New within the bound: the implication, and the way the determinant conjecture enters.**
- **The implication.** Take a torsion-free group with Strong Atiyah over `Qbar` and Lück's determinant conjecture.
  Then it has integral von Neumann kernel dimensions over every coefficient field of transcendence degree at most 2,
  and these are invariant under automorphisms of `C` fixing `Qbar`.
  - No hypothesis of soficity, local indicability or approximation is used.
- **The mechanism.** The determinant conjecture is applied only to integral models over `Z[G]` of zero-dimensional
  cycles, whose Chow forms are small on hyperplanes through `z`. The main steps are (RES2), Proposition C,
  Corollary 6 and Lemma J.
- **Why this matters.** No source reached uses the determinant conjecture to get base change to transcendental
  coefficients. Jaikin-Zapirain says plainly that the determinant route "cannot work for general K", because the
  conjecture fails for transcendental coefficients. The lane's argument never applies the determinant bound to a
  transcendental matrix, so it avoids exactly that obstacle.

**What it does not add: no new group.**
- Sofic groups satisfy the determinant conjecture. For every sofic group the conclusion is already known in
  stronger form, over every subfield of `C` and for all embeddings (Jaikin-Zapirain 2019).
- For locally indicable groups it is known with no determinant hypothesis (Jaikin-Zapirain–López-Álvarez 2020).
- The theorem is new only as an implication, for torsion-free groups not known to be sofic or locally indicable.
  No such group satisfying both hypotheses is known.

**Philippon's part.** Part 3's Diophantine construction is an elementary proof of a weak special case of Philippon,
JNT 81 (2000), Théorème 1, with `n = 2` and `d = 0`. The lane's own nodes already say so.

## What is Jaikin-Zapirain's

1. **A. Jaikin-Zapirain, *The base change in the Atiyah and the Lück approximation conjectures*, GAFA 29 (2019)
   464–538, doi:10.1007/s00039-019-00487-3.** Read from the Springer PDF, §1.
   - **Theorem 1.1:** "Let G be a sofic group. Assume that the strong Atiyah conjecture holds for G over Q̄. Then the
     strong Atiyah conjecture holds for G over C."
   - **Theorem 1.3:** the sofic Lück approximation over every subfield `K ⊆ C`.
   - **Corollaries 1.5–1.7** hold for sofic groups: the strong algebraic eigenvalue, center and independence
     conjectures. Corollary 1.7: "rk_G(φ_1(A)) = rk_G(φ_2(A))" for any two embeddings `φ_i : K → C`.
   - **The obstacle, verbatim (p. 470):** "This result was known previously when K = Q̄ ([ES05], [DLMSY03]). The proof
     of this particular case used the solution of the so-called determinant conjecture in the case of sofic groups
     when K = Q̄. This method cannot work for general K because the determinant conjecture is not valid over an
     arbitrary field K (see [JAI19]). Our approach is completely different and it uses the theory of epic ∗-regular
     R-rings".
2. **A. Jaikin-Zapirain, *L²-Betti numbers and their analogues in positive characteristic*, Groups St Andrews 2017,
   LMS Lecture Note Ser. 455 (2019) 346–405, doi:10.1017/9781108692397.015.** Read from the Cambridge PDF.
   - **§10.3, Conjecture 10.9** is "the determinant conjecture over K". Then: "Unfortunately Conjecture 10.9 is not
     correct if K = C", with the example `A = z − e^{2πir}` over `C[Z]`.
   - **§10:** in the number-field case "the proof of this case uses a partial solution of the determinant conjecture";
     "The passage from algebraic number fields to arbitrary fields K uses algebraic techniques".
   - **§10.5:** induction on transcendence degree, through natural transcendental extensions of Sylvester rank
     functions and the strong algebraic eigenvalue conjecture (Conjecture 10.12).
   - **§12.3, Question 12.5:** "Let G be a group. Is it true that A_C(G) = A_Q̄(G)?"
     - Theorem 12.6 answers it for sofic `G` with `A_Q̄(G) ≤ (1/n)Z`.
     - The td2 theorem gives the transcendence-degree ≤ 2 case of Question 12.5 for torsion-free groups, under the
       determinant conjecture. That is a partial answer, not the question.
3. **A. Jaikin-Zapirain and D. López-Álvarez, Math. Ann. 376 (2020) 1741–1793, arXiv:1810.12135v4** (source).
   - For locally indicable groups they prove Strong Atiyah over every subfield of `C`, and the strong algebraic
     eigenvalue, center and independence conjectures.
   - "All these conjectures were proved for sofic groups in [Ja17base]."
   - The lane's degree-one node already cites this list for its items 2–3, which are these conjectures over `Qbar`
     under the determinant conjecture.

**Consequence for any statement.**
- For sofic and for locally indicable groups, items 1–3 of the node are special cases of these theorems.
- The node's inductive shape resembles §10.5: transcendence degree climbed step by step, with the algebraic
  eigenvalue conjecture as the one-variable step.
- The tools are unrelated, though. Jaikin-Zapirain uses ∗-regular rings and approximation; the lane uses Diophantine
  cycles and the determinant bound.

## What is Philippon's

- **Source.** P. Philippon, *Approximations algébriques des points dans les espaces projectifs I*, J. Number Theory 81
  (2000) 234–253, doi:10.1006/jnth.1999.2461.
  - My MSI copy of the archived PDF has the same md5 (`7e60b0d073b610962cf81c8d6e65d0b9`) as the copy recorded in
    `philippon-zero-cycles-approximate-points-of-p3-citation`.
  - Its text layer shows Théorème 1 (p. 236), "Soit n ∈ N*, c_n = 2^(n+4) n! et x ∈ P_n(C), alors pour tous entiers
    max(0, n−3) ≤ d ≤ n, H ≥ 1 et Δ ≥ (4c_n)^(n−d+1), il existe un cycle Z de dimension d, irréductible et
    récursivement défini sur Q ...", with degree, height and distance budgets.
  - The full statement is quoted on main.
- **Credit boundary** (already stated on main in `philippon-zero-cycles-approximate-points-of-p3` and in
  `algebraically-independent-points-approximable-by-zero-cycles`).
  - For `s = 2`, Part 3 builds the small bivariate polynomial by Minkowski, cuts it with a univariate polynomial, and
    takes the Chow form of `V(p_1, q)`. That is a self-contained proof of a weak special case of Théorème 1 with
    `n = 2`, `d = 0`.
  - It gives only the ratio statement, with worse constants and no degree or height budget.
  - Philippon's theorem gives more, in every dimension `n ≤ 3`. The transcendence-degree-three route
    `atiyah-transcendence-degree-three-via-philippon` uses his `n = 3` case directly.
- **What remains the lane's:** the operator side (RES2), Proposition C, Corollary 6, Lemma J, and the link from
  small Chow forms to kernel dimensions.

## Prior uses of the determinant conjecture

- **Lück's approximation theorem**, and Schick, *L²-determinant class and approximation of L²-Betti numbers*, TAMS
  2001.
- **Dodziuk–Linnell–Mathai–Schick–Yates,** CPAM 56 (2003), arXiv:math/0107049 (source). Its abstract proves Atiyah
  over `Q̄G` for a class of groups and states: "We also establish the absence of eigenvalues that are Liouville
  transcendental numbers whenever the covering transformation group is either residually finite or more generally in
  a certain large bootstrap class".
  - The repo's superseded `determinant-conjecture-excludes-liouville-atiyah-exceptions` is of the same kind, and
    should credit DLMSY.
  - Jaikin-Zapirain recalls a different base-change result from the same paper: "In [DLMSY03] it was shown that the
    Kaplansky zero-divisor conjecture for C[G] follows from the Kaplansky zero-divisor conjecture for Q̄[G]."
- **Elek–Szabó (2005):** sofic groups satisfy the determinant conjecture.
  - Kirstein–Kremer–Lück, arXiv:2311.17830, §5, list sofic groups in the class `F`.
  - Their "Status of the Atiyah Conjecture" theorem, for any `Q ⊆ F ⊆ C`, draws its general-field cases from
    Jaikin-Zapirain Corollary 1.2 and Jaikin-Zapirain–López-Álvarez. It has no determinant-conjecture base change.

## Citing works and searches

- **OpenAlex:** 24 works citing the GAFA paper (W2922526935). Semantic Scholar lists none for the DOI (index gap).
- **Grepped arXiv sources:**
  - the 11 citers with arXiv ids: 2010.09146, 2201.01432, 2102.04549, 2107.11507, 2005.12814, 2012.15844,
    2002.12522, 1901.07158, 1811.00356, 1911.08951, 1902.06476;
  - plus 2005.12374 and 2311.17830, found by title search.
  - Search terms: "determinant conjecture", "base change", "transcendence degree", "algebraically independent",
    "independence conjecture", "not valid over".
  - Only Lück 2102.04549 and Kirstein–Kremer–Lück 2311.17830 mention the determinant conjecture, as status surveys.
    No citer gives a determinant-conjecture base change.
- **arXiv title searches** ("Atiyah conjecture", newest 25; "determinant conjecture"): Fisher–Ng 2606.19606 (June 2026)
  and Manzoor 2508.15154 were grepped, with no base change.
- **Schick,** *Integrality of L²-Betti numbers*, arXiv:math/0001101: its abstract concerns limits of groups; there is
  no base change to transcendental coefficients.

**Bound.**
- **Not reached:** MathSciNet, zbMATH, web search (budget exhausted); Lück's book (2002), Chapters 10 and 13; the
  2019 chapter "Lück's Approximation Theorem"; Jaikin-Zapirain's *The universality of Hughes-free division rings*;
  book-only citers.
- **Partial reads:** GAFA §§1–2 and the section headings; the survey's §§10.2–10.5 and 12.3.

## Credit a public statement should carry

**Suggested wording:**
"Under Lück's determinant conjecture, Strong Atiyah over Q̄ for a torsion-free group implies integral von Neumann
kernel dimensions over every coefficient field of transcendence degree at most two, invariant under automorphisms of
C fixing Q̄. For sofic groups this, and much more, is due to Jaikin-Zapirain (GAFA 2019, Theorem 1.1 and Corollary
1.7); for locally indicable groups it is due to Jaikin-Zapirain and López-Álvarez (Math. Ann. 2020). The two-variable
Diophantine input is a weak form of Philippon's approximation theorem (J. Number Theory 81, 2000, Théorème 1). The
determinant-conjecture method goes back to Lück, Schick and Dodziuk–Linnell–Mathai–Schick–Yates. What is new is that
the determinant conjecture, applied only to integral models of zero-cycles, carries base change past the obstruction
recorded by Jaikin-Zapirain."

**Rules for any statement:**
- Do not present it as a new case of the Atiyah conjecture for a known group.
- Do not present the Diophantine step as new.
- State that item 3 (finite extensions, Part 4) is unreviewed.
