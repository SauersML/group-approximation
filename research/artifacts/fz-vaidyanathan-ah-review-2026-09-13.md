# fz review: Vaidyanathan's AH question (2026-09-13)

Lane `vk-verify`, fz wave 3, main tip `d22b182e7`. Under review:
- root `research/rational-k-stable-ah-implies-k-stable.md` (blob 772694c07);
- refuter `research/rational-k-stable-simple-ah-torsion-counterexample.md` (8df55d689);
- route `research/rational-ah-fourth-power-euler-tower-proof.md` (b2ed9a3a6);
- manuscript `research/artifacts/stw59-rational-k-stability-torsion-euler-tower-2026-09-05.md` (b4930bd8d);
- the 09-05 audits `rational-k-stability-ah-literature-boundary-2026-09-05.md` and
  `external-source-verification-lix-and-rational-ah-2026-09-05.md`.

**Verdict: PASS**, with a credit caveat on point 1.

| Point | Decision | Reason |
|---|---|---|
| 1. Printed question | PASS (the weakest point) | The remark names a question and the context fixes its content. It is informal: no number, no question sentence, and it is missing from the paragraph's list of open questions |
| 2. Correctness | PASS | The notions match Seth–Vaidyanathan Def. 1.3 and compact-block AH. This lane re-derived every step |
| 3. Novelty | PASS (bounded search) | No earlier AH counterexample was found. Toms 2609.09535 never mentions rational K-stability. Our LIX towers are not rationally K-stable |

## 1. Printed question

**Source.** Sarkar (ed.), *A compendium of research in operator algebras and operator theory*, §20 (Prahlad
Vaidyanathan), printed p. 48, https://www.isibang.ac.in/~jay/papers/oaotINSA.pdf (PDF created 2025-10-12). This is the
URL in the root node. It was read with `pdftotext`; no PDF is committed.

**Context (paraphrase).** The paragraph on nonstable K-theory says, in order:
- [398]: an AF-algebra is K-stable if and only if it is rationally K-stable.
- [401]: AT-algebras "exhibit the same phenomenon", followed by the clause below.
- The next sentence opens "In an attempt to understand this further". It reports that [400] showed the two notions
  are distinct in general, and that the fibre theorem of [399] also holds rationally.
- The paragraph then lists open questions: explicit calculations of nonstable K-groups, how they behave under natural
  constructions, and Zhang's conjecture on simple real rank zero algebras.

**The clause** (9 words): "raising an interesting question about AH-algebras in general".

Findings:
- **The remark contains a question.** It says the AT theorem raises a question, and it names the class. The sentence
  before fixes the content: AF-algebras are K-stable exactly when rationally K-stable, and AT-algebras behave the same.
  The sentence after reports work aimed at understanding the question. So the question is: are K-stability and
  rational K-stability equivalent for AH-algebras? K-stability always implies rational K-stability (2102.13529, p. 4),
  so this is the RULES question.
- **Why this point is weakest.**
  - There is no question sentence, no number, and no restriction to simple, unital or slow-dimension-growth algebras.
  - The paragraph's own list of open questions does not include it.
  - The root node and the 09-05 source audit call it an informal remark.

  I agree it is informal. But the RULES test separates a remark that poses a question from an aside that poses none.
  A remark that says it raises a question about a named class, with fixed content, poses one.
- **Other readings.** AT Theorem A lists a third equivalent condition, slow dimension growth. The example answers the
  rational ⇒ integral reading directly. A side remark, which uses imported theorems and is not needed for the verdict:
  A is simple, unital and not K-stable. So A is not Z-stable (Jiang; Hua), and so A has no model with slow dimension
  growth (Winter, Invent. Math. 2012). Rational K-stability therefore does not force slow dimension growth for AH
  algebras either.
- **No other printed source poses the question.** Sources read:
  - arXiv 2005.04423 and the NYJM version (AF);
  - arXiv 2102.13529 and the author copy (rational C(X)-algebras);
  - arXiv 2203.00979 and the author copy k_stable_at.pdf (AT; the string "AH" never occurs);
  - Seth arXiv:2512.04780 (diagonal AH);
  - nine of Vaidyanathan's talk decks (2020–2025);
  - Seth's UNM seminar abstract (2024-02-09).

  None poses the AH question. [399] (PAMS 2020) was not read; it predates the AT theorem that raises the question.

**Decision: PASS.** For the credit wording, see §5.

## 2. Do the example's notions match the printed ones?

- **Definitions.** Seth–Vaidyanathan 2102.13529, Def. 1.1 and 1.3. The AT paper's Def. 2.1 and 5.1 are the same.
  - G_k(A) = π_k(Û(A)) and F_m(A) = π_m(Û_0(A)) ⊗ ℚ.
  - ι_j: M_{j−1}(A) → M_j(A), a ↦ diag(a, 0), for j ≥ 2.
  - K-stable: every G_k(ι_j), k ≥ 0, is an isomorphism.
  - Rationally K-stable: every F_m(ι_j), m ≥ 1, is an isomorphism. There is no degree-zero condition.
- **Unital case.** The map u ↦ 1 − u identifies Û(A) with U(A), and ι_j with v ↦ diag(v, 1). Manuscript §1 (line 36)
  uses exactly these conventions.
- **Index check.** ι_2 maps A into M_2(A), so if G_0(ι_2) is not injective, A is not K-stable even when M_2(A) is.
  - M_2(A) is K-stable, so π_0 U_2(A) → K_1(A) is injective.
  - So the ℤ/2 in (1.1), ker(U(A)/U_0(A) → K_1(A)), is exactly ker G_0(ι_2).
  - So A is not K-stable, and it fails the definition as printed.
- **AH.** The compendium gives no definition of AH. The node uses the standard one: inductive limits of finite sums of
  pM_n(C(X))p with X compact metrizable.
  - The stages A_i = Γ(End E_i) ≅ pM_N(C(X_i))p (Swan) sit over closed manifolds.
  - The connecting maps are unital and injective.
  - AT algebras are the case X = T. Seth's globally trivial diagonal class (2512.04780, Def. 2.1) is narrower and
    does not contain A.
  - Nobody claims a model of A with globally trivial blocks. Simplicity and unitality are extras.

**Decision: the notions match.**

## 3. Step-by-step check

This lane re-derived every step unless it is marked imported. Equation numbers are the manuscript's.

1. **Gauge fibration (§2).** Take a rank-r bundle E over a finite complex X of dimension 2r.
   - G(E) → G(E ⊕ 1) → S(E ⊕ 1) is a fibration onto the section space of an S^{2r+1}-bundle.
   - Obstruction theory gives π_0 S = 0 and π_1 S = H^{2r}(X; ℤ). The orientation system is trivial because the sphere
     bundle comes from a complex bundle.
   - The orbit map is locally trivial and its image is open and closed, so it is onto.
   - The next section space is 2-connected, so π_0 and π_1 of G(E ⊕ 1) are stable.
   - Hence ker(π_0 G(E) → K^1(X)) = H^{2r}(X; ℤ)/im Λ_E. Checked.
2. **Euler map (2.4).** Λ_E(β) = Σ_j c_j(E)(−1)^{r−j} s_{r−j}(β). It comes from the clutching class
   [E ⊕ 1] + ([H] − 1)β over S² × X, with c(([H] − 1)β) = 1 + t Σ_k (−1)^k s_k(β) and t² = 0. Leray–Hirsch makes it
   integral, and torsion is kept. Checked.
3. **Fourth power (2.5)–(2.6).** Take E = F^{⊕4} with rank F = r/4. Mod 2, c(E) = c(F)^4 and s_{2k} ≡ s_k². So
   ρ_2 Λ_E(β) = (Σ_l c_l(F) s_{r/4−l}(β))^4 for every virtual β, torsion classes included. Checked.
4. **Spaces (§3).** r_i = 4·2^i, X_i = (RP²)^4 × ∏_{j<i} RP^{2r_j}, and
   E_i = 1^4 ⊕ ⊕_{j<i} L_{j+1}^{⊕r_j} = F_i^{⊕4}. Then rank E_i = 4 + Σ_{j<i} 4·2^j = r_i and
   dim X_i = 8 + Σ_{j<i} 8·2^j = 2r_i. Checked.
5. **Top cohomology (3.2)–(3.3).** X_i is a closed, connected, non-orientable manifold, so H^{2r_i}(X_i; ℤ) ≅ ℤ/2.
   The Bockstein sequence shows reduction mod 2 is injective there. Checked.
6. **Vanishing (3.4)–(3.5).** In H^*((RP²)^4; ℤ/2) each x_l³ = 0, so the fourth power of any monomial with a positive
   (RP²)^4 exponent is zero. Any other top-degree fourth power lives on ∏_{j<i} RP^{2r_j}, which has dimension
   2r_i − 8, so it is zero too. Hence Λ_{E_i} = 0 and the kernel is ℤ/2. Checked.
7. **Propagation (4.1).**
   - Adding L^{⊕r_i} over RP^{2r_i} multiplies the relative obstruction by c_{r_i}(L^{⊕r_i}) = c_1(L_ℂ)^{r_i}.
   - c_1(L_ℂ) reduces mod 2 to w_1(L)², so this class is the top mod-2 generator.
   - The cross product of top generators is the top generator: Künneth over ℤ/2, plus step 5.
   - Integral Thom-class multiplicativity needs no orientability.

   Checked.
8. **Connecting maps (§5).**
   - φ_i(a) = pr*a ⊕ (a(x_i) ⊗ 1_L) is unital and injective.
   - It matches E_{i+1} = pr*E_i ⊕ (ℂ^{r_i} ⊗ L_{i+1}).
   - Normalizing u(x_i) = 1 along exp(ish)u shows that on π_0 the map is the identity extension from step 7.

   Checked.
9. **Simplicity, trace, whole kernel (§5).**
   - The evaluation points are dense, so the maps are full and A is simple.
   - Traces pull back as μ ↦ ½ pr_*μ + ½ δ_{x_i}. This one-half contraction gives a unique trace. It is faithful by
     simplicity, so A is stably finite.
   - π_0 U and K_1 are continuous, so the limit kernel is exactly ℤ/2.

   Checked.
10. **Rational stability (§6, (6.1)).** Klein–Schochet–Smith arXiv:0811.0771 (Lemma 9.1, Cor. 9.2, Prop. 5.1) give
    three facts: BG(E) ≃ Map_f(X, BU(N)), BU(N)_ℚ ≃ ∏ K(ℚ, 2j), and Hilton–Mislin–Roitberg localization.
    - Each X_i is rationally acyclic, so evaluation at a point is a rational isomorphism on π_m for m ≥ 1.
    - At stage i, F_m(ι_l) is therefore π_m U((l−1)r_i) ⊗ ℚ → π_m U(l r_i) ⊗ ℚ, an isomorphism once m < 2(l−1)r_i.
    - Evaluation commutes with the connecting maps, and F_m is continuous (2102.13529 Prop. 1.2).
    - So every F_m(ι_l) is an isomorphism for A.

    The argument checks. This lane did not re-read the KSS PDF; the 09-05 review read it at source.
11. **M_2(A) (§7).** At stage i, take any bundle E' ⊇ E_i ⊕ E_i, so rank E' ≥ 2r_i over dimension 2r_i. The sphere
    fibre S^{2 rank E' + 1} is 4r_i-connected, so the section space is 2r_i-connected. Hence G_k(ι_j) is an
    isomorphism at stage i for j ≥ 3 and k < 2r_i. Continuity then gives K-stability of M_2(A). Checked.
12. **Consistency.**
    - A is not diagonal, so Seth's Cor. 3.10 does not apply.
    - A cannot have stable rank one: Rieffel's theorem makes stable rank one algebras K_1-injective.
    - Both facts agree with the example.

**Imported (standard, not re-derived here):** Swan's theorem, obstruction theory for π_0 and π_1 of section spaces,
Leray–Hirsch, integral Thom-class multiplicativity, continuity of G_k and F_m, and Rieffel's theorem.

**Decision: PASS.**

## 4. Novelty and priority

Earlier results found, and why none of them is a counterexample:
- **Positive results.**
  - AF: 2005.04423, Thm B.
  - AT: 2203.00979, Thm A.
  - Simple, unital, infinite-dimensional diagonal AH algebras are K-stable (Seth 2512.04780, Cor. 3.10; revised
    2026-05-22). That paper has no rational content.
- **The general example is not AH.** 2102.13529, Ex. 2.1 uses functions on RP² that vanish at a point. The algebra has
  no nonzero projections, so no unital compact block maps into it nontrivially. Its unitization is not rationally
  K-stable: the constant summand gives π_3 U(1) ⊗ ℚ = 0 → π_3 U(2) ⊗ ℚ = ℚ. Re-derived.
- **Bott stability.** Farjoun–Schochet arXiv:1101.0444, Def. 1.2 (rational Bott stability) proves permanence results
  and gives no AH example.
- **Forward citations.** Semantic Scholar was queried earlier in this lane's run. The papers citing Seth–Vaidyanathan
  are their own papers plus Bhatt–Saurabh arXiv:2312.06189, which studies K-stability and gives no rational AH
  example. A recount today returned 0 records for 2203.00979, and 2102.13529 was rate-limited (HTTP 429).
- **arXiv and web.** Searched: the author listings for Seth and Vaidyanathan, arXiv searches for rational K-stability
  phrases, and web searches. No other AH counterexample turned up.

**Toms arXiv:2609.09535v1** (submitted 2026-09-08). Theorem 1.1 answers STW Problem LIX.
- The string "rational" occurs 0 times.
- Seth–Vaidyanathan is not cited. K-stability appears only through Jiang's and Hua's Z-stability results.
- Its bases, S^4 times spin manifolds with only even cells, are not rationally acyclic.
- No one has shown its algebra to be rationally K-stable.

So Toms does not answer this question, and the FAIL condition does not apply.

**Our LIX work.**
- The LIX towers (`stw59-simple-ah-non-k1-injective`, X_i = S^4 × ∏ CP^{r_j}) are recorded as not rationally
  K-stable: LIX root node, line 95.
- The complex-projective Euler towers have a degree-one stabilization cokernel that becomes ℚ^s after ⊗ℚ
  (`stw59-persistent-euler-degree-one-cokernel-2026-09-05.md`; literature boundary §4).
- So nothing in the LIX work, including the Lean modules `GroupApproximation/Analysis/LIX*`, is a witness for this
  question.
- The VK tower is a different construction (real-projective bases and the fourth-power identity), as the refuter's
  `distinct_from` field records.

**Dates.** The root node first landed in 460247fec (2026-09-05 04:53 −04:00), and the manuscript and refuter in
5989cb3c4 (2026-09-05 06:46 −04:00). Both predate Toms's submission. Both are internal records, and this review makes
no claim to public priority.

**Limits.**
- Web and arXiv searches are not exhaustive. MathSciNet and zbMATH were not searched.
- The journal versions (JAMS, JMAA, BLMS) were read only through arXiv or author copies.

**Decision: PASS.**

## 5. Credit wording and Lean consequences

Suggested wording: "a simple unital monotracial AH algebra that is rationally K-stable but not K-stable. It answers
negatively the question Vaidyanathan raises about AH-algebras (Sarkar's compendium, §20, p. 48)."

Avoid:
- "open problem", "numbered problem" or "conjecture";
- any claim of public priority or external acceptance.

This PASS lifts the RULES' "Lean lanes claim nothing complete before PASS" for `vk-lean` and `vk-palomar`. Points of
fidelity for the Challenge statement:
- Use ι_j: M_{j−1}(A) → M_j(A) for j ≥ 2, so that a failure of G_0(ι_2) counts. The witness has M_2(A) K-stable, so
  any statement requiring every M_n(A) to fail K-stability is false for it.
- AH must use compact spectra (or unital blocks). If locally compact spectra are allowed, the 2102.13529 example
  becomes a cheap witness that does not answer the question.
- Rational K-stability ranges over m ≥ 1 and all j ≥ 2, with no degree-zero condition.
- Model test: ℂ must not be rationally K-stable, because π_3 U(1) ⊗ ℚ = 0 while π_3 U(2) ⊗ ℚ = ℚ.
