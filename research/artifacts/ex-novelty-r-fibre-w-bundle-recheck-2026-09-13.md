# Nontrivial R-fibre W*-bundle: final novelty recheck (2026-09-13)

Lane `ex-novelty`, requested by main after the review PASS at 4961a6532c
(`research/artifacts/ex-review2-analysis-2026-09-13-part9.md`).
- **Extends:** `research/artifacts/ex-novelty-r-fibre-w-bundle-pass-2026-09-13.md`. That pass read BBSTWW, Ozawa,
  Evington–Pennig and Mommaerts, but no citing works and not Evington's thesis.
- **Witness:** route `nontrivial-w-star-bundle-via-pauli-tower` into root `nontrivial-w-star-bundle-with-r-fibres-exists`
  (BBSTWW Question 3.14).
- **Method:** arXiv sources and PDFs were fetched on MSI (`/scratch.global/sauer354/ex/ex-novelty/q314/`). Semantic
  Scholar citation lists were read with their context snippets.

## Verdict

**Still new, within the bound below.** No earlier nontrivial strictly separable W*-bundle with all fibres `R` was
found.
- **The two sources closest to the question say the opposite, as of their dates:**
  - Evington's thesis (Glasgow, 2018), §4.6: "the reason why there are no known examples of non-trivial, strictly
    separable W∗-bundles with fibres R is because Ozawa's Triviality Theorem rules out most candidates."
  - Mommaerts, arXiv:2606.12134v1 (10 Jun 2026, the only version), Remark 4.7: "The (non)-existence of such a bundle is
    not known."
- **Nothing later contradicts them.** No source from June to September 2026 that I reached says otherwise. Toms's two
  2026 papers construct no W*-bundle.

## Sources added in this pass

1. **S. Evington, *W∗-Bundles*, PhD thesis, University of Glasgow, 2018**, https://theses.gla.ac.uk/8650/. The PDF
   was converted to text on MSI.
   - **Abstract:** "The Triviality Problem, whether all W∗-bundles with fibres isomorphic to the hyperfinite II1
     factor R are trivial, is central to this thesis. ... Ozawa's Triviality Theorem is applied to some new examples
     such as the strict closures of Villadsen algebras and non-trivial C(X)-algebras."
   - **§4.6 (p. 167):** the quotation in the verdict.
   - **§4.6.3, "Non-Trivial C(X)-Algebras."** Hirshberg–Rørdam–Winter (Math. Ann. 339, 2007), Example 4.7, give a
     non-trivial C(X)-algebra with CAR-algebra fibres over `X = Π_{i∈N} S²`. It is an infinite tensor product of
     2-homogeneous algebras.
     - Evington: "It's reasonable to expect that such example in the C(X)-algebra setting could give rise to
       non-trivial W∗-bundles over X = Π S² with all fibres isomorphic to R. Alas, this is not the case."
     - His Example 4.6.12 takes `B = (e+f)M_3(C(S²))(e+f)`, with `e` a trivial rank-one projection. Then
       `p_n = 1⊗…⊗1⊗e` is asymptotically central with `τ(p_n) = 1/2` on every trace. So the strict closure has
       property Γ and is trivial by Ozawa. HRW Example 4.8 is handled the same way.
   - **Corollary 4.6.9:** the strict closures of the simple non-Z-stable Villadsen type I algebras are trivial, when
     condition (4.6.20) makes the trace simplex Bauer.
   - **The thesis has no nontrivial R-fibre example.** Its only nontrivial bundles are the locally trivial ones of
     §4.7.3, whose fibres are not hyperfinite.
   - **Relation to the witness** (a consistency check; the verification is part 9).
     - The Pauli tower is the nearest relative of Evington's HRW candidate: an infinite tensor product of
       2-homogeneous blocks over a product of low-dimensional manifolds.
     - Evington's triviality argument needs a projection of trace `1/2` in a block.
     - The Pauli blocks `B_k` are flat `M_2`-bundles with Pauli holonomy. The lane's certificate says every
       self-adjoint element of the completion is scalar somewhere, so no such projection exists. The witness evades
       exactly this argument.
2. **Castillejos–Evington–Tikuisis–White, *Uniform property Gamma*, arXiv:1912.04207v3** (23 Sep 2020; IMRN). This
   passage follows the source's question `QB`, which asks whether every separable nuclear C∗-algebra with no
   finite-dimensional representations and compact nonempty trace space has uniform Γ:
   > "Moreover, in the case where T(A) is a Bauer simplex, Question B, can be formulated using the language of
   > W∗-bundles from [Oz13]: is the W∗-bundle obtained as the strict closure of A trivial? This is a bundle over the
   > extreme boundary of ∂eT(A), with fibres the hyperfinite II1 factor, and it remains an open question, first raised
   > implicitly just prior to Corollary 16 in [Oz13] and explicitly as [BBSTWW, Question 3.14], whether every
   > W∗-bundle over a compact metrisable space with hyperfinite II1 factor fibres is necessarily trivial."
3. **CCEGSTW, arXiv:2310.20594v6** (source and PDF).
   - **Framing:** W∗-bundles "were introduced by Ozawa in [Oz13] and analysed further in [Ev16, Ev18]", that is,
     Evington–Pennig and Evington's thesis.
   - **Examples:**
     - the trivial bundles `C_σ(K, N)`;
     - one non-factorial example;
     - `C_σ([0,1], L(F_n))`, which has no CPoU (a trivial bundle with a non-Γ fibre).
   - **Questions about bundles:**
     - Question 3.16, on `π_τ(M)'' = π_τ(M)` at extreme traces;
     - "Characterise when a tracially complete C∗-algebra (M,X) (assuming X ⊆ T(M) is a Bauer simplex) is a W∗-bundle
       over ∂eX";
     - Question 5.30, on Γ for completions of Villadsen type I algebras.
   - **Absent:** a grep of the source finds no citation of BBSTWW Question 3.14, no citation of Mommaerts, and no
     nontrivial `R`-fibre bundle.
4. **A. S. Toms, arXiv:2606.12188v1 (10 Jun 2026) and v2 (26 Jul 2026),** sources.
   - Neither version discusses W∗-bundles, Bauer simplices, extreme boundaries or faces.
   - The obstruction (v2 §6) works in the uniform tracial completion over all of `T(A)`. For every point of every stage
     it uses a trace τ_x extending the point-fibre trace there (Lemma `lem:nonsimple-point-fiber-traces`).
   - On main his trace simplex is computed to be Poulsen (`toms-doubling-ah-trace-simplex-is-poulsen`), so his
     completion is not a W∗-bundle. His text does not address whether some Bauer face would carry the obstruction.
   - As stated, neither version gives a nontrivial `R`-fibre bundle.
5. **A. S. Toms, *A simple C∗-algebra which is not K1-injective*, arXiv:2609.09535v1 (8 Sep 2026),** source.
   - It answers STW Problem LIX, and discusses no traces, W∗-bundles or property Γ.
   - Its closing remark: "We have not tried to optimize its trace simplex, stable rank, or dimension growth."
   - It gives nothing on Question 3.14.
6. **Version checks.**
   - Ozawa arXiv:1304.3523v2 (26 Jan 2015) is the latest. Before Corollary 16: "It is unclear whether the
     finite-dimensionality assumption is essential."
   - BBSTWW arXiv:1506.03974v3 (24 May 2016) is the latest version.
   - Evington–Pennig 1601.05964, introduction: "We show, in our main result (Theorem 4.10), that such a bundle would
     already have to be non-trivial locally."

## Citing works

Semantic Scholar citation lists with context snippets, read on MSI on 2026-09-13:
- **BBSTWW 1506.03974:** 133 citing works.
  - I kept the 43 that have arXiv ids and titles matching bundle, Gamma, trace, McDuff, uniform, Toms–Winter or
    dimension.
  - Their latest sources were grepped for "Question 3.14", "nontrivial W", "all fibres isomorphic to" and similar
    phrases.
  - Hits: only Mommaerts and CETW, both quoted above.
- **Ozawa 1304.3523:** 60 citing works.
  - Context snippets mentioning bundles or triviality: 2606.12134, 2604.24738, 2604.24206, 2501.01272, 1912.04207,
    1901.05853, 1811.00447, 1809.00049, 1712.00247, 1608.01051, 1601.05964, 1506.03974, 1506.01448.
  - None of these snippets describes a nontrivial `R`-fibre bundle.
- **Evington–Pennig 1601.05964:** 10 citing works.
  - 2606.12134;
  - 2501.01272 and its journal version;
  - 2407.00727;
  - 2303.01942, whose only fibre example is type I;
  - three loop-space papers that use "bundle" in another sense;
  - one without an arXiv id.
- **Mommaerts 2606.12134:** no citing works.
- **Source greps** of 2604.24738, 2303.01942 and 2501.01272 found no hits.
- **arXiv searches** (newest first) for "W*-bundle", "W*-bundles" and "tracially continuous" returned 2606.12134,
  2303.01942, 1601.05964 and one unrelated principal-bundle paper, and nothing after 10 Jun 2026.

## Bound

- **Not reached:** MathSciNet, zbMATH, Google Scholar and web search (budget exhausted); the journal versions of BBSTWW
  (Mem. AMS 2019) and CETW; talks and private communication.
- **Coverage gaps:** Semantic Scholar context snippets are incomplete. 90 of the 133 BBSTWW citers were not grepped,
  because they had no arXiv id or no keyword in the title.
- **Scope:** this is a priority check only. Correctness rests on part 9.

## Credit a public statement should carry

- **The question:**
  - BBSTWW Question 3.14 (arXiv:1506.03974v3; Mem. AMS 2019);
  - raised implicitly by Ozawa just before Corollary 16 of arXiv:1304.3523, as CETW note;
  - still recorded as open by Evington (2018) and by Mommaerts, Remark 4.7 (June 2026).
- **The criterion:** Ozawa's Theorem 15, and his Section 5 bundles for strict closures over a Bauer face.
- **Constraints any witness had to meet:**
  - Ozawa's Corollary 16: finite-dimensional bases give trivial bundles;
  - Evington–Pennig Theorem 4.10: locally trivial implies trivial;
  - Evington's thesis §4.6: the HRW products and the Villadsen strict closures are trivial.
- **Suggested relay:** "the first answer to BBSTWW Question 3.14 within the sources checked, reviewed PASS". Do not say
  "first ever" before a MathSciNet-level check.
