# Novelty check: braided V is not inner amenable (Zaremsky Problem 2.11), 2026-09-13

Requested by z-verify-groups after its review PASS (`research/artifacts/zp-review-groups-2026-09-13-part1.md` §8,
c0ff0a5f90) of claim `braided-v-is-not-inner-amenable` (lane z2-11-bv-inner-amen, 55604bc42e).

**Verdict: NEW within the sources checked (bounded).** No source states that Brin's braided V (bV = V_br) is or is not
inner amenable. The two most recent statements by the list's author call the question open.

## Evidence

1. **Bashwinger–Zaremsky, "Non-inner amenability of the Higman-Thompson groups", arXiv:2203.13798** (v1 25 Mar 2022,
   last revised 18 Jul 2025; to appear in IJAC). It proves T_n and V_n are not inner amenable for n ≥ 2. Closing
   remarks, as quoted by a fetch of the arXiv HTML (tool quote, not re-read by eye): "Other related groups for which
   inner amenability is open in general include braided Thompson groups and Röver–Nekrashevych groups, and it would be
   interesting to try and use similar tools to prove for example that none of these are non-inner amenable." Its only
   other braided mention: bF yields McDuff factors [BZ23].
2. **Zaremsky's list, version of July 12, 2026, Problem 2.11**: "Is braided V inner amenable? (Probably not.)"
3. **Bashwinger–Zaremsky, "Von Neumann algebras of Thompson-like groups from cloning systems", arXiv:2104.04826v2**
   (J. Operator Theory, doi 10.7900/jot.2021apr16.2355). Read pp. 1–3 of the v2 PDF. Abstract: "L(bV) and L(bF) are
   type II₁ factors and L(bF) is McDuff. In particular we get the surprising result that bF is inner amenable."
   Theorem 5.10 requires a fully compatible, slightly pure, uniform cloning system. Nothing on inner amenability of bV.
   Section 6 (questions) was not read.
4. **DeBonis–de Santiago–Khan, arXiv:2312.08345** (v. 3 Oct 2024):
   - Theorem A: McDuff groups from slightly pure uniform cloning systems.
   - Theorem B: T_d and V_d are properly proximal.
   - Theorem C: L(T_d) and L(V_d) are prime.
   - Example 2.9: "the cloning system bV_d arises from is not even slightly pure". No result covers bV_d.
5. **Bashwinger–DeBonis, "On similarity structure groups and their W* and C*-algebras", arXiv:2507.18821v2**
   (22 May 2026). Non-inner amenability of CSS* groups (Theorem B). Its introduction says related frameworks "do not
   apply to some in the cloning system family, like the braided Higman-Thompson group bV_d".
6. **Ariza Mejía–Chifan–Osin–Sun, "McDuff superrigidity for group II₁ factors", arXiv:2511.23123**: mentions F and
   F_n only; nothing on braided Thompson groups.
7. **Kerr–Tucker-Drob, "Dynamical alternating groups, stability, property Gamma, and inner amenability"** (Ann. Sci.
   ENS 2023, doi 10.24033/asens.2528). It treats alternating groups of topologically free Cantor actions. bV acts on
   the Cantor set only through V, with nontrivial kernel, so it is not covered.
8. **Citation sweeps**:
   - Semantic Scholar citations of Haagerup–Olesen arXiv:1609.05086: 45 entries, 2015–2026.
   - Semantic Scholar citations of arXiv:2104.04826: 5 entries (2109.13389, 2203.13798, 2312.08345, 2507.18821,
     2511.23123).
   - OpenAlex `cites:W2963356329` (the JFA version): 30 works.
   - No citing title concerns braided groups, apart from the cloning-system papers above.
   - OpenAlex search "braided Thompson", publication date ≥ 2026-07-01 (first page of 193 hits): nothing relevant.

## Bounds

- The session's web-search budget was exhausted. Sources came from API citation lists, arXiv abstract/HTML pages and
  one PDF.
- For citing papers only titles were checked, except items 3–7.
- No MathSciNet, zbMATH or Google Scholar.

## Remarks for the verifier and the owner lane

- **Cheaper known route?** Dahmani–Guirardel–Osin [DGO17, Theorem 8.14], as cited on p. 2 of arXiv:2104.04826:
  acylindrically hyperbolic ICC groups are not inner amenable. So a proof that bV is acylindrically hyperbolic would
  give the result directly.
  - No source found says bV is acylindrically hyperbolic.
  - Fournier-Facio–Lodha–Zaremsky, arXiv:2204.05272 (abstract), give bV an infinite-dimensional space of
    quasimorphisms. That does not imply acylindrical hyperbolicity.
  - Item 1's 2025 statement, by a coauthor of that paper, indicates no such corollary was known.
- **Credit to carry in the node:**
  - Haagerup–Olesen (the PSL(2,Z) ≤ T lifting and centralizer technique, arXiv:1609.05086);
  - Bashwinger–Zaremsky (T_n, V_n; II₁ factor L(bV));
  - Effros (property Γ and inner amenability);
  - Brin (arXiv:math/0406042) and Dehornoy for bV.
- **Relay wording:** "answers Zaremsky's Problem 2.11 negatively, as the list predicted; first proof within the
  sources checked (bounded search, no MathSciNet/zbMATH)".
