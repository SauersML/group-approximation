---
rg: 2
id: cepss-nonhausdorff-steinberg-simplicity
kind: claim
title: Clark–Exel–Pardo–Sims–Starling simplicity criterion for non-Hausdorff Steinberg algebras, with the Grigorchuk groupoid
distinct_from:
  steinberg-algebra-simple-iff-minimal-effective: that is Steinberg's criterion, which characterizes simplicity only for Hausdorff groupoids; this adds the singular-support condition for ample groupoids with Hausdorff unit space, and the Grigorchuk examples.
artifacts:
  - research/artifacts/un-open-3-grigorchuk-characteristic-2026-09-13.md
---

**ESTABLISHED (import).** L. O. Clark, R. Exel, E. Pardo, A. Sims and C. Starling, *Simplicity of algebras associated
to non-Hausdorff groupoids*, arXiv:1806.04362. Read from the arXiv TeX source on MSI, 2026-09-13. For a field `K`:
- **(S)** Theorem `thm:simple`. Let `𝒢` be a second-countable ample groupoid with Hausdorff unit space. `A_K(𝒢)` is
  simple iff `𝒢` is minimal and effective, and every nonzero `f ∈ A_K(𝒢)` has support with nonempty interior.
- **(G0)** Theorem `thm:grigsimple`(1). For the groupoid `𝒢_(G,X)` of the Grigorchuk group's self-similar action,
  `A_K(𝒢_(G,X))` is simple for every field `K` of characteristic zero.
- **(G2)** Corollary `cor:grigZ2notsimple`. The singular ideal `𝒮_(Z_2)(𝒢_(G,X))` is nonzero, so `A_(Z_2)(𝒢_(G,X))`
  is not simple.
- **(B)** `𝒢_(G,X)` is ample and minimal, and effective since the action is faithful. It is not Hausdorff.
- **(P)** In the proofs, characteristic zero is used only to solve six linear equations (`lem:LCzero`), which
  `lem:zeinterior` and `lem:grigsingular` then use.

Verbatim quotes: `cepss-nonhausdorff-steinberg-simplicity-citation`.

**Review (un-verify, 2026-09-13): PASS (import).** `thm:simple` (l.809–818), `prop:singularideal` (l.612–614), `lem:LCzero` with the six equations (l.2395–2426), `cor:grigZ2notsimple` (l.2431–2440) and the spanning sentence (l.2512–2513) checked verbatim against the arXiv e-print `CEPSS_revision_Mar07_2019.tex` of arXiv:1806.04362. See `research/artifacts/un-review-2026-09-13-part7.md` §2.
