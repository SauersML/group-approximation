---
rg: 2
id: li-derived-full-group-homology-citation
kind: route
title: Import Li's identification of full group homology with groupoid K-theory and its spectral sequence
target: li-derived-full-group-homology-is-k-theory-cover
requires: []
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**Source.** Xin Li, *Ample groupoids, topological full groups, algebraic K-theory spectra and
infinite loop spaces*, arXiv:2209.08087.
- **Numbering.** Theorem numbers are those printed in the current arXiv version, as reported by
  ex-verify2-groups from the PDF (`research/artifacts/ex-review2-groups-2026-09-13-part4.md`,
  §1). This lane checked them independently against the TeX e-print `Homology_TFG.tex`
  (modified 2024-11-25), read on MSI at
  `/scratch.global/sauer354/ex/ex-fp-simple-full-group-obstruct/src/2209.08087/main.tex`.
  - The check counted the shared `[section]` theorem counter, which covers theorems, lemmas,
    corollaries, propositions, remarks, definitions and examples.
  - Sections are §1 Introduction through §6 Applications.
- **Quotations** are verbatim, with TeX macros expanded. TeX labels are given in parentheses for
  traceability.

1. **Theorem 4.18** (stated in the introduction as **Theorem A**; label `thm:HKB=HG`). "Let `G` be
   an ample groupoid with locally compact Hausdorff unit space `G^(0)` and `C` an abelian group. We
   have `H~_*(K(B_G), C) ≅ H_*(G, C)`." This is item 1.
2. **Corollary 5.20** (label `cor:HDG=HtiOKB`). "Let `G` be an ample groupoid, with locally compact
   Hausdorff unit space `G^(0)` without isolated points. Assume that `G` is minimal and has
   comparison. Then `H_*(D(G), C) ≅ H_*(D(R × G), C) ≅ H_*(Ω~^∞_0 K(B_G), C)` for all abelian
   groups `C` and all `* >= 0`."
   - It rests on **Theorem 5.19** (label `thm:HDG=HtiOKB`), which states the same isomorphism for
     `D(R × G)` with no hypotheses on `G`.
   - The text of §5.4, immediately before Theorem 5.19, defines `Ω~^∞_0 K(B_G)` as "the universal
     cover of `Ω^∞_0 K(B_G)`". The same passage defines `D(G)` as "the subgroup of `F(G)` generated
     by commutators".
   - This is item 2.
3. **Proof of Theorem 6.12** (label `thm:H2H0H1H1`). "Let `S` be the sphere spectrum. The
   Atiyah-Hirzebruch spectral sequence ... has `E^2_{p,q} = H~_p(K(B_G), π_q(S))` and converges to
   `π_{p+q}(K(B_G))`. Since the Atiyah-Hirzebruch spectral sequence is a first quadrant spectral
   sequence ...". This is item 3.
4. **Recorded examples (item 4).**
   - **§2.3.2, "Groupoid homology for examples":** "For a transformation groupoid `G = Γ ⋉ X` ...
     groupoid homology is canonically isomorphic to group homology with coefficients in the
     `Γ`-module `C_c(X, C)`".
   - **§2.2.2, "Transformation groupoids":** "Suppose that `Γ` is countably infinite, that `X` is
     compact, metrizable and totally disconnected, and that the `Γ`-action on `X` is free. Then
     the transformation groupoid `G = Γ ⋉ X` has comparison if all finitely generated subgroups of
     `Γ` have subexponential growth [DZ]".
   - **§2.2.3, "Tiling groupoids":** "For aperiodic, repetitive tilings with finite local
     complexity, the corresponding tiling groupoids are étale, minimal, have unit spaces
     homeomorphic to the Cantor space, and are almost finite by [IWZ], hence have comparison."
   - **§6.4, "Examples":** "let `G` be the groupoid attached to the classical Penrose tiling. Then
     `H_*(G) ≅ Z^8` if `*=0`, `Z^5` if `*=1`, `Z` if `*=2`, `{0}` otherwise."
   - **Remark 6.13:** groupoid homology is Morita invariant ("see for instance [Mat12, §3] or
     [Mil, §4]").

**Scope of the source check.** A grep of the source for "finitely presented", "type F" and `FP_`
finds only background, in §2.5 (Examples of topological full groups), on type `F_n` examples of
other authors.
