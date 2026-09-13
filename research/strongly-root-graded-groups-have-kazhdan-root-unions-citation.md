---
rg: 2
id: strongly-root-graded-groups-have-kazhdan-root-unions-citation
kind: route
title: Import the strong-grading Kazhdan criterion and Kazhdan-ratio observation from Ershov–Jaikin-Zapirain–Kassabov
target: strongly-root-graded-groups-have-kazhdan-root-unions
requires: []
---

Literature import. M. Ershov, A. Jaikin-Zapirain, M. Kassabov, *Property (T) for groups graded by root systems*,
arXiv:1102.0031. Checked 2026-09-12 against the TeX source `2014gradedT0310.tex`, fetched with curl on MSI and
read locally.

- **Part (a)** is the theorem labelled `thm:main2`, which the introduction calls "the central result of this
  paper". It reads: "Let `Φ` be an irreducible classical root system of rank `>= 2`, and let `G` be a group which
  admits a strong `Φ`-grading `{X_α}`. Then `∪ X_α` is a Kazhdan subset of `G`."
- **Definitions.** The grading definition, with (i) generation and (ii) the commutator condition for
  `α ∉ R_(<0) β`, opens the subsection "Groups graded by root systems". "Strong at the pair `(γ, Φ_f)`" and "strong"
  are defined later in that subsection, right after the lemma that the core subgroup is normal in the Borel subgroup.
  The `A_2` case is the example just before Lemma `corebase`: "the core of the Borel set `{α, β, α+β}` is `{α+β}` and
  the boundary is `{α, β}`."
- **Part (b)** is Observation `Kazhrat`, items (iii) and (ii).
  - (iii) says `kappa(G, S) >= kappa(G, B) kappa_r(G, B; S)`. Here `kappa_r(G, B; S)` is the largest `δ` such that
    `(S, δ ε)`-invariant vectors are `(B, ε)`-invariant.
  - (ii) says `kappa(G, H; S) <= 2 kappa_r(G, H; S)` for normal `H`. The source proves it by splitting
    `V = V^H ⊕ (V^H)^⊥`, following Shalom, Cor. 2.3.
- **Kazhdan constants.** The source defines `kappa(G, S)` and Kazhdan subsets in its §2, and defines property (T)
  as having a finite Kazhdan subset.

Only these statements are imported. Theorem numbers are not recorded, because the source numbers theorems within
sections and the published numbering was not rechecked.
