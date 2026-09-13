---
rg: 2
id: labbe-shift-is-a-toral-rotation-coding-citation
kind: route
title: Labbé, Markov partitions for toral Z^2-rotations featuring Jeandel-Rao Wang shift and model sets, arXiv:1903.06137
target: labbe-shift-is-a-toral-rotation-coding
requires: []
artifacts:
  - research/artifacts/labbe-shift-wall-rigidity-2026-09-13.md
---

Source: S. Labbé, *Markov partitions for toral Z^2-rotations featuring Jeandel-Rao Wang shift and model
sets*, arXiv:1903.06137. The TeX source was read on MSI at
`/scratch.global/sauer354/ex/ex2-labbe-quantum-rigidity/src/1903.06137.d/common-content.tex`. Items are
cited by LaTeX label and source line; the printed theorem numbers were not checked.

- **Items 1–4.** Theorem `thm:OmegaU-partition` (lines 539–559): "The Wang shift `Ω_U` has the following
  properties: (i) the subshift `X_(P_U,R_U)` is minimal, aperiodic and is equal to `Ω_U`, (ii) `P_U` is a
  Markov partition for the dynamical system `(T^2,Z^2,R_U)`, (iii) `(T^2,Z^2,R_U)` is the maximal
  equicontinuous factor of `(Ω_U,Z^2,σ)`, (iv) the set of fiber cardinalities of the factor map
  `Ω_U -> T^2` is `{1,2,8}`, (v) the dynamical system `(Ω_U,Z^2,σ)` is strictly ergodic and the
  measure-preserving dynamical system `(Ω_U,Z^2,σ,ν)` is isomorphic to `(T^2,Z^2,R_U,λ)`."
- **The rotation.** Lines 522–528: `R_U^n(x) = x + φ^(-2) n` on `T^2 = R^2/Z^2`.
- **Markov partitions.** Definition `def:Markov` (line 1089) requires a symbolic representation.
  Definition `def:symb-repr` (line 1073): every `w` has `∩ cl D_n(w)` equal to one point.
- **Item 2, factor map.** Proposition `prop:factor-map` (line 1427).
- **Item 4, entropy.** Zero entropy follows from (v) by the variational principle.
- **Item 5.** Lemma `lem:tiling-one-to-one` (line 1348) gives injectivity. Lemma `lem:closure-of-tilings`
  (line 1284) gives that `X_(P,R)` is the closure of the image of generic points.
- **Item 6.** Read from the vector figure `article3_partitionU.pdf` in the same source. Its content stream draws
  straight segments in the frame `[0, 85.04042]^2`, whose endpoint coordinates normalize to the listed
  golden-mean values. For example `32.48314/85.04042 = φ^(-2)` and `20.07536/85.04042 = φ^(-3)`. The
  directions were recomputed from the endpoints. The artifact, Section 0, lists one interior segment of each
  direction.
