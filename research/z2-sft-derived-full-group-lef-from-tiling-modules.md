---
rg: 2
id: z2-sft-derived-full-group-lef-from-tiling-modules
kind: claim
title: If the local tiling algebras of a free minimal Z^2 SFT have nonzero finite-dimensional modules at every scale, its derived full group is LEF
distinct_from:
  zd-derived-full-group-fp-excludes-periodic-quantum-tilings: that derives non-finite-presentation from the same modules; this derives LEF, which is stronger for an infinite simple group, by replacing finite presentation with the trivial-or-exact dichotomy for truncated presentations.
  labbe-shift-derived-full-group-is-lef: that is the LEF question for Labbé's shift; this is a sufficient criterion for any free minimal Z^2 SFT.
artifacts:
  - research/artifacts/labbe-periodic-quantum-tilings-obstruct-fp-2026-09-13.md
  - research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md
---

**ESTABLISHED (unreviewed).**

**Statement.** Let `X ⊆ A^(Z^2)` be a free minimal subshift of finite type and `G = D([[Z^2 ~ X]])`.
Suppose that for every `D` there is a field `k_D` such that the local tiling algebra `A_D(X, k_D)` of
`sft-crossed-product-fp-iff-quantum-rigid` has a nonzero finite-dimensional module. Then `G` is LEF.

**Contrapositive.** If `G` is not LEF, there is `D_0` such that for all `D >= D_0` and every field `k`,
`A_D(X, k)` has no nonzero finite-dimensional module. So refuting LEF entails finite-dimensional quantum
rigidity at large scale. Since LEF of an infinite simple group excludes finite presentation, this
implies `zd-derived-full-group-fp-excludes-periodic-quantum-tilings`.

**Consequences for Labbé's shift.**
- A periodic quantum tiling of Labbé's tiles at every scale (`labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`)
  gives LEF, not only non-finite-presentation: route `labbe-lef-via-periodic-quantum-tilings`.
- Every refutation of `labbe-shift-derived-full-group-is-lef`, in particular any proof of the
  non-spatial crux (C2), must prove along the way that contextual periodic quantum tilings of Labbé's
  tiles do not exist at large scale.

**Model test.** Calibration only, same proof, not claimed separately: for an infinite minimal
`Z`-subshift, the one-dimensional modules from periodic points of Markov approximations (artifact,
Remark 2.2) exist at every scale, and the argument gives LEF of `D([[phi]])`, in agreement with
Grigorchuk–Medynets. For an aperiodic `Z^2`-SFT all one-dimensional modules are absent, so only
contextual modules can feed the criterion. A trivial module `V = 0` is excluded by hypothesis.

Route: `z2-sft-derived-full-group-lef-from-tiling-modules-proof`.
