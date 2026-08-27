---
rg: 2
id: iwahori-sector-closure
kind: route
title: Dogon–Vigdorovich sector closure via the Iwahori endpoint
target: non-hyperlinear-group
requires:
  - iwahori-local-global-defect-question
  - dv-s-arithmetic-hs-stable-nonhyperlinear-extension
artifacts:
  - notes/HIGHEST_YIELD_NONHYPERLINEAR_ATTACK.md
  - research/artifacts/two-paper-ingestion-2026-08-19.md
---

A positive answer to `iwahori-local-global-defect-question` — the printed
Dogon–Vigdorovich Question 1.2, that the global distance `D(π)` to a compatible
representation is controlled by a modulus in the local Iwahori defect
`def(π)` — gives Hilbert–Schmidt stability of the amalgam
`SL₂(ℤ) *_B SL₂(ℤ) ≅ SL₂(ℤ[1/2])`. That group is an `S`-arithmetic lattice
in `SL₂(ℝ) × SL₂(ℚ_p)` satisfying the hypotheses of
`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`, so it has a
non-hyperlinear finite central extension, which is the goal. This is their
Corollary 1.3, and it is the composition they perform; this route does not
re-derive it.

The candidate produced is an amalgamated free product of virtually free groups
over a finite index subgroup, and by
`sl2-half-central-extension-not-residually-amenable` it is not residually
amenable — so it is not already known to be hyperlinear.

**Route history.** Until 2026-08-19 this route required
`iwahori-outlier-repair` directly, and the literature step above lived only in
this body as prose. The prerequisite is unchanged in substance: the repair
theorem now feeds the question through
`iwahori-defect-question-from-outlier-repair`, so the same chain
`edge-pair-mixed-gap-collapse → iwahori-outlier-localization →
iwahori-outlier-repair → iwahori-local-global-defect-question → here` reaches
the goal, with the two imported theorems now checkable nodes rather than an
uncited assertion.

The original sector reasoning, kept: per HIGHEST_YIELD (2026-08-14), the mixed
edge representation converges to the regular character of `B/⟨z⟩ ≅ ℤ*C₂`;
Kesten's gap localizes the almost-invariant identity vector in a sparse
low-energy window, which is a bimodule decomposing into low-energy
`Hom(θⱼ, πᵢ)` blocks.
