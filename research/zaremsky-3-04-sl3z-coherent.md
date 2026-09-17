---
rg: 2
id: zaremsky-3-04-sl3z-coherent
kind: claim
title: "Zaremsky Problem 3.4 resolved: is SL_3(Z) coherent?"
root: true
distinct_from:
  sl3z-is-coherent: that claim is the affirmative answer; this is the question, established by either answer
  sl3z-is-incoherent: that claim is the negative answer; this is the question, established by either answer
artifacts:
  - research/artifacts/zp-open-status-sections-2-4-2026-09-13-part1.md
---

M. C. B. Zaremsky, *Some open problems* (version of July 12, 2026,
https://zaremsky.github.io/open_problems.pdf), Section 3, Problem 4, verbatim:
"Is SL3(Z) coherent? (Meaning every finitely generated subgroup is finitely
presented.) (Famous problem of Serre.)"

This claim is the question. It is established only through an answer route:

- **Yes**: `zaremsky-3-04-by-yes` requires `sl3z-is-coherent`
  (every finitely generated subgroup of `SL_3(Z)` is finitely presented).
- **No**: `zaremsky-3-04-by-no` requires `sl3z-is-incoherent`
  (some finitely generated subgroup of `SL_3(Z)` is not finitely presented).

Never write a `requires: []` route into this claim.

**Precise reading.** A group is coherent when every finitely generated
subgroup is finitely presented. Coherence is a commensurability invariant: it
passes to subgroups, and a group containing a coherent subgroup of finite
index is coherent (a finitely generated subgroup meets it in a finite-index,
finitely generated, hence finitely presented subgroup). So the question is the
same for `SL_3(Z)`, `GL_3(Z) = SL_3(Z) x {±I}`, any congruence subgroup, and
any group commensurable with them.

**Context.** The question is attributed to Serre (Zaremsky's note; the
original problem-list reference was not re-verified here). For `n >= 4`,
`SL_n(Z)` contains `SL_2(Z) x SL_2(Z)`, hence `F_2 x F_2`, which contains
Stallings' finitely generated, not finitely presented subgroup (Stallings
1963), so `SL_n(Z)` is incoherent for `n >= 4`; the same holds for
`Sp_4(Z)`. The case `n = 3` is the one Zaremsky lists as open. The ZP status
sweep (artifact above, bounded web and arXiv search, 2026-09-13) found no
answer.

Structural facts this region records for any attack (proved in their own
nodes): centralizers of infinite-order elements of `SL_3(Z)` are solvable,
so `SL_3(Z)` contains no `Z x F_2` and no `F_2 x F_2`; every finitely
generated subgroup of `SL_3(Z)` that is not Zariski dense is finitely
presented, so any witness to incoherence is a thin (Zariski-dense,
infinite-index) subgroup.

## Attempts

- 2026-09-13 (z3-04-sl3z-incoherent): incoherence side. Stallings' mechanism
  through `F_2 x F_2` is dead in `SL_3(Z)`. Live criteria: a subgroup of
  cohomological dimension two with nonzero Euler characteristic and a
  fibration onto `Z`, or a virtually RFRS subgroup of cohomological dimension
  two with positive second L²-Betti number. See `sl3z-is-incoherent`.
- 2026-09-13 (z3-04-sl3z-coherent): coherence side; see `sl3z-is-coherent`.
- 2026-09-17 (sw-097, inverter): two obstructions to incoherence witnesses.
  `sl3r-simply-connected-domain-subgroups-are-coherent` shows that a
  subgroup acting properly on a simply connected open subset of the plane,
  the dual plane, the flag manifold or `R^3 \ 0` is coherent. So convex or
  Vinberg certificates of faithfulness cannot produce a witness.
  `sl3z-racg-witnesses-are-antiflag-configurations` puts any faithful
  right-angled Coxeter witness in anti-flag normal form and proves rules
  R1–R5, which exclude grid, `Q_4` and Clebsch witnesses even over `R`.
  Every induced square of a witness graph comes from a rigid shared-centre or
  shared-axis pattern, and girth-5 witnesses have distinct centres and axes.
  Bounded searches found no configuration with positive Euler characteristic
  satisfying the rules.
