---
rg: 2
id: generic-limit-of-subshift-sl-models-is-simple-kazhdan
kind: claim
title: In the Cantor set of infinite marked limits of the finite simple models SL_{3N}(F_2), the simple Kazhdan limits G_X form a dense G_δ, and the generic limit is over a regular Toeplitz subshift
distinct_from:
  subshift-algebra-groups-embed-in-marked-groups: that proves Y ↦ G_Y is a homeomorphism onto a closed set; this identifies the closure of the periodic-word finite models inside it and proves that simplicity is generic there
  finite-simple-groups-converge-to-simple-kazhdan-group: that shows each G_X over a minimal X is a limit of finite simple groups; this describes the whole limit set topologically and the generic member
artifacts:
  - research/artifacts/sk-free-2-generic-limits-2026-09-13.md
---

**ESTABLISHED (unreviewed)** via `generic-limit-of-subshift-sl-models-is-simple-kazhdan-proof`.

Fix a finite alphabet `A` with `|A| ≥ 2`. The note's finite models are the marked groups `(SL_{3N}(F_2), ρ_y(e_ij(1)), ρ_y(e_ij(τ_s)))` over periodic words `y`. Their closure in the space of marked groups is these isolated points together with a Cantor set `𝒞_A = {G_Y : Y ⊆ A^Z infinite chain transitive}`, which is homeomorphic to the closure of the infinite transitive subshifts. In `𝒞_A`:
- the simple groups, exactly the `G_X` with `X` infinite minimal, form a dense `G_δ` that is not `F_σ`, and the non-simple limits are dense;
- a generic limit is `G_X` with `X` a regular Toeplitz subshift, uniquely ergodic, of zero entropy, strongly orbit equivalent to the universal odometer, with rank-one dimension group;
- a generic limit has unsolvable word problem.

So the generic infinite limit of this expander family of finite simple groups is an infinite simple Kazhdan LEF group.

**Review (sk-verify-15, 2026-09-13): PASS.** Boundary of the models (no aliasing for N > 2λ, Euler walks, isolation), Lemma 1 (admissible = closure of infinite transitive), Lemma 2 (Cantor, minimal G_δ dense with dense complement, not F_σ) and the three conclusions re-derived; Pavlov–Schmieding checked at source. See `research/artifacts/sk-verify-15-2026-09-13-part3.md` §4.

**Review (sk-verify-16, 2026-09-13): PASS.** Re-derived: window dependence and the homeomorphism onto a closed set, admissible = T̄′[A], minimality G_δ and dense (Pavlov–Schmieding Thm 1.3(1) on the open T̄′ ∩ S[A], by their Lemma 2.3), non-minimal SFT approximants, Baire, and meagerness of recursive languages. See `research/artifacts/sk-verify-16-2026-09-13.md` §7.
