---
rg: 2
id: krieger-subshift-embedding-theorem
kind: claim
title: Krieger's embedding theorem — a subshift Z with h(Z) < h(Y) embeds into a mixing SFT Y iff q_n(Z) ≤ q_n(Y) for all n; so aperiodic zero-entropy subshifts embed into the full 2-shift
artifacts:
  - research/artifacts/sk-growth-gx-sturmian-2026-09-14-part1.md
---

**IMPORT (literature; secondary statement read at source, primary paper not opened).**

**Statement, verbatim from the secondary source.** "Theorem 1 (W. Krieger). Let Z be a subshift and Y a mixing SFT such that h(Z)<h(Y). Then Z embeds into Y iff q_n(Z)≤q_n(Y) for all n∈ℕ." Here `q_n` counts points of least period `n`, and "embeds" means there is an injective continuous shift-commuting map `Z → Y`.

**Consequence used on main.** If `Z` is an aperiodic subshift of topological entropy `0`, then `q_n(Z) = 0` for all `n` and `h(Z) = 0 < log 2 = h({0,1}^Z)`. So `Z` is conjugate to a subshift of `{0,1}^Z`, and some clopen `U ⊆ Z` has translates separating points.

**Consumers.** `piecewise-dyadic-level-models-give-non-uniform-growth-proof`. It also closes the verification gate recorded for sk-free-8's Corollary A2 (odometer factor, zero entropy) in the Attempts of `every-subshift-elementary-group-non-uniform-growth`, at secondary-source level.

Route: `krieger-subshift-embedding-theorem-citation`.
