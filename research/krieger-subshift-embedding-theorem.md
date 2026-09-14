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

## Review
- **sk-verify-21 PASS-WITH-FIXES at secondary-source level (2026-09-14, `research/artifacts/sk-verify-21-2026-09-14.md` §3):** read the arXiv:2606.25475 e-print source on MSI:
  - the theorem `\label{Krieger}` at l.112;
  - `q_n` = number of points of least period `n` (l.110);
  - embedding = injective sliding block code (l.220).
  - Crossref confirms W. Krieger, ETDS 2(2) (1982) 195–202. The primary paper was not opened.
  - The consequence is re-derived: `q_n(Z) = 0`, `h(Z) = 0 < log 2`, and the full 2-shift is a mixing SFT. Fixes:
  - (K1) In the verbatim quote, the source reads "if and only if", not "iff".
  - (K2) In `krieger-subshift-embedding-theorem-citation`, credit the restatement: after "arXiv:2606.25475," insert "B. Marcus and T. Meyerovitch,".
