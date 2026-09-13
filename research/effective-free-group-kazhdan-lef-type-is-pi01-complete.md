---
rg: 2
id: effective-free-group-kazhdan-lef-type-is-pi01-complete
kind: claim
title: The LEF type of the Kazhdan elementary groups over effectively closed minimal topologically free free-group subshifts is Pi-zero-one complete on the promise class
distinct_from:
  effective-free-group-kazhdan-lef-type-is-pi01: that is the upper bound; this is hardness on the same promise class.
artifacts:
  - research/artifacts/un-open-6-tarski-complexity-2026-09-13.md
---

**OPEN.** With the notation of `effective-free-group-kazhdan-lef-type-is-pi01`: there is a computable map
`M ↦ e(M)` from Turing machines to indices with `e(M) ∈ 𝒫` for every `M`, such that `X_(e(M))` carries an invariant
probability measure iff `M` never halts. Then "every `EL_N(R_e)` is LEF" is `Π⁰₁`-complete on `𝒫`, and "no MF quotient
from some rank on" is `Σ⁰₁`-complete.

## Attempts

- **Without the promise it is easy, and useless.** Let `X_(e(M))` be the full shift until `M` halts, and then forbid
  every letter. Measure existence is then `Π⁰₁`-hard, but `X_(e(M))` is empty when `M` halts, so `e(M) ∉ 𝒫`. The whole
  difficulty is keeping minimality and topological freeness in both outcomes.
- **Amenable acting groups are dead.** For amenable `Γ` every nonempty subshift carries an invariant measure, so the
  predicate is trivially true; hardness needs a non-amenable acting group. `F_r` is the natural test.
- **Switch construction (sketch, not proved).** Build `X_(e(M))` hierarchically: level-`s` skeletons are odometer-like
  (finite Schreier-graph towers, invariant frequencies) while `M` has not halted by stage `s`; if `M` halts at stage
  `s0`, the skeletons from level `s0` on insert boundary-like paradoxical blocks, giving a finite paradoxical
  decomposition (a `Σ⁰₁` certificate). Firewalls to check:
  - the limit must be minimal in both outcomes, so the paradoxical blocks must recur uniformly;
  - effectiveness must survive, so the forbidden list at stage `s` may depend only on the first `s` steps of `M`;
  - a late halt must not leave a residual measure on the odometer part, since paradoxicality is a global property
    of the unit class.
- **Upper bound firewall.** `𝒫` itself is not known to be decidable; a reduction must land in `𝒫` by construction,
  not by a test.
