---
rg: 2
id: free-minimal-subshift-el-groups-all-lef-iff-virtually-cyclic
kind: claim
title: The elementary groups of every free minimal subshift over a finitely generated group are LEF exactly when the group is virtually cyclic
distinct_from:
  free-group-cantor-elementary-group-lef-iff-invariant-measure: that decides LEF action by action for free acting groups; this asks for which acting groups LEF holds for every free minimal subshift at once.
  free-minimal-subshifts-all-rf-iff-virtually-cyclic: that is the dynamical (residual finiteness) version; this is the group-theoretic version, which could be strictly weaker if non-RF subshifts had matricial crossed products.
artifacts:
  - research/artifacts/sk-general-actions-b-converse-map-2026-09-13-part1.md
---

**OPEN.** Let `Γ` be finitely generated and infinite, and `q` a prime power. Say `Γ` has (∀LEF) if `EL_N(LC(X,F_q) ⋊ Γ)` is LEF for every free minimal subshift `X ⊆ A^Γ` and every `N >= 3`. Conjecture: `Γ` has (∀LEF) iff `Γ` is virtually cyclic.

Every such `EL_N(LC(X,F_q) ⋊ Γ)/Z` is infinite, finitely generated, simple and Kazhdan (`steinberg-elementary-groups-are-simple-mod-centre`, EJZ). So the conjecture says `Z`, up to finite index, is the only acting group for which the note's theorem holds for every free minimal subshift.

## Attempts

- **(⇐) proved.** By artifact Proposition C every free minimal subshift over a virtually cyclic group is RF. `residually-finite-actions-give-matricial-crossed-products` then gives LEF.
- **(⇒) proved when `Γ` is not LEF**, at every `N >= 3`. `Γ` embeds in `EL_N/Z` by `crossed-product-group-embeds-in-projective-elementary-group`.
- **(⇒) proved when `Γ ⊇ F_2`.**
  - `f2-groups-have-paradoxical-free-minimal-subshifts` gives a free minimal subshift with no invariant measure.
  - So the crossed product is not matricial (`matricial-steinberg-algebras-have-invariant-measures`).
  - So `EL_4` is not LEF (`lef-el-groups-force-exactly-matricial-simple-ring`).
- **Sketch, import missing: every non-amenable `Γ`.** Tarski's theorem gives a paradoxical decomposition, and the `F_2` construction goes through with finitely many pieces.
- **Where it dies: amenable LEF groups that are not virtually cyclic.**
  - Non-RF free minimal subshifts exist over them in all known cases (`free-minimal-subshifts-all-rf-iff-virtually-cyclic`).
  - The missing step is "not RF ⟹ not matricial". It fails to follow from the invariant measure, which always exists for amenable groups.
  - For `Z^2` this is decided by `labbe-wang-shift-crossed-product-is-not-exactly-matricial`: exact matricial models of an aperiodic SFT ring are periodic quantum tilings (`labbe-tiles-admit-periodic-quantum-tilings-at-every-scale`).
  - If Labbé's crossed product is exactly matricial, `Z^2` could still have (∀LEF) for all we know, and the conjecture would need a different witness.
