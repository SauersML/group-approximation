---
rg: 2
id: free-minimal-subshifts-all-rf-iff-virtually-cyclic
kind: claim
title: Every free minimal subshift over a finitely generated group is residually finite exactly when the group is virtually cyclic
distinct_from:
  measure-rf-class-is-exactly-virtually-free-groups: that quantifies over Cantor actions carrying a full-support invariant measure and conjectures the virtually free groups; this quantifies over free minimal subshifts with no measure hypothesis and conjectures the virtually cyclic groups.
artifacts:
  - research/artifacts/sk-general-actions-b-converse-map-2026-09-13-part1.md
---

**OPEN.** Let `Γ` be finitely generated and infinite. Conjecture: every free minimal subshift `X ⊆ A^Γ` is residually finite (Kerr–Nowak), equivalently window-periodic, iff `Γ` is virtually cyclic.

**Meaning for the note.** Periodic approximation is how the note gets finite models. This conjecture says `Z` is, up to finite index, the only acting group for which periodic approximation works for every free minimal subshift.

## Attempts

- **(⇐) proved** (artifact §3, Proposition C).
  - A virtually cyclic group has a normal infinite cyclic subgroup of finite index.
  - Krylov–Bogolyubov plus averaging over the finite quotient gives an invariant measure, of full support by minimality.
  - `virtually-free-group-measure-actions-are-rf` then makes the action RF.
- **(⇒) proved when `Γ` is not residually finite.** `gjs-countable-groups-have-free-minimal-subflows` gives a free minimal subshift, and `free-rf-actions-force-residually-finite-groups` shows it is not RF.
- **(⇒) proved when `Γ` has a weakly aperiodic SFT `Y`** (nonempty, no finite orbit), artifact Proposition D.
  - Take a minimal subset `M` of `Y × W`, with `W` a free minimal subflow.
  - `M` is free, minimal and a subshift.
  - It is an extension of a closed invariant subset of `Y` without finite orbits, so it is not RF (`extensions-of-aperiodic-sfts-are-not-residually-finite-actions`).
- **Lifting lemma (proved, artifact §3).** A weakly aperiodic SFT on a subgroup `H ≤ Γ` induces one on `Γ` through `{x : (g^(-1)·x)|_H ∈ Y for all g}`.
- **Reduction.** (⇒) therefore follows from the **Carroll–Penland conjecture** (arXiv:1502.03195, abstract level, bounded check): a finitely generated group has a weakly aperiodic SFT iff it is not virtually `Z`.
  - Known cases, recalled and not read from the PDFs here: `Z^2` (Berger); free groups (Piantadosi); lamplighters (Cohen, arXiv:1710.03707); one-ended hyperbolic groups (Cohen–Goodman-Strauss–Rieck, arXiv:1706.01387); virtually nilpotent groups other than virtually `Z` (Carroll–Penland); Baumslag–Solitar groups (Aubrun–Kari).
  - By the lifting lemma these cover every group containing one of them.
- **Where it dies.** The remaining groups are residually finite, not virtually `Z`, and contain no subgroup known to carry a weakly aperiodic SFT, for example some infinite torsion groups.
  - For those, a non-RF free minimal subshift needs either a weakly aperiodic SFT or a different mechanism.
  - Measure-free subshifts would do for non-amenable groups, since RF forces an invariant measure. That route needs Tarski's theorem, which is not imported here.
