---
rg: 2
id: minimal-z2-subshift-derived-full-groups-are-fg-simple
kind: claim
title: Derived subgroups of full groups of free minimal Z^d-subshifts are finitely generated infinite simple groups
distinct_from:
  periodic-approximable-subshifts-host-no-fp-simple-group: That is an obstruction to finite presentation for subgroups of full groups of subshifts with periodic approximations; this imports finite generation and simplicity of the derived subgroup for every free minimal Z^d-subshift, including aperiodic SFTs.
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

**ESTABLISHED (import).** Let `X ⊆ A^{Z^d}` be an infinite minimal subshift on which `Z^d` acts freely. Then the derived subgroup `D([[Z^d ~ X]])` of the topological full group is finitely generated, infinite and simple, and it lies in every nontrivial normal subgroup of `[[Z^d ~ X]]`.

**Sources.** All were read from arXiv TeX sources on MSI; see the artifact, Section 1.
- **Finite generation:** Chornyi--Juschenko--Nekrashevych, arXiv:1602.04255, Theorem `main`. It applies because a free action is faithful.
- **Simplicity and the normal-subgroup property:** Matui, as quoted in ChJN line 207, and Nekrashevych, arXiv:1511.08241, Theorem 1.1 for `A(G)` of minimal groupoids of germs. The two groups coincide for abelian acting groups (ChJN line 86).
- **Infinite:** order-3 elements cycling disjoint clopen sets generate the derived subgroup (ChJN line 209), and a perfect `X` has infinitely many of them.
