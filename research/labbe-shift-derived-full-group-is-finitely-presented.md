---
rg: 2
id: labbe-shift-derived-full-group-is-finitely-presented
kind: claim
title: The derived subgroup of the topological full group of Labbé's minimal aperiodic Wang shift is finitely presented
distinct_from:
  periodic-approximable-subshifts-host-no-fp-simple-group: That kills finitely presented simple subgroups for subshifts with periodic approximations, including minimal Z-subshifts; this asks for finite presentation over Labbé's aperiodic Z^2 SFT, where that obstruction provably cannot fire.
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

**OPEN.** Let `Omega_U` be Labbé's 19-tile Wang shift (`minimal-aperiodic-wang-shift-exists`). The group `D([[Z^2 ~ Omega_U]])` is finitely presented.

## Attempts

- **Refutation through SFT neighbourhoods (the suggested mechanism "finite presentation forces periodic points").** Dead as it stands.
  - `fp-subshift-full-group-subgroups-extend-to-sft` produces an SFT neighbourhood, and `Omega_U` is already one.
  - Any argument that reads only finite orbits of SFT neighbourhoods is blind here, by `sfts-without-finite-orbits-are-not-residually-finite-actions`.
  - That also rules out Ma's LEF theorem and Grigorchuk--Medynets-style LEF arguments as stated.
- **Positive results.** None apply.
  - Matui's finite presentation (arXiv:1210.5800) covers one-sided irreducible SFT groupoids, which are compressible and so non-amenable (`amenable-full-group-forces-invariant-measure`).
  - Nekrashevych's finitely presented groups (arXiv:1312.5654, lines 50–90) come from expanding maps and hyperbolic groupoids.
  - Neither covers two-dimensional SFT groupoids, and the sources read contain no finite presentation criterion for `Z^2`-SFT full groups.
- **Isolation.** No contradiction found. A finitely presented infinite simple group is isolated in the space of marked groups. `D([[Omega_U]])` is sofic by the Elek--Szabó remark in Elek--Monod line 128, and soficity gives no contradiction with isolation.
