---
rg: 2
id: sl3-toeplitz-harmonic-pe-groups-are-simple
kind: claim
title: The projective elementary groups PE_N(R_T) of the SL_3(Z) Toeplitz harmonic ring are infinite simple groups with centre of order at most 2, and they are finitely presented exactly when E_N(R_T) is
distinct_from:
  sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational: that proves the ring is simple and K_1-rational; this is the group side, normal subgroups and the centre clause of E_N over it.
  sl3-toeplitz-harmonic-elementary-groups-are-fp: that is the open finite-presentation claim; this reduces the host premise for R_T to it.
  ample-steinberg-el-simple-mod-centre-without-hausdorff: that is for Steinberg algebras, whose coefficients are locally constant; this is for R_T, whose harmonic coefficient is not locally constant.
artifacts:
  - research/artifacts/gq-referee-b-sl3-toeplitz-harmonic-pe-groups-are-simple.md
  - research/artifacts/gq-referee-c-sl3-toeplitz-harmonic-pe-groups-are-simple.md
---

**ESTABLISHED** by `sl3-toeplitz-harmonic-pe-groups-are-simple-proof`. Referees `gq-referee-b` and `gq-referee-c` PASS
(`research/artifacts/gq-referee-b-sl3-toeplitz-harmonic-pe-groups-are-simple.md`,
`research/artifacts/gq-referee-c-sl3-toeplitz-harmonic-pe-groups-are-simple.md`). Both checked the Lean
signature against `R_T`. The claim is conditional on parts 1–3 of
`sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`, which have one referee pass (`gq-referee-a`).

## Statement

Let `R_T` be the ring of `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational` and `N >= 3`.

1. **Normal subgroups.** Every normal subgroup of `E_N(R_T)` is central or all of `E_N(R_T)`. So
   `PE_N(R_T) = E_N(R_T)/Z(E_N(R_T))` is an infinite simple group.
2. **Centre clause.** `Z(E_N(R_T)) = Λ_N(R_T)·I ⊆ {±I}`, a group of order at most 2.
3. **Finite presentation.** `PE_N(R_T)` is finitely presented if and only if `E_N(R_T)` is.
4. **Embedding.** For `N >= n+2`, `GL_n(Q)` embeds in `PE_N(R_T)`
   (`q-algebra-elementary-quotients-contain-gl-n-q`).

Hence, if `E_N(R_T)` is finitely presented for some `N >= n+2`, then `GL_n(Q)` embeds in a finitely
presented simple group. If this holds for infinitely many `N`, then `R_T` satisfies
`q-algebra-with-fp-simple-projective-elementary-group`, through
`q-algebra-host-via-sl3-toeplitz-harmonic-ring`.

## Position

**Update (2026-09-18).** `E_N(R_T)` is not finitely presented for any `N >= 3`
(`bounded-harmonic-rings-are-not-finitely-presented`, which refutes
`sl3-toeplitz-harmonic-elementary-groups-are-fp`). So `PE_N(R_T)` is simple but not finitely presented,
and `R_T` is not a host. The simplicity argument (local annihilation plus the Lean criterion) applies
unchanged to any finitely presented replacement that contains the clopen indicators.


This settles items (1) and (2) of the coordinator's group-side list for `R_T`. The simplicity of
`PE_N(R_T)` is no longer open. The only open condition on the group side is finite presentation of
`E_N(R_T)` (`sl3-toeplitz-harmonic-elementary-groups-are-fp`). Its known necessary conditions are the
two K-budget clauses of `sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget`.
