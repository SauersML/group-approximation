---
rg: 2
id: minimally-almost-periodic-groups-are-not-pmf
kind: claim
title: Groups with no nontrivial finite-dimensional unitary representation are not purely matricial field; this covers every simple elementary group over a Steinberg algebra, including Pestov's group
distinct_from:
  binary-leavitt-unit-group-is-minimally-almost-periodic: that proves minimal almost periodicity for one Leavitt unit group through Thompson subgroups; this is the general no-PMF consequence, together with the Malcev criterion covering all infinite f.g. groups without finite quotients.
  infinite-kazhdan-group-with-mf-reduced-cstar: that asks for MF of the reduced algebra, which allows non-exact asymptotic representations; this only excludes genuine representations (PMF).
artifacts:
  - research/artifacts/un-reduced-cstar-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed).**

1. **No PMF.** Let `Γ ≠ 1` be such that every homomorphism `Γ → U(d)`, for every `d`, is trivial. Then no sequence of
   finite-dimensional unitary representations converges strongly to `λ_Γ`. In Magee–de la Salle's terms
   (arXiv:2312.03220v2, Def. 1.2), `Γ` is not PMF.
2. **Malcev criterion.** Every infinite finitely generated group with no nontrivial finite quotient satisfies the
   hypothesis of item 1.
3. **Application.** Let `k` be finite and `A_k(𝒢)` finitely generated, with `𝒢` as in
   `steinberg-elementary-groups-are-simple-mod-centre`, and `N ≥ 3`. Then `EL_N(A_k(𝒢))` and `EL_N(A_k(𝒢))/Z` are
   not PMF. This includes Pestov's group `S = EL_3(LC(X,F_q)⋊ℤ)/Z` (`simple-kazhdan-lef-group-from-minimal-subshift`)
   and the boundary-action group of `boundary-action-elementary-simple-kazhdan-not-mf`.

**Consequence for the measure side.** Any MF embedding of `C*_r(S)` has to use asymptotic representations that are
not close to genuine ones: for Pestov's group, the LEF models. So the open question
`directly-finite-subshift-el-n-reduced-cstar-is-mf` is about non-exact models only.

Proof route: `minimally-almost-periodic-groups-are-not-pmf-proof` (artifact §2.1).
