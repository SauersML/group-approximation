---
rg: 2
id: deligne-triple-cover-exact-mf-radical
kind: claim
title: The MF radical of Deligne's triple cover is exactly its order-three center
goal: true
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  deligne-triple-cover-finite-residual-is-center: that computes the intersection of kernels of finite quotients; this computes the smaller intersection of kernels of all norm-matrix-corona representations.
  deligne-triple-cover-central-generator-is-mf-radical: that is the hard inclusion C_3 <= Rad_MF(E_3); this packages it with the unconditional reverse inclusion to give the exact radical.
---

For Deligne's connected triple cover

```text
1 -> C_3 -> E_3 -> Sp_4(Z) -> 1
```

one has

```text
Rad_MF(E_3) = C_3.                                     (DER1)
```

In particular, for either generator `z` of `C_3`,

```text
z in Rad_MF(E_3).                                      (DER2)
```

## Attempts

- The reverse inclusion is unconditional:
  `Rad_MF(E_3) <= Res_fin(E_3)=C_3`.  The forward inclusion is exactly
  `deligne-triple-cover-central-generator-is-mf-radical`.
- Because `C_3` has prime order and the universal MF quotient detects
  triviality of the radical, `(DER1)` is equivalent to the open claim that
  `E_3` is not MF.  Finite-dimensional invisibility alone does not establish
  this asymptotic operator-norm assertion.
- `deligne-triple-cover-mf-radical-dichotomy` now records the unconditional
  result: the radical is either `1` or the order-three covering kernel
  `C_3`.  The nontrivial branch is equivalently the open point-norm sector
  exclusion `deligne-nontrivial-maslov-opnorm-sectors-are-empty`.
- **2026-09-18, swarm-0917-w7-w7-deligne-last1 (calibration): the last
  mile is blocked, and the manuscript's own mechanism is provably silent.**
  - *Blocked routes.* Both shortest routes end in one open leaf, and each
    leaf is at least flagship-hard:
    - LLP route: `sp4-mod3-twisted-fibres-have-llp` implies the HS gap,
      hence non-hyperlinearity of `E_3`. It also implies the open LLP of
      `C*(F2 x F2)` (`mod3-twisted-fibre-llp-forces-f2xf2-llp`).
    - MH1 route: `maslov-diverging-positive-lifts-have-vanishing-high-degree-mass`
      is equivalent to the HS gap
      (`high-degree-range-mass-is-exactly-tracial-ucp-liftability`).
  - *Class killed.* `deligne-cover-compression-defects-are-trivial`
    (ESTABLISHED) proves `D(Delta, L) = 1` for every subgroup `Delta` of
    every Deligne cover `Gamma_n` of `Sp_(2g)(Z)` and every `L <= Delta`.
    The same holds for every central quotient of `E_3` that keeps `z`.
    - Every compression-defect non-MF criterion therefore dies at "exhibit
      `1 != w in D(E_3, L)`". This covers normal-Kazhdan, finite-normal,
      central-defect-element, locally-finite, mark-stability and the
      manuscript's compression criterion.
    - The kill holds for Kazhdan or non-Kazhdan `L`, thin or arithmetic.
    - The invariant is the Guichardet--Wigner quasimorphism
      (`sp2g-central-commutators-of-universal-lifts-are-torsion`).
  - *Consequence for decomposition.* A thin rigid subgroup
    (`sp4-deligne-rigid-infinite-index-subgroup-exists`) cannot be exploited
    through compression. Any proof of `(DER2)` must use operator-norm data
    that no source-side commutator identity encodes, or pass through an
    overgroup with an extension theorem.
