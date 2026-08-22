---
rg: 2
id: relative-kazhdan-bimodule-upgrades-finite-covariance
kind: claim
title: An exact relative-Kazhdan covariance bimodule upgrades finite tests to the whole module
artifacts:
  - research/artifacts/whole-module-kazhdan-mixed-word-audit-2026-08-21.md
distinct_from:
  relative-kazhdan-bimodule-requires-whole-module-covariance: that shows the canonical factor construction does not automatically descend; this proves the dimension-free conclusion once a genuine bimodule with the prescribed module restriction has been supplied.
  infinite-character-actor-word-energy-interface: that asks the finite presentation to supply such control; this is the abstract relative-property-T estimate after the correction gate.
---

Let `Gamma=M rtimes A` have relative property `(T)` with respect to `M`.
Choose a finite relative Kazhdan set `Q subset Gamma` and constant `kappa>0`.
Let `rho:M->U(d)` and `pi:A->U(d)` be exact, fix `s in A`, and suppose there
is a genuine unitary representation `Theta_s` of `Gamma` on `L^2(M_d)` whose
restriction to `M` is

```text
Theta_s(m)X=rho(s m) X rho(m)^*.                        (RKU1)
```

Assume moreover that, for `xi=pi(s)`, the finite displacements
`||Theta_s(q)xi-xi||_2`, `q in Q`, are bounded by `epsilon`.  Then

```text
sup_(m in M) ||rho(s m)pi(s)rho(m)^*-pi(s)||_2
   <= 2 epsilon/kappa.                                  (RKU2)
```

Equivalently, finite Kazhdan-set covariance controls the full whole-module
covariance with a dimension-independent constant.  Combining `(RKU2)` with
the whole-module averaging identity `(IWE2)` controls the complete character
transport energy.

