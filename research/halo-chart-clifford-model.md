---
rg: 2
id: halo-chart-clifford-model
kind: route
title: Get the Clifford crossed product from halo-product / sofic-action permanence
target: kun-thom-clifford-crossed-product-ce
requires: []
artifacts:
  - notes/TRUE_LAMP_CHARTS_RECOVER_THE_SET_ACTION.md
  - notes/FALSE_HALO_ACTION_AUDIT.md
---

Apply Alekseev--Bradford (arXiv:2601.18742, Definition 4.23, Theorem 5.1,
Corollary 5.2) or Gao--Kunnawalkam Elayavalli--Patchell (arXiv:2401.04945,
Theorem 3.8) to the Clifford lamp group `C(X)`, using Clifford or unitary
labels in place of the commuting lamps to supply the sofic-action hypothesis.

Dead: `lamp-charts-recover-set-action` shows that any such chart system, for
any target class, proves the coset action sofic, which
`coordinate-action-not-sofic` refutes.  Relabelling is not a repair — the
locally-sofic collapse theorem of the halo audit shows every finite-dimensional
target class is already covered.  A Connes embedding of
`Cl(G/Gamma) crossed_product G` must therefore be non-chartable: no injective
partial homomorphisms on the lamps over a positive-density set of states.
