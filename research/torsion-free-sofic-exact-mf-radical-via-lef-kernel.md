---
rg: 2
id: torsion-free-sofic-exact-mf-radical-via-lef-kernel
kind: route
title: Take the mapping torus of a torsion-free LEF Kazhdan kernel with exact radical; soficity is free
target: torsion-free-sofic-exact-mf-radical-over-z
requires:
  - torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical
  - sofic-kernel-amenable-quotient-permanence
---

Take `(K, φ)` as in `torsion-free-lef-kazhdan-kernel-with-exact-mapping-torus-radical`, and set
`G = K ⋊_φ Z`. Each clause of (TFZ1) then holds.

- **Finitely presented.** This is (LK2).
- **Torsion-free.** An element `(k,n)` with `n ≠ 0` maps to `n ≠ 0` in `Z`, so it has infinite order.
  An element `(k,0)` lies in the torsion-free group `K`.
- **Sofic.** `K` is LEF, hence sofic: for a local embedding of a finite window into a finite group `F`,
  composing with the left regular action of `F` gives a sofic approximation on that window which is
  exact and has no fixed points. `Z` is amenable, so `G` is sofic by
  `sofic-kernel-amenable-quotient-permanence`.
- **Kazhdan kernel.** `K` is nontrivial and has property (T), by (LK1).
- **Exact radical.** `Rad_MF(G) = K × {0}` is (LK3).
- **Quotient.** `G/K ≅ Z`.

This is the unique branch of the flagship lying in the sofic permanence closure, by
`permanence-closure-radical-witnesses-have-lef-kernels`. The preferred strengthening of the
flagship ("`K` finitely presented") is impossible on this route, by (PW3) of that claim.
