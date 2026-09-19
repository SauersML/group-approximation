---
rg: 2
id: profinite-clifford-filtration
kind: route
title: Build the Clifford crossed product from an exact G-invariant finite-dimensional filtration
target: kun-thom-clifford-crossed-product-ce
requires: []
artifacts:
  - notes/NOTEPAD.md
---

Exhaust `Cl(G/Gamma)` by finite-dimensional `G`-invariant Clifford
subalgebras and apply the Capraro--Paunescu theorem that a profinite action of
a hyperlinear group on a finite von Neumann algebra has Connes-embeddable
crossed product.

Dead: `profinite-action-fixed-algebra-invariant` shows any such filtration
forces `A^Gamma` to be `G`-invariant, which destroys the root Majorana
witness — `c_(Gamma)` lies in `A^Gamma` while `u_h c_(Gamma) u_h^*` does not
commute with `pi(Gamma)`.  Equivalently, there is no `G`-invariant
exhaustion of `G/Gamma` by finite sets, and forcing one identifies the
invisible cosets.  The obstruction needs neither property `(T)` nor
soficity.
