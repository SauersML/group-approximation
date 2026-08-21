---
rg: 2
id: cascade-closes-from-koopman-regularity
kind: route
title: Koopman spectral regularity of the Weyl defect closes the absorption cascade
target: solenoid-absorption-cascade-converges
requires:
  - weyl-defect-koopman-spectral-regularity
  - bs14-exact-representation-variety-is-hs-locally-rigid
---

The cascade node assembles the machine: the correction equation is the
`x4` cohomological equation `c - c circ T = e'`, solved by the Ruelle
transfer operator (spectral gap on bounded-variation functions,
Ruelle--Perron--Frobenius), with the periodic-orbit (root-of-unity)
obstructions killed to `O(delta)` uniformly by dihedral Gowers--Hatami
on each `x4`-cycle and the order-`3` fixed obstruction killed by the
atomless regular trace.  The one analytic input that remains is the
transverse spectral regularity of `e'`, supplied by
`weyl-defect-koopman-spectral-regularity` `(KSR)`.  Given `(KSR)`, the
Lasota--Yorke bound produces the coboundary `c` with
`|| c ||_2 <= C delta`, which is the cascade's conclusion.
