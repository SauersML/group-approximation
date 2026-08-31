---
rg: 2
id: head-retention-forces-distance-from-every-global-frame
kind: claim
title: A Jacobson head cannot hide in a globally rotated Toeplitz frame
distinct_from:
  head-retention-forces-macroscopic-carrier-motion: that measures distance from the displayed carrier; this quotients all common unitary frame changes
  presentation-defect-does-not-control-off-commutant-mass: that exhibits global conjugacy as an obstruction to commutant projection; this removes exactly that obstruction before locating the survivor
  pauli-swap-coherence-reduces-to-the-commutant-gate: that treats generator-dependent discrete swaps; this treats arbitrary continuous common rotations
---

For the Toeplitz carrier tuple `A` define its global-frame orbit distance

```text
eta_orb(U,A)
 = inf_(W unitary) max_(s in Sigma)||U_s-WA_sW^*||_2.  (HGF1)
```

There are constants `C_0,C_1<infinity`, depending only on the fixed
presentation, such that every unitary tuple `U` satisfies

```text
||w(U)-I||_2 <= C_0 delta(U)+C_1 eta_orb(U,A).          (HGF2)
```

Thus a common macroscopic `SU(2)` rotation of two carrier sheets is a pure
absorber: it changes neither the endpoint obstruction nor the head
modulus. Any head-retaining mixed-isotype sequence must stay a fixed
distance from every globally conjugated Toeplitz carrier.

After the monomial and infinitesimal firewalls, the smallest surviving
two-sheet mechanism is therefore a macroscopic, nonmonomial,
generator-dependent rotation with nonvanishing frame curvature. The
claim does not bound that curvature from the defining relators.

DERIVATION
conjugacy-orbit-version-of-the-endpoint-bound-proof
