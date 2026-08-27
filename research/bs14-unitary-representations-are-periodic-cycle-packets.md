---
rg: 2
id: bs14-unitary-representations-are-periodic-cycle-packets
kind: claim
title: Every finite-dimensional unitary BS(1,4) representation is a sum of periodic solenoid cycle packets
distinct_from:
  iwahori-square-root-presentation-is-bs14-plus-one-involution: that identifies the metabelian core inside the arithmetic presentation; this classifies every exact finite-dimensional unitary representation of that core.
  parabolic-spectrum-is-doubling-invariant: that is an approximate spectral transport statement; this gives the exact block normal form, including the arbitrary multiplicity monodromy.
---

Let `R,S in U(d)` satisfy

```text
R S R^(-1)=S^4.                                      (BP1)
```

Then the finite spectral measure of `S` is invariant under `z |-> z^4`.
Every atom has positive integer weight, so the fourth-power map is a
permutation of the finite support: no nonperiodic tail can feed a cycle in a
finite invariant weighted set.  Consequently every eigenvalue of `S` is a
root of unity of odd order, and the support is a disjoint union of periodic
fourth-power orbits.

For one orbit

```text
O={lambda,lambda^4,...,lambda^(4^(m-1))},             (BP2)
```

all spectral subspaces have one common dimension `k`.  After choosing
bases, its invariant summand has the form

```text
H_O = direct_sum_(j in Z/m) C^k,
S|_(H_O) = diag(lambda^(4^j) I_k),                    (BP3)
R(v_0,...,v_(m-1))=(v_1,...,v_(m-1),V v_0),           (BP4)
```

for an arbitrary unitary monodromy `V in U(k)` (up to the harmless reversal
of the orbit convention).  Conversely every packet `(BP3)--(BP4)` satisfies
`(BP1)`, and orthogonal sums of such packets give all finite-dimensional
unitary representations of `BS(1,4)`.

There is a useful further reduction.  Diagonalize `V` and apply that one
change of basis simultaneously on all `m` orbit spaces in `(BP3)`.  The
packet then splits orthogonally into `k` multiplicity-one packets, one for
each eigenvalue `v in T` of `V`; on such a packet `R^m=v`.  Thus the
monodromy data are continuous but **scalar**.  They are not an irreducible
`U(k)` obstruction.  Any relative repair of the Iwahori involution must
control how it couples scalar packets `(O,v)` with inverse `R`-spectral data,
rather than solve a genuinely matrix-valued return problem.  It still cannot
match only the spectrum of `S`: the phase `v` is an independent continuous
coordinate.
