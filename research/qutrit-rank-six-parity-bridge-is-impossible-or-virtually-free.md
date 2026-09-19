---
rg: 2
id: qutrit-rank-six-parity-bridge-is-impossible-or-virtually-free
kind: claim
title: The rank-six qutrit parity bridge is either Clifford-impossible or virtually free
artifacts:
  - research/qutrit-rank-six-parity-bridge-proof.md
distinct_from:
  thompson-27-cylinder-qutrit-cell-is-fd-invisible: that constructs the rank-six marginal and its three-phase coefficient cancellation; this tests the most economical finite Clifford spectral identification for that marginal.
  finite-projective-sector-groupoids-have-conjugate-absorbers: that gives a general absorber for finite sector transports; this uses the explicit qutrit stabilizer geometry to rule out the coherent Clifford conjugacy and then identifies the exact finite-amalgam fallback.
  qutrit-head-only-overlap-envelope-is-finite: that fences a Jacobson idempotent-root attachment; this fences a rank-matched involution attachment.
---

In the nine-dimensional spin block of the qutrit packet, choose the standard
two-qutrit model.  Then the six-atom marginal is

```text
R=(1-|2><2|) tensor I_3.                                 (QPB1)
```

Let `Pi` be one-qutrit parity, `Pi|x>=|-x>`, and let

```text
E_+=(1+Pi)/2.
```

Both `R` and `E_+ tensor I_3` have rank six, with rank-three
complements.  Nevertheless no one-qutrit Clifford `g` satisfies

```text
(g tensor I_3) R (g^* tensor I_3)=E_+ tensor I_3.        (QPB2)
```

Thus the rank match cannot identify the marginal with a coherent Clifford
parity cut while retaining the qutrit packet occurrence.  In particular no
normalizer conjugacy converts the exact three-phase marginal into that
spectral cut.

There is also a sharp firewall for weakening coherence.  Let `A` be any
finite Clifford actor with a nine-dimensional representation in which a
distinguished involution `u` has multiplicities `6/3), and amalgamate it
with `F` only over a finite central subgroup `C` acting compatibly by
scalars.  Then

```text
Gamma=F *_C A                                             (QPB3)
```

is virtually free, residually finite, and hyperlinear.  After unitary
conjugation of the `A`-representation inside the common scalar sector, one
can arrange

```text
(1+sigma(u))/2=R                                         (QPB4)
```

exactly.  Hence a rank-only or central-type parity identification has an
exact finite-dimensional countermodel inside a hyperlinear support group.

The dichotomy is exact for this proposed bridge: full Heisenberg/Clifford
coherence makes the spectral identification impossible, while weakening the
attachment enough to align the two rank-six cuts leaves a finite amalgam.
A load-bearing overlap must use a noncentral raw coefficient incidence, not
only parity multiplicities or a central finite-sector gluing.
