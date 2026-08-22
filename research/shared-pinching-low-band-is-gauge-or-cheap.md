---
rg: 2
id: shared-pinching-low-band-is-gauge-or-cheap
kind: claim
title: The equality-split low pinching band is gauge or removable at vanishing cost
distinct_from:
  row-square-equality-variance-transfers-averaged-pinching-gap: that transfers the exact local-face gap but leaves a spectral band of width O(sqrt(epsilon)) near the old commutant; this must dispose of that band.
  common-character-rotation-is-flat-for-involution-jacobian: that identifies exact simultaneous-conjugation motion inside the zero band; this must also handle genuinely positive eigenvalues created by equality splitting.
  central-adaptive-peeling-or-noncentral-stopping: that treats high anchor-odd spectral cuts; this treats the near-zero spectrum of the shared averaged pinching Hamiltonian.
---

OPEN.  In the setting of
`row-square-equality-variance-transfers-averaged-pinching-gap`, let

```text
 e_low=1_[0,kappa](H_R),       kappa=O(sqrt(epsilon)).     (SLB1)
```

Show that the part of the intrinsic correction carried by `e_low` is either
simultaneous-conjugation gauge, or can be reset/absorbed with normalized
Hilbert--Schmidt cost `o_epsilon(1)`, uniformly in code length, matrix
dimension, and occurrence multiplicity.

The positive spectrum above `kappa` already has a uniform finite-Green gap.
Thus only almost-invariant Hilbert--Schmidt directions born from splitting
the old local-face commutant remain.  A successful proof may identify them
with equality-cloud variance and charge them to `I-S_i^2`, or use a
spectral coarea cut whose boundary is paid by that same variance.

## Attempts

Ordinary Davis--Kahan perturbation locates the low spectral subspace but
does not make its projection an element of the physical matrix algebra:
`H_R` acts on `L_2(M)`.  It therefore cannot be cut away directly.  Nor can
one declare the whole low band gauge; equality perturbations can split an
old commutant direction to a small positive eigenvalue.  The needed argument
must exploit the special inner-adjoint form of `H_R`, converting low
Dirichlet energy back into a physical approximately reducing projection or
an explicit common conjugator.

