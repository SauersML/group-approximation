---
rg: 2
id: shared-pinching-low-band-is-gauge-or-cheap
kind: claim
title: The equality-split low pinching band has only vanishing Dirichlet energy
distinct_from:
  row-square-equality-variance-transfers-averaged-pinching-gap: that transfers the exact local-face gap but leaves a spectral band of width O(sqrt(epsilon)) near the old commutant; this must dispose of that band.
  common-character-rotation-is-flat-for-involution-jacobian: that identifies exact simultaneous-conjugation motion inside the zero band; this must also handle genuinely positive eigenvalues created by equality splitting.
  central-adaptive-peeling-or-noncentral-stopping: that treats high anchor-odd spectral cuts; this treats the near-zero spectrum of the shared averaged pinching Hamiltonian.
---

ESTABLISHED.  In the setting of
`row-square-equality-variance-transfers-averaged-pinching-gap`, let

```text
 e_low=1_[0,kappa](H_R),       kappa=O(sqrt(epsilon)).     (SLB1)
```

Although `e_low` is a spectral projection on `L_2(M)` rather than a physical
matrix projection, it need not be removed.  The spectral theorem gives

```text
 <e_low T,H_R e_low T> <=kappa||T||_2^2.                (SLB2)
```

For shared reflections `(R_i)`,

```text
 <R_i,H_RR_i>=(1/4)avg_j||[R_i,R_j]||_2^2.              (SLB3)
```

Thus the normalized complete-pair energy carried by the low band is at most
`4kappa`, uniformly in cardinality and dimension.

The positive spectrum above `kappa` has a uniform finite-Green gap.  On an
eigenvalue `lambda<=kappa`, the **forced** response `G_K H_R` has multiplier
`1-(1-lambda)^K<=K lambda`, so the correction generated from the Dirichlet
forcing there is also `O(Kkappa)` for fixed `K`.  This is not an operator
bound for `G_K` on arbitrary low-band inputs.  The actual forcing contains
the `H_R` factor, and may remain as a vanishing floor.

## Attempts

The low band is not literally gauge, and Davis--Kahan does not make its
projection physical.  Neither is needed: Hilbert--Schmidt forcing asks for
vanishing relator energy, already supplied by `(SLB2)--(SLB3)`.
