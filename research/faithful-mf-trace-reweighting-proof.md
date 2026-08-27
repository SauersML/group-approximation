---
rg: 2
id: faithful-mf-trace-reweighting-proof
kind: route
title: Dilute one faithful norm block inside arbitrarily many prescribed trace blocks
target: faithful-mf-models-realize-all-mf-traces
requires: []
---

Use the sequential definitions of an MF algebra and an MF trace.  Separability
permits one common diagonal sequence on a countable dense star-subalgebra;
the uniform pointwise norm bounds then extend every limit to all of `B`.

Let `phi_n:B->M_(k_n)` witness that `tau` is an MF trace and let
`psi_n:B->M_(ell_n)` be asymptotically isometric MF coordinates for `B`.
After discarding finitely many zero-dimensional coordinates, choose
`m_n>=1` with

```text
ell_n/(m_n k_n+ell_n)<=1/n.
```

Define `Theta_n` by `(FMT1)`.  Every linearity, star and multiplicativity
defect of `Theta_n` has operator norm equal to the maximum of the
corresponding defects of `phi_n` and `psi_n`, hence tends to zero.  For every
`a in B`,

```text
||Theta_n(a)||=max(||phi_n(a)||,||psi_n(a)||)->||a||,
```

where the lower limit comes from `psi_n` and the standard asymptotic
contractivity of MF coordinates supplies the upper limit.

Writing `D_n=m_n k_n+ell_n`,

```text
tr_(D_n)(Theta_n(a))
 = (m_n k_n/D_n) tr_(k_n)(phi_n(a))
   +(ell_n/D_n) tr_(ell_n)(psi_n(a)).                    (FMT2)
```

The second coefficient tends to zero, the second trace is bounded for fixed
`a`, and the first trace tends to `tau(a)`.  Equation `(FMT2)` proves the
desired trace convergence.  The reverse implication is precisely the MF
trace definition, without using asymptotic isometry.
