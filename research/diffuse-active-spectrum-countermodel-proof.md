---
rg: 2
id: diffuse-active-spectrum-countermodel-proof
kind: route
title: Use the regular trace of the active-module semidirect product
target: diffuse-active-spectrum-blocks-qualitative-collapse
requires: []
---

Let `lambda` be the left regular representation of `K=M semidirect H` and
let `tau` be its canonical trace.  Since `M` is abelian, Fourier transform
identifies its von Neumann algebra with

```text
L(M)=L^infinity(M_hat, mu_Haar).
```

Conjugation by `lambda(h)` implements the dual action of `h in H` exactly.
Thus all module multiplication laws and all actor covariance laws have zero
error.

The additive group `M` is infinite: the faithful active relative-Leavitt
corner contains active coefficient spaces of arbitrarily large finite
dimension.  Hence its compact dual has atomless Haar measure.  In
particular the singleton consisting of the trivial character has measure
zero.

For every nonidentity group element `g`, the regular trace has
`tau(lambda(g))=0`.  Apply this to `m_0` and compute

```text
||lambda(m_0)-1||_2^2
 = 2-2 Re tau(lambda(m_0))
 = 2.
```

On a finite atomic PVM, the character-orbit proof applies the discrete
Schreier Poincare inequality separately to the weighted atoms.  In the Haar
model there are no character atoms.  Equivalently, in the Koopman
representation on `L^2(M_hat,mu_Haar)`, the constant function is invariant
although almost every character belongs to an infinite discrete orbit.
Thus the discrete orbit gap cannot be integrated against Haar in the manner
needed for the finite-coordinate estimate.
