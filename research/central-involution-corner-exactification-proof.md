---
rg: 2
id: central-involution-corner-exactification-proof
kind: route
title: Spectrally round the sign and polar-correct every diagonal generator block
target: central-involution-corner-exactification
requires: []
---

Write `U_n=phi_n(J)`.  Spectrally round the unitary `U_n` to the nearest
self-adjoint involution `Z_n`.  Pointwise on the circle, distance to
`{+1,-1}` is at most `|z^2-1|`, hence

```text
||Z_n-U_n||_2 <= ||U_n^2-I||_2=o(1).                  (CIE1)
```

Put `e=(1-Z_n)/2` and `f=1-e`.  For a generator value `V=phi_n(s)`, its
block diagonal part

```text
X=eVe+fVf
```

satisfies

```text
||V-X||_2=||[e,V]||_2=(1/2)||[Z_n,V]||_2=o(1).        (CIE2)
```

The last estimate uses centrality of `J`, `(CIE1)`, and the corresponding
microstate multiplication defects.  Since `X` is a block-diagonal
contraction and

```text
||X*X-I||_2 <= 2||X-V||_2,
```

polar decomposition in each square diagonal block, with an arbitrary
unitary completion on its kernel, gives a block-diagonal unitary `W` with

```text
||W-X||_2 <= ||I-X*X||_2 <= 2||X-V||_2.               (CIE3)
```

Set `psi_n(s)=W`, and set `psi_n(s^-1)=W*` for inverse pairs.  If a named
generator is its own inverse, start with its self-adjoint unitary value and
use the blockwise sign of the self-adjoint compression; this gives a
block-diagonal involution with the same `o(1)` bound.  Thus inverse
normalization and exact commutation with `Z_n` hold simultaneously.

Every fixed word evaluation changes by at most its length times the largest
generator perturbation.  Therefore fixed multiplication defects and traces
change by `o(1)`.  On the negative block, normalized Hilbert--Schmidt norms
scale by `tau(e)^(-1/2)`, so restriction remains a microstate whenever
`liminf tau(e)>0`.

For canonical microstates, spectral rounding preserves the trace of `J` up
to `o(1)`, so `tau(e)=(1-tau(Z_n))/2 ->1/2`.  Exact commutation gives

```text
tau_e(e psi_n(g)e)
 =tau(e psi_n(g))/tau(e)
 =[tau(psi_n(g))-tau(Z_n psi_n(g))]/[2tau(e)],
```

which is the claimed corner formula.  The second numerator term stays
`o(1)`-close to the original fixed word trace of `Jg`.

