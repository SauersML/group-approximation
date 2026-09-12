---
rg: 2
id: agent-free-compressor-complement-gauge-proof
kind: route
title: Put the selected simple packet block beside cyclic gauges of unbounded order
target: agent-free-compressor-named-row-retains-complement-gauge
requires: []
---

Let `ell_n->infinity` and put

```text
R_n=S times k[C_(ell_n)],             P_n=(1_S,0).     (CGP1)
```

Choose one packet generator `b_i` and write its matrix in `S` as `B_i`.
For a generator `g_n` of `C_(ell_n)`, define coefficient units

```text
b_(i,n)=(B_i,1),               u_(i,n)=(B_i,g_n).     (CGP2)
```

All other named packet units may be placed as `(B_j,1)`.  Equations `(NCG2)`
are literal identities in `R_n`, because multiplication by `P_n` deletes the
second factor.  Take the left regular unitary representation of the finite
elementary group `E_N(R_n)`.

The root `x_13(P_n)` lies in the first direct factor and has order `p`, giving
`(NCG3)`.  The diagonal quotient

```text
D_(u_i)D_(b_i)^(-1)
```

lies in the second direct factor and has order `ell_n`.  Its left-regular
spectral measure is uniform on the `ell_n`-th roots of unity.  Hence, for
every projection `e_n` and every `delta>0`,

```text
tr(e_n)
 <=#{z^ell_n=1:|z-1|<=delta}/ell_n
   +delta^(-2)||(D_(u_i)D_(b_i)^(-1)-1)e_n||_2^2.     (CGP3)
```

First let `n->infinity`, then `delta->0`; this proves `(NCG4)`.  The argument
uses the full elementary group over `R_n`, so increasing the Steinberg rank
adds relations but does not remove the countermodel.

