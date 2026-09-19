---
rg: 2
id: exterior-return-right-module-dimension-proof
kind: route
title: Compare the return kernel with the conditional-expectation mass
target: exterior-return-generates-almost-full-right-edge-module
requires: []
---

Since `yr=0` and `y=x-z`,

```text
xr=zr.                                                  (ARP1)
```

The matrix `x` is unitary, so

```text
tr(r)=||xr||_2^2=||zr||_2^2<=||z||_2^2<=(q+eta)^2,     (ARP2)
```

which proves `(ARM2)--(ARM3)`.

For `b in B`, bimodularity gives

```text
E_B(yb)=E_B(y)b=0,                                     (ARP3)
```

so `yB` is orthogonal to `B`.  Its algebraic kernel under the right-module
map `B->L2(M_d)`, `b mapsto yb`, is a right ideal of the finite-dimensional
C-star algebra `B`, hence has the form `eB` for a projection `e in B`.
Because `ye=0`, one has `e<=r`, and `(ARP2)` gives

```text
tr(e)<=tr(r)<=(q+eta)^2.                               (ARP4)
```

The quotient `B/eB` is isomorphic as a right `B`-module to `(1-e)B`, whose
Murray--von Neumann dimension for the restricted normalized trace is
`tr(1-e)`.  This proves `(ARM4)`.
