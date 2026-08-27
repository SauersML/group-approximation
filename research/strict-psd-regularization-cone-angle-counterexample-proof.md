---
rg: 2
id: strict-psd-regularization-cone-angle-counterexample-proof
kind: route
title: Hide one negative affine eigenvalue on one normalized-HS coordinate
target: strict-psd-regularization-has-no-uniform-hs-affine-error-bound
requires: []
artifacts:
  - research/artifacts/deligne-maslov-character-rigidity-and-psd-cone-fence-2026-08-21.md
---

In `M_d`, with normalized Hilbert--Schmidt norm, put

```text
A_d = diag(-1,1,...,1),
L_d = {I+s A_d : s in R},
H_d = diag(1,3,...,3).
```

Then `H_d >= I`, while

```text
X_d=I+2A_d=diag(-1,3,...,3) in L_d
```

and therefore

```text
dist_2(H_d,L_d) <= ||H_d-X_d||_2 = 2/sqrt(d).
```

On the other hand `I+sA_d` is positive exactly when `-1 <= s <= 1`.
For such `s`, direct minimization gives

```text
||H_d-(I+sA_d)||_2^2
 = ((s+0)^2 + (d-1)(2-s)^2)/d,
```

whose constrained minimizer is `s=1`; its value is one.  This proves
`(CER2)`.

Finally fix any `0<t<1`.  Since `H_d>=I`,

```text
G_d=(H_d-tI)/(1-t) >= 0,
H_d=(1-t)G_d+tI.
```

Thus the same counterexample is already the output of strict regularization
by a label-compatible Slater point.  The obstruction is the unbounded angle,
in normalized Hilbert--Schmidt geometry, between the PSD cone and the affine
line `L_d`.
