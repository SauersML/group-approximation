---
rg: 2
id: agent-free-compressor-one-row-implies-kernel-sector
kind: route
title: Square the reflected Hilbert corner to obtain the terminal adjoint kernel sector
target: agent-free-compressor-payload-kernel-fixed-sector
requires:
  - agent-free-compressor-one-row-kernel-reflection
---

Given `e` from `(ORK2)--(ORK4)`, let `E` be the orthogonal projection of
normalized Hilbert--Schmidt space onto

```text
e M_d e.
```

Then

```text
tr_ad(E)=tr(e)^2>=c^2 q_bad^2-o(1),                   (ORI1)
```

which is `(PKF1)`.  Left and right multiplication are contractions in
normalized Hilbert--Schmidt norm.  Hence `(ORK3)` implies

```text
||[E,Ad U(x_i)]||_(2,ad)=o(1),                        (ORI2)
```

and `(ORK4)`, together with its adjoint, implies

```text
||(Ad U(r_j)-1)E||_(2,ad)=o(1).                       (ORI3)
```

All lists are fixed, so the constants remain dimension-independent.
Equations `(ORI1)--(ORI3)` are exactly `(PKF1)--(PKF3)`.  The terminal route
`agent-free-compressor-kernel-carrier-is-terminal` then contradicts canonical
microstates because `ker(theta)` is infinite.
