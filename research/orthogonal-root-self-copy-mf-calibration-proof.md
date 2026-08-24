---
rg: 2
id: orthogonal-root-self-copy-mf-calibration-proof
kind: route
title: Use finite support for MF and Steinberg commutators for root saturation
target: orthogonal-root-self-copy-is-mf-compatible
requires:
  - binary-leavitt-heisenberg-is-orthogonal-central-self-copy
---

Every finite subset of `G` is contained in one finite group `E_n(F_q)`.
The inclusion into that finite group followed by the regular representation
is an exact finite-dimensional unitary model separating the chosen subset,
so `G` is MF.

The elementary matrices satisfy

```text
x_ij(a)x_ij(b)=x_ij(a+b),
[x_ij(a),x_jk(b)]=x_ik(ab),
```

with the standard off-root commutation relations.  Disjoint infinite
coordinate blocks commute and each supports another copy of the finitary
elementary group.

Let `a!=0` and let `N` be the normal closure of `x_ij(a)`.  For a third
index `k`, commutation with `x_jk(b)` gives `x_ik(ab)`.  Since multiplication
by `a` permutes `F_q`, every coefficient occurs.  Elementary root
permutations and further Steinberg commutators spread these elements to all
root positions, which generate `G`.  Hence `N=G`.
