---
rg: 2
id: stw74-stationary-matrix-threshold-proof
kind: route
title: Minimize and freeze the projection-return level along uniform finite-root cutdowns
target: stw74-counterexamples-have-stationary-matrix-thresholds
requires:
  - stw74-counterexample-has-uniform-root-towers
  - stw74-all-stabilized-projections-are-properly-infinite
---

Use the uniform-root-tower theorem for `a` and write

```text
x_k=[(a-epsilon_k)_+],       x_k << x_(k+1),
n x_k=[1_A]=u                for every k.                    (1)
```

For each `k`, define

```text
mu_k=min{j>=1 : M_j(H_k) contains a nonzero projection}.
```

This set is nonempty.  Indeed, (1) says that the compact projection class
`u` is below the class of the positive element
`(a-epsilon_k)_+ tensor 1_n`.  A projection Cuntz below a positive element
is Murray--von Neumann equivalent to a projection in its hereditary
subalgebra, so `M_n(H_k)` contains a nonzero projection.  Therefore

```text
mu_k <= n.                                                   (2)
```

Since `D` is projectionless, `mu_k>=2`.  The inclusions
`H_k subset H_(k+1)` make `(mu_k)` nonincreasing.  A nonincreasing sequence
in the finite set `{2,...,n}` is eventually constant; discard its initial
segment and call the constant value `m`.  Minimality gives both lines of
`(T)`.

It remains to identify the projections which occur.  Let
`0!=q in M_m(H_k)`.  The stabilized-projection theorem makes `q` properly
infinite.  It is full in the simple algebra `A tensor K`, so compactness of
`u` gives `u<=N[q]` for some finite `N`.  Proper infiniteness gives
`N[q]=[q]`.  Conversely `[q]<=u` because the properly infinite unit is the
largest Cuntz class.  Hence

```text
[q]=u.
```

Equality of Cuntz classes of projections is stabilized Murray--von Neumann
equivalence, completing the proof.

