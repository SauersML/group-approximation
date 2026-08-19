---
rg: 2
id: strongly-connected-branching-gives-rational-pressure-proof
kind: route
title: Path counts propagate one branch into every state and give an integer subeigenvector
target: strongly-connected-branching-gives-rational-pressure
requires: []
---

Write `B=A^T`.  For every state `i`, the coordinate

```text
(B^n 1)_i
```

is the number of length-`n` directed paths starting at `i`, counted with edge
multiplicity.  Strong connectivity implies every state has at least one
outgoing edge, so these path counts are nondecreasing in the weak sense needed
below: once there are two distinct paths at some length, extending each by any
one outgoing edge leaves at least two distinct paths at every larger length.

Choose a branching state `v`, with at least two outgoing edges.  For every
state `i`, strong connectivity gives a directed path from `i` to `v`; let its
length be `d_i`.  At length `d_i+1`, follow that path and then choose either of
two outgoing edges at `v`.  Thus

```text
(B^(d_i+1) 1)_i >= 2.
```

Because every endpoint has an outgoing edge, the same lower bound remains
true at all larger lengths.  Taking

```text
N >= max_i (d_i+1)
```

gives the coordinatewise integer inequality

```text
B^N 1 >= 2 * 1.                                      (1)
```

Now set

```text
y = sum_(t=0)^(N-1) B^t 1.
```

This is a strictly positive integer vector.  Telescoping gives

```text
B y - y = B^N 1 - 1 >= 1.                            (2)
```

Let `M=max_i y_i`.  Since `1 >= y/M` coordinatewise, `(2)` implies

```text
B y >= y + 1 >= (1+1/M)y.
```

Hence `(SCB1)` holds with the explicit rational choice `kappa=1/M>0`.
No limiting theorem, spectral computation, or irrational eigenvalue enters
the certificate.