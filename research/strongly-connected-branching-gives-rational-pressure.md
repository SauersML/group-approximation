---
rg: 2
id: strongly-connected-branching-gives-rational-pressure
kind: claim
title: One genuine branch in a finite strongly connected automaton gives an explicit rational pressure certificate
artifacts:
  - experiments/branching_pf_certificate.py
---

Let `A` be a nonnegative integer matrix with convention `A[j][i]` equal to the
number of directed branch edges from state `i` to state `j`.  Suppose the
underlying directed multigraph is strongly connected and some state has at
least two outgoing edges, counted with multiplicity.

Then there exist an integer vector `y>0` and a rational `kappa>0` such that

```text
A^T y >= (1+kappa) y.                               (SCB1)
```

More explicitly, put `B=A^T` and let `1` be the all-ones vector.  If `N` is
large enough that every state can reach a branching state in fewer than `N`
steps, then every coordinate of `B^N 1` is at least `2`.  Hence

```text
y = 1 + B1 + ... + B^(N-1)1
```

satisfies

```text
B y = y + B^N1 - 1 >= y + 1.
```

Taking `M=max_i y_i` and `kappa=1/M` proves `(SCB1)`.

Thus for integer branch automata, the supercriticality test needed by the
atlas route is purely finite-state: **strong recurrence plus one real branch**.
No spectral-radius calculation or algebraic Perron eigenvector is required.
Combined with `rational-supercritical-branch-certificate`, a low-energy return
path from the already-known doubled Pauli edge immediately yields a rational
trace-pressure inequality.