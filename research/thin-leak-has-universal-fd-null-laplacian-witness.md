---
rg: 2
id: thin-leak-has-universal-fd-null-laplacian-witness
kind: claim
title: Every thin commutant leak is detected by one universal finite-dimensional-null Laplacian sequence
distinct_from:
  thin-profinite-selected-gap-lemma: that assumes weak containment of the entire selected cyclic module and transfers the C-Laplacian gap; this identifies a single explicit sequence of group-ring tests whose survival is equivalent to the marked leak.
  thin-selected-module-is-profinite-continuous: that asks for continuity on the whole finite-dimensional completion; this needs upper semicontinuity only for the displayed universal cutoff sequence.
---

Fix

```text
A=SL_3(Z),  C=<a,b>,  r in A\C
```

as in `explicit-sl3-thin-codense-tau-pair`.  Take a symmetric generating
list `S_C` for `C` and put

```text
Delta_C=sum_(c in S_C)(1-c)^*(1-c),
L=4|S_C|,
x_N=(1-Delta_C/L)^N,
y_N=(r-1)x_N in C[A].                                 (ULW1)
```

There are constants `kappa>0` and `0<q<1`, depending only on the displayed
pair, such that

```text
||y_N||_FD <= 2q^N,                                    (ULW2)
```

where `||.||_FD` is the supremum over all finite-dimensional unitary
representations of `A`.

On the other hand, let `pi:A->U(M)` be any representation in a finite
tracial von Neumann algebra, let `alpha=Ad pi` on `L^2(M)`, and let
`v in U(M)` centralize `pi(C)`.  Then for every `N`,

```text
alpha(x_N)v=v,
alpha(y_N)v=alpha(r)v-v,                               (ULW3)
```

and hence

```text
||alpha(y_N)v||_2=||[v,pi(r)]-1||_2.                   (ULW4)
```

Thus every marked thin commutant leak is witnessed by the **same** sequence
`(y_N)`: its finite-dimensional norm decays exponentially, while its value
on the selected unitary stays constant.  Full weak containment of the
selected module is more than the terminal proof needs.
