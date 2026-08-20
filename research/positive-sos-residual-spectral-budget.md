---
rg: 2
id: positive-sos-residual-spectral-budget
kind: claim
title: A small positive SOS residual forces a quantitative low-spectrum budget
---

Let `(N,tau)` be a finite tracial von Neumann algebra with `tau(1)=1`.  Let
`A=A*>=0`, let `kappa>0`, let `B>=0`, and put

```text
R = A^2 - kappa A - B,
||R||_2 <= eta.
```

Then the spectral projection

```text
P_0 = 1_[0,kappa/2](A)
```

obeys

```text
tau(P_0 A) <= 2 eta/kappa,
tau(P_0 sqrt(A)) <= sqrt(2 eta/kappa).                 (SB1)
```

More generally, for `0<a<=b<kappa`, put

```text
P_[a,b] = 1_[a,b](A),
c(a,b)=min(a*(kappa-a), b*(kappa-b)) > 0.
```

Then

```text
tau(P_[a,b]) <= (eta/c(a,b))^2.                        (SB2)
```

Thus an approximate identity of the form
`A^2-kappa A = positive + small` does more than exclude a fixed middle
spectral interval: it gives a dimension-free first-moment budget for *all*
low eigenvalues at once.  This is the form relevant to recursive normalized-HS
block refinement, where many tiny low-energy directions may coexist.
