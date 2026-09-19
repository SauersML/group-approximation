---
rg: 2
id: positive-sos-residual-spectral-budget
kind: claim
title: A small positive SOS residual forces a quantitative low-spectrum budget
---

Let `(N,tau)` be finite tracial with `tau(1)=1`. Let `A=A*>=0`, `kappa>0`,
`B>=0`, and

```text
R=A^2-kappa A-B,                 ||R||_2<=eta.
```

For `P_0=1_[0,kappa/2](A)`,

```text
tau(P_0 A)<=2eta/kappa,
tau(P_0 sqrt(A))<=sqrt(2eta/kappa).                    (SB1)
```

For `0<a<=b<kappa`, if `P_[a,b]=1_[a,b](A)` and
`c(a,b)=min(a(kappa-a),b(kappa-b))`, then

```text
tau(P_[a,b])<=(eta/c(a,b))^2.                          (SB2)
```

Thus an approximate identity `A^2-kappa A=positive+small` gives a
dimension-free first-moment budget for all low eigenvalues at once.
