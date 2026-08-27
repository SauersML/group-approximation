---
rg: 2
id: central-hnn-inversion-symmetrized-trace-is-mf-proof
kind: route
title: Cancel the stable letter with its inverse in two matrix corners and apply homotopy lifting
target: central-hnn-inversion-symmetrized-trace-is-mf
requires: []
artifacts:
  - research/artifacts/shulman-central-hnn-inversion-lifting-audit-2026-08-22.md
---

Write `Q_2=prod M_(d_n)/direct-sum_(2,omega) M_(d_n)` and amplify `f`
entrywise to matrices over `Q_2`.  There are two homomorphisms

```text
Phi,Psi:D -> M_2(Q_2),

Phi(a)=diag(f(a),f(a)),       Phi(t)=diag(f(t),f(t)*),
Psi(a)=diag(f(a),f(a)),       Psi(t)=1.
```

They are homotopic.  For a unitary `u`, put

```text
R_s = [[cos(pi s/2), -sin(pi s/2)],
       [sin(pi s/2),  cos(pi s/2)]],

H_s(u)=diag(u,1) R_s diag(1,u*) R_s*.
```

Then `H_0(u)=diag(u,u*)` and `H_1(u)=1`.  If `u` commutes with `f(C)`,
every `H_s(u)` commutes with `diag(f(C),f(C))`.  Keeping the base image
fixed and sending `t` to `H_s(f(t))` therefore gives a homotopy of
homomorphisms from `Phi` to `Psi`.

Let `r:D->A` be the retraction fixing `A` and sending `t` to `1`.  Since
`f|A` lifts to a discrete asymptotic homomorphism, `Psi`, which is the
twofold amplification of `(f|A) o r`, does too.  Shulman's homotopy-lifting
Theorem 11 (arXiv:2508.00125v5) now makes `Phi` lift to a discrete
asymptotic homomorphism.  Proposition 23 of the same paper says that the
matrix-normalized trace of `Phi` is MF.  But

```text
tr_2 o Phi = (tau + tau o iota)/2,
```

which proves the claim.
