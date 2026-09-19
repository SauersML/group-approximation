---
rg: 2
id: hereditarily-mf-principal-closure-proof
kind: route
title: Evaluate transplanted closure on quotient-MF visible groups
target: hereditarily-mf-quotients-have-principal-camouflage-closure
requires:
  - mf-semantic-closure-transplantation
  - amenable-implies-operator-mf
---

The transplantation formula gives

```text
cl_MF^(C_d(Q))(N)=pi^(-1)(cl_MF^Q(pi(N))).
```

Since `Q/pi(N)` is MF, its MF radical is trivial and
`cl_MF^Q(pi(N))=pi(N)`.  Hence

```text
cl_MF(N)=pi^(-1)(pi(N))=N ker(pi)=N K,
```

which is `(HMQ1)`.  A quotient is MF exactly when its defining normal
subgroup is MF-closed, so `(HMQ2)` follows from `K=normalClosure(d)`.

The interval correspondence is the ordinary correspondence theorem for the
surjection `pi`.  Finally, quotients of amenable groups are amenable, and
`amenable-implies-operator-mf` supplies their MF property.

