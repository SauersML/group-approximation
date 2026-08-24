---
rg: 2
id: mf-camouflage-surgery-preserves-matricial-stability-proof
kind: route
title: Apply split corona stability to camouflage surgery
target: mf-camouflage-surgery-preserves-matricial-stability
requires:
  - mf-camouflage-surgery
  - split-corona-equivalences-preserve-matricial-stability
  - matricial-stability-identifies-radicals
---

The quotient `pi_Q` is split and, by `(C1)`, precomposition gives a bijection
on homomorphisms to every norm-corona unitary group.  Hence `(CMS2)` is
`(SCE3)`.

Assume `Q` is MF and stable.  Camouflage radical transplantation gives

```text
Rad_MF(C_d(Q))=ker(pi_Q)=normalClosure(d).             (CMP1)
```

By `(CMS2)`, `C_d(Q)` is stable, so
`matricial-stability-identifies-radicals` gives

```text
Rad_fd(C_d(Q))=Rad_MF(C_d(Q)).                         (CMP2)
```

Amalgam normal form keeps `d` nontrivial, proving non-MF and `(CMS3)`.
Free groups and `Z` are MF and point-norm stable by
`matricially-stable-groups-exist`; substitution gives the concrete family.
Finite presentability is the finite amalgam presentation already recorded
in `mf-camouflage-surgery`.
