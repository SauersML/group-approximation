---
rg: 2
id: finite-saturated-table-cover-proof
kind: route
title: Add finite normal-generation certificates and descend through the epimorphism
target: finite-saturated-table-cover-removes-literal-group-presentation
requires: []
---

Because `z` normally generates `Delta`, for every generator `g_i` choose one
finite identity in `Delta`

```text
g_i=product_(j=1..m_i) a_(ij) z^(epsilon_(ij)) a_(ij)^(-1),
epsilon_(ij) in {+1,-1}.                              (FSP1)
```

All `a_(ij)` are finite words in `g_1,...,g_k`.  Define `Gamma` on those
`k` generators by the finite relator list consisting of `B` and the `k`
identities `(FSP1)`.  Evaluation in `Delta` respects every relator and is
surjective because the `g_i` generate, proving `(FSC1)`.

The relations `(FSP1)` put every generator of `Gamma` in the normal closure
of `z`, so `z` normally generates `Gamma`.  Its lift is nontrivial because
its image under `pi` is the assumed nontrivial element of `Delta`.

Finally, let `rho` be a homomorphism from `Delta` to a norm matrix corona.
By hypothesis `rho composed_with pi` kills `z`; normal generation makes
`rho composed_with pi` trivial.  Surjectivity of `pi` then makes `rho`
trivial.  This proves the descent assertion.
