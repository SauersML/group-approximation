---
rg: 2
id: compression-defect-mark-stability-proof
kind: route
title: Compose the exact finite-dimensional kill with one-element point-norm repair
target: compression-defect-dies-in-mf-under-mark-stability
requires:
  - compression-defect-dies-in-finite-dimensions
  - fd-mark-stability-forces-mf-invisibility
---

By `compression-defect-dies-in-finite-dimensions`, for every field `k`, every
finite-dimensional `k`-space `V` and every `pi : H -> GL_k(V)` one has
`D(H,L) <= ker pi`.  Specializing to `k=C` and to unitary `pi` -- every
finite-dimensional unitary representation is such a `pi` -- gives

```text
D(H,L) <= Rad_fd(H).
```

Let `w in D(H,L)` be a mark at which `H` is fd-stable.  Then
`w in Rad_fd(H)`, so `fd-mark-stability-forces-mf-invisibility` applies
verbatim and gives `w in Rad_MF(H)`.  If `w != 1`, the identity
homomorphism-detecting corona representation cannot exist, i.e. no faithful
`Theta : H -> U(Q)` exists and `H` is not MF.  This is clause 1.

Clause 2 is clause 1 applied at every element of `D(H,L)`, and clause 3
follows because `Rad_MF(H)` is an intersection of kernels of homomorphisms
out of `H` and hence normal: it contains the normal closure of any subset it
contains, and that closure is `H` by hypothesis.

The matricial-stability specialization is immediate, since Dadarlat's
point-norm hypothesis is fd-stability at every element simultaneously; it is
the hypothesis of `matricial-stability-identifies-radicals`, and the
conclusion `Rad_MF=Rad_fd` of that node gives clauses 1-3 in one step as
well.  Both readings compose the same two halves; the mark-local one is
recorded because it is what the endpoint actually consumes.
