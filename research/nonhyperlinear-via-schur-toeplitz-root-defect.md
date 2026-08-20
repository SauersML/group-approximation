---
rg: 2
id: nonhyperlinear-via-schur-toeplitz-root-defect
kind: route
title: Promote the Schur predicate density by identifying it with a Toeplitz root defect
target: non-hyperlinear-group
requires:
  - schur-idempotent-is-an-injective-toeplitz-defect
  - schur-toeplitz-envelope-has-proper-self-embedding
  - schur-toeplitz-root-mark-is-fd-invisible
  - hs-schur-toeplitz-root-defect-collapse
---

Take the explicit finitely presented ascending HNN group and nontrivial root
word `(H_f,w_f)` from the algebraic claims. The normalized-HS collapse theorem
forces every asymptotic representation to send `w_f` to the identity. If
`H_f` were hyperlinear, its canonical delta trace would admit microstates;
because `w_f!=1` has order `p`, those microstates keep it a fixed positive
distance from the identity, contradicting the collapse. Hence `H_f` is an
explicit nonhyperlinear group.

This route is the coefficient-root version of trace promotion: the scale-free
Schur orientation is not imposed by a direct group relator. It is made equal
to a one-sided Toeplitz defect which vanishes in every finite coefficient
quotient, and the only open content is making that finite-dimensional fact
robust in normalized Hilbert--Schmidt metric.
