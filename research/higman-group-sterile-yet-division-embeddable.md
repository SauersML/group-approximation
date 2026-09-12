---
rg: 2
id: higman-group-sterile-yet-division-embeddable
kind: route
title: Higman's group - Malcev on one side, Fisher-Sanchez-Peralta 3.14 on the other
target: linear-sterility-does-not-obstruct-division-embedding
requires: []
artifacts:
  - research/artifacts/strong-atiyah-audit-2026-08-17.md
---

## Why sufficient

Let `H = <a,b,c,d | b^a=b^2, c^b=c^2, d^c=d^2, a^d=a^2>`.

**No nontrivial finite quotient.**  Higman's 1951 theorem; `H` was the first
known infinite group with this property.

**Torsion-free.**  Two independent reasons, both from the source read below:
`H` is realised as a square of groups with `BS(1,2)` vertex groups and `Z`
edge groups, and it is left-orderable by Rivas--Triestino, who show it acts
faithfully and continuously on `R`.

**Every finite-dimensional representation over every field is trivial.**  Let
`rho : H -> GL_n(F)`.  The image is a finitely generated linear group, hence
residually finite by Mal'cev.  If `rho(H) != 1`, residual finiteness gives a
nontrivial finite quotient of `rho(H)`, and composing with `rho` gives a
nontrivial finite quotient of `H` -- contradiction.  So `rho` is trivial, and
the all-fields linear residual of `H` is `H` itself.

**Yet `k[H]` embeds in a division ring for characteristic-zero `k`.**
Fisher--Sanchez-Peralta, arXiv:2303.08165, Proposition 3.14, closing their
Section 3: *"Here we show that `kH` has the (a priori) stronger property of
embedding into a division ring, at least when `k` is a field of
characteristic zero"* -- stronger, that is, than the zero-divisor conclusion
Rivas--Triestino's left-orderability already gives.

Together these give the claim: maximal sterility under exact
finite-dimensional representations coexists with division-ring embeddability.

## Scope discipline

This route establishes a **negative** statement about what sterility implies.
It must not be read as Strong Atiyah for `H`: the division ring of
Proposition 3.14 is not asserted to be the affiliated-operator division
closure, and the paper makes no such claim.

Trust surface: `requires: []`, importing Higman 1951 (no finite quotients),
Mal'cev (finitely generated linear implies residually finite), and
Fisher--Sanchez-Peralta Proposition 3.14.  The last was read at pinpoint level
from the arXiv source this session, including the surrounding sentences that
identify the group and its left-orderability; the first two are standard and
were taken at textbook level.
