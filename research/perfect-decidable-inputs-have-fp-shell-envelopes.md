---
rg: 2
id: perfect-decidable-inputs-have-fp-shell-envelopes
kind: claim
title: Perfect decidable infinite finite presentations admit finitely presented shell envelopes
distinct_from:
  decidable-inputs-have-fp-shell-envelopes: that asks for every infinite finitely presented decidable input, while this only asks for perfect inputs. A perfect-envelope embedding suffices to use this restricted hypothesis for Boone--Higman; no implication back to a shell envelope of the original input is asserted.
artifacts:
  - research/artifacts/boone-higman-perfect-shell-route-2026-09-08.md
---

For every infinite perfect finitely presented group P with decidable
word problem, some enumeration nu:P->N makes E_nu finitely presented.
This is OPEN.

E_nu is already simple and contains P for every enumeration. A
successful enumeration must be computable, by the effective
extraction claim. The outstanding step is a finite presentation
of this faithful simple group, not a proof of simplicity or of
finite generation of its point stabilizers.

## Attempts

The explicit perfect-envelope construction reduces every input of
Boone--Higman to this input class without losing finite presentation
or decidable word problem. The normal-core positive control does
not discharge this claim: an infinite perfect group cannot be
virtually cyclic, and the corresponding shell prefix core is trivial
for every enumeration. No general relation-compression argument
for E_nu has been supplied.
