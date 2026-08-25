---
rg: 2
id: property-t-free-manuscript-results
kind: claim
title: Reprove the non-MF manuscript endpoints without Property T
root: true
goal: true
artifacts:
  - non_mf_groups_exist.tex
---

**OPEN.**  Produce a replacement proof of the results advertised by
`non_mf_groups_exist.tex` in which Property `(T)` is absent from the proof,
not merely hidden behind a premise-free theorem.

The replacement must include the mathematical endpoints that remain after
removing the Kazhdan-specific intermediate language:

1. an explicit countable non-MF group, with a nontrivial element killed by
   every homomorphism to every norm matrix corona;
2. the full-MF-radical version for the binary-Leavitt group;
3. the basic MF-radical and MF-kernel-closure calculus;
4. functoriality, normal-generation saturation, full-kernel pullback, and
   universal factorization;
5. the explicit simplicity, defect, and prescribed-visible-quotient
   consequences used by the manuscript.

The final kernel-checked surface is

```text
GroupApproximation/Manuscript/OneSidedMFRadical/Unconditional.lean
```

and must have no declaration input standing for an unformalized literature
result.  Its proof dependency cone must not use a Property-`(T)` or Kazhdan
theorem.  In particular, a closed declaration obtained by instantiating
`HasKazhdanPropertyT` does **not** satisfy this claim.

The Kazhdan projection/order/transport statements in the current manuscript
are proof machinery, not endpoints to rename.  They must be removed from the
replacement argument and replaced by the finite-coordinate Property-`(T)`-free
mechanism that proves MF invisibility.

## Attempts

The downstream radical calculus is already algebraic and independent of
Property `(T)`.  The load-bearing missing input is the concrete
binary-Leavitt MF collapse recorded at
`property-t-free-leavitt-full-mf-radical`.  Writing a theorem package whose
only new premise is an authenticated return would be conditional and would
not settle this goal; the literal return compiler must first be proved.
