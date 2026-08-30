---
rg: 2
id: scaling-lamp-kernel-isomorphism-invariant
kind: claim
title: The scaling-family lamp kernel is intrinsic under isomorphism
distinct_from:
  literal-telescope-split-normal-form: the split normal form selects the lamp kernel as the kernel of a displayed retraction for m=2; it does not characterize that kernel from the abstract group.
  literal-lamp-kernel-clifford-block-amalgam: that claim computes the internal structure of the doubling lamp kernel; it does not prove that an isomorphism of full groups must preserve the selected kernel.
  scaling-skeleton-quotients-pairwise-nonisomorphic: that claim separates the quotients after the lamp kernel has been selected; this claim is the missing descent from an isomorphism of full groups to those quotients.
artifacts:
  - research/artifacts/scaling-lamp-kernel-characteristicity-frontier-2026-08-30.md
---

**OPEN.**  For all `m,n>=2`, every isomorphism

```text
Phi:E_m -> E_n
```

carries the normal closure `N_m=<<c_m>>` of the lamp generator onto
`N_n=<<c_n>>`.

The cross-family formulation is deliberate.  Proving merely that `N_m` is
fixed by `Aut(E_m)` does not by itself identify it with `N_n` under an
isomorphism between two different family members.  A proof must give an
intrinsic group-theoretic characterization of `N_m`, or directly prove the
displayed functorial statement.

## Attempts

Ordinary abelianization is scale-independent and cannot select `N_m`.
Killing the base leaves the common quotient `Z*C_2`, so unmarked finite
quotients can also be scale-blind.  The existing block-amalgam normal form
computes the doubling kernel internally but does not classify automorphisms
of the full group.  The surviving approach is an intrinsic radical or normal
form characterization of the lamp kernel, uniform in `m`.
