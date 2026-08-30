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
  - research/artifacts/composite-scaling-kazhdan-radical-reconstruction-2026-08-30.md
---

**ESTABLISHED.**  For all `m,n>=2`, every isomorphism

```text
Phi:E_m -> E_n
```

carries the normal closure `N_m=<<c_m>>` of the lamp generator onto
`N_n=<<c_n>>`.

The kernel now has a presentation-free characterization.  If

```text
K_T(G)=<FinRad(H): H<=G maximal with property (T)>,
```

then the exact composite-block analysis proves

```text
K_T(E_r)=N_r
```

for every scale `r>=2`.  Property `(T)`, maximality, and finite radicals
are preserved by abstract isomorphisms, so the displayed formula is
functorial across different family members.

DERIVATION
[[scaling-lamp-kernel-via-maximal-kazhdan-radicals]]
