---
rg: 2
id: scaling-family-abelianization-is-constant
kind: claim
title: Every literal non-MF scaling group has abelianization Z plus C2
distinct_from:
  scaling-family-pairwise-nonisomorphic: That asks whether the groups E_m are pairwise non-isomorphic; this proves that abelianization cannot distinguish any two of them.
  continuum-nonisomorphic-fg-non-mf: That separates external products E times Z^k by abelianization rank; the scaling parameter m disappears completely from the abelianization of E_m.
artifacts:
  - non_mf_group_notes.tex
  - research/artifacts/scaling-family-invariants-audit-2026-08-30.md
---

For every integer `m >= 2`, the literal eight-generator scaling group `E_m`
of [[scaling-family-non-mf]] has

```text
E_m^ab ~= Z direct_sum C_2,
```

where the infinite cyclic generator is the stable letter `t` and the
order-two generator is the image of `c`.  In particular, neither the
torsion-free rank nor the full isomorphism type of the abelianization can
distinguish two members of the scaling family.
