---
rg: 2
id: leavitt-odd-nine-proof
kind: route
title: Generate reduced necklaces directly and certify all length-nine free-factor syllables
target: leavitt-no-odd-nine-corner-relations
requires:
  - leavitt-no-odd-five-seven-corner-relations
---

The artifact uses the Fredricksen--Kessler--Maiorana recursion to generate
rotation-minimal necklaces directly, then quotients inversion and rejects
adjacent inverse letters.  Thus it never scans the ambient `8^9` word set.

For each of the `2241906` representatives it expands
`h_1=q_0p_1`, `k_2=p_0e_1`, simplifies the exact elementary abelian root
subgroup `<a,e,q>`, cancels adjacent `p,p^(-1)`, deletes trivial factor
syllables, and iterates after merging newly adjacent syllables.  Every
remaining syllable moves an explicitly tested basis vector in the standard
infinite-word module.  The MSI output is

```text
LENGTH 9 ORBIT_REPRESENTATIVES 2241906
CONSERVATIVE_SURVIVORS 0
UNKNOWN_BLOCKS 0.
```

Hence every word has a nonempty reduced `G_0*G_1` normal form.

