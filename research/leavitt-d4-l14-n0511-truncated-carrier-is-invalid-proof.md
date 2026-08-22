---
rg: 2
id: leavitt-d4-l14-n0511-truncated-carrier-is-invalid-proof
kind: route
title: Restore the omitted endpoint syllables by matching the two exact normal-form parametrizations
target: leavitt-d4-l14-n0511-truncated-carrier-is-invalid
requires:
  - leavitt-d4-l14-n0511-first-carrier-splits-five-ways
  - leavitt-d4-l14-n0511-branch1-is-fenced
---

The exact branch-I normal form used by the exhaustive cancellation-tree
proof writes

```text
p=g1, b=g10, c=g11, d=g12
```

and gives the carrier

```text
H=c_0 d_1 p^-1_2 b_3.
```

Under the notation of the removed truncated calculation this is exactly

```text
H=j_0 k_1 a^-1_2 i_3.
```

The two omitted terms are not removable decorations: they lie in free
factors zero and three, respectively, and occur in the exact reduced
nineteen-syllable boundary proved in
`leavitt-d4-l14-n0511-branch1-is-fenced`.  Deleting them changes both the
carrier normal form and every insertion of `H^-1` in the boundary.  Hence
neither the two-copy carrier nor the derived eighteen-syllable periodic
word is a consequence of the classified carrier system.

