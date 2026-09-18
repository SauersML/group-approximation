---
rg: 2
id: pbh-coset-condition-passes-to-finite-index-overgroups
kind: claim
title: If C satisfies the coset-wreath condition in G, so does every subgroup containing C with finite index, and so does the setwise stabilizer of any finite set of cosets of C
distinct_from:
  pbh-coset-wreaths-iff-identity-edge-hnns: that proves the equivalence of conditions (a)--(e) and lists finite subgroups, centralizers, retracts, fixed subgroups and finite intersections as cases; this adds closure under finite-index overgroups and finite set-stabilizers, which none of those cases gives.
  free-group-coset-wreaths-satisfy-pbh: that is the normal-virtual-retract criterion (passing down to a finite-index normal subgroup of G); this passes up from C to finite-index overgroups of C inside G.
---

**ESTABLISHED** by `pbh-coset-condition-finite-index-overgroups-proof` (lane proof,
elementary, not reviewed; no priority claimed).

Let `G ∈ B_A`. Say `C ≤ G` is **good** if it satisfies the equivalent conditions (a)--(e)
of `pbh-coset-wreaths-iff-identity-edge-hnns`; for example `Z/2 wr_(G/C) G ∈ B_A`, or
`G *_C (C × K) ∈ B_A` for every `K ∈ B_A`.

## Statement

Let `C ≤ G` be good.
1. For every finite set `S ⊆ G/C`, its setwise stabilizer `Stab_G(S)` is good.
2. In particular, every `C'` with `C ≤ C' ≤ G` and `[C' : C] < ∞` is good.

## Examples

- For `h` of infinite order in a hyperbolic group `H`, the maximal elementary subgroup
  `E(h)` is good, because it contains the centralizer `C_H(h)` with finite index. This
  holds with torsion. See `cusp-extensions-of-rel-hyperbolic-groups-satisfy-pbh`.
- Normalizers `N_G(C)` with `[N_G(C) : C] < ∞` are good whenever `C` is.
