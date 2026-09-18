---
rg: 2
id: virtual-retracts-satisfy-pbh-coset-wreath-closure
kind: claim
title: Virtual retracts satisfy the coset-wreath conditions, so for every finitely generated subgroup C of a limit group or of a finitely generated virtually free or Fuchsian group G, the lamplighters A wr_(G/C) G, the identity-edge HNNs and the doubles G *_C G lie in B_A
distinct_from:
  free-group-coset-wreaths-satisfy-pbh: that proves the free-group case through a normal finite-index subgroup and Kurosh, and records that plain virtual retracts are not enough for its argument; this proves that they are, and extends the conclusion to limit groups and to finite-index overgroups (virtually free, Fuchsian, virtually limit groups).
  pbh-coset-wreath-subgroups-closure-properties: that is the general closure statement; this is its virtual-retract consequence and the classes it covers.
artifacts:
  - research/artifacts/gq-bh-openq-papers-list.md
---

**ESTABLISHED** by `virtual-retracts-satisfy-pbh-coset-wreath-closure-proof` (lane proof;
not independently reviewed; no priority claimed). `CR(G)` is as in
`pbh-coset-wreath-subgroups-closure-properties`.

## Statement

1. **Virtual retracts.** Let `G ∈ B_A`, let `K ≤ G` have finite index, and let `C ≤ K` be a
   retract of `K`. Then `C ∈ CR(G)`. So for all `A, K' ∈ B_A`, all of the following lie
   in `B_A` and, when finitely generated, embed in finitely presented simple groups:
   - `A ≀_{G/C} G`;
   - `G *_C (C × K')`, in particular the identity-edge HNN `⟨G, t | [t, c] = 1 (c ∈ C)⟩`;
   - the double `G *_C G`.
2. **Groups with property (LR).** Suppose every finitely generated subgroup of `G ∈ B_A` is
   a virtual retract ("property (LR)", Minasyan, arXiv:1810.02654). Then every finitely
   generated subgroup of `G`, and of every group containing `G` with finite index, lies in
   `CR`.
3. **Classes covered.** Item 2 applies to:
   - finitely generated free groups (Marshall Hall);
   - limit groups, i.e. finitely generated fully residually free groups, including closed
     orientable surface groups of genus `≥ 2` (Wilton, arXiv:math/0605546);
   - finitely generated virtually free groups, e.g. `PSL_2(Z)`, `SL_2(Z)` and free products
     of finite groups;
   - finitely generated Fuchsian groups;
   - finite-index overgroups of limit groups.

So for every finitely generated subgroup `C` of any of these groups `G`,
`Z ≀_{G/C} G`, `⟨G, t | [t, C] = 1⟩` and `G *_C G` embed in finitely presented simple groups.

## Remarks

- Minasyan (arXiv:1810.02654, abstract) records that (LR) is **not** stable under
  finite-index overgroups and asks whether all finitely generated virtually free groups
  satisfy (LR). Item 2 does not need it: the coset-wreath conditions are inherited by
  finite-index overgroups (`pbh-coset-wreath-subgroups-closure-properties`, part 2).
- `Z ≀_{F_2/⟨[a,b]⟩} F_2` is already covered by `free-group-coset-wreaths-satisfy-pbh`. It
  is also covered by case 2 (centralizers) of `pbh-coset-wreaths-iff-identity-edge-hnns`,
  since `⟨[a,b]⟩ = C_{F_2}([a,b])`.
