---
rg: 2
id: free-group-coset-wreaths-satisfy-pbh
kind: claim
title: For every finitely generated subgroup C of a free group F, the coset lamplighters A wr_(F/C) F and the identity-edge extensions F *_C (C x K) lie in the permutational Boone--Higman class
distinct_from:
  pbh-coset-wreaths-iff-identity-edge-hnns: that is the equivalence for one subgroup C and its sufficient conditions; this adds normal virtual retracts to those conditions and applies them to every finitely generated subgroup of a free group.
  pbh-closed-under-decidable-permutational-wreaths: that is the open closure for all decidable stabilizers over all G in B_A; this settles it for free top groups with finitely generated stabilizers, including the first test case recorded there.
  ascending-hnn-of-free-groups-satisfy-boone-higman: that is ascending HNN extensions of free groups; this is identity-edge HNN extensions over arbitrary finitely generated subgroups.
---

**ESTABLISHED** by `free-group-coset-wreaths-satisfy-pbh-proof` (lane proof, not
reviewed; no priority claimed).

## Statement

**Criterion (normal virtual retracts).** Let `G ∈ B_A` and `C <= G`. Suppose some
finite-index normal subgroup `N ⊴ G` has `N ∩ C` a retract of `N`. Then conditions
(a)–(e) of `pbh-coset-wreaths-iff-identity-edge-hnns` hold for `C`. In particular, for
all `A, K ∈ B_A`:
- `A wr_(G/C) G ∈ B_A`;
- `G *_C (C × K) ∈ B_A`.

**Free groups.** Every finitely generated subgroup `C` of a finitely generated free
group `F` satisfies this criterion. So for all `A, K ∈ B_A`, both `A wr_(F/C) F` and
`F *_C (C × K)` lie in `B_A`. In particular:
- the identity-edge HNN extensions `<F, t | [t, c] = 1 (c ∈ C)>`;
- the coset lamplighters `Z wr_(F/C) F`, including the test case `Z wr_(F_2/<a>) F_2`
  of `pbh-closed-under-decidable-permutational-wreaths`

all embed in finitely presented simple groups.

## Scope

- **Virtual retracts.** The criterion needs a *normal* finite-index subgroup `N` with
  `N ∩ C` a retract of `N`. A virtual retract in the usual sense (a retract of some
  finite-index `H ⊇ C`) is not enough for the argument as written. The problem is the
  orbits of `H` through cosets `gC` with `g ∉ H`.
- **Other classes.** For free groups, Marshall Hall's theorem and the Kurosh subgroup
  theorem supply `N`. For surface groups, limit groups and virtually special groups,
  finitely generated or quasiconvex subgroups are virtual retracts, but the normal form
  of the criterion is not checked here.
