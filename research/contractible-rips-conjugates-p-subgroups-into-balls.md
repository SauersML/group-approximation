---
rg: 2
id: contractible-rips-conjugates-p-subgroups-into-balls
kind: claim
title: A contractible Rips complex conjugates every finite p-subgroup into the d-ball and bounds the cohomological dimension of every torsion-free subgroup
distinct_from:
  contractible-rips-complex-gives-finite-classifying-space: that is the torsion-free case, where the whole group gets a finite K(G,1); this treats groups with torsion, bounds every torsion-free subgroup, and adds a second invariant, finite p-subgroups, through Smith theory
  thompson-f-has-no-contractible-rips-complex: that is one consequence of the dimension bound for F; this is the general invariant, which also rules out groups such as Thompson's T that contain 2-groups of unbounded order
  smith-fixed-point-theorem-for-finite-p-groups: that is the classical fixed point theorem; this applies it to Rips complexes of groups
---

**ESTABLISHED** (route `contractible-rips-conjugates-p-subgroups-into-balls-proof`).

Let `G` be a group with a finite symmetric generating set `S`, let `d >= 1`, and
suppose the Rips complex `R_d(G,S)` is contractible. (Its simplices are the finite
nonempty subsets of `G` with pairwise `S`-distance at most `d`.) Put
`N = |B_S(d)|`. Then:

1. **Dimension.** Every torsion-free subgroup `H <= G` has `cd H <= N - 1`.
2. **Smith invariant.** For every prime `p` and every finite `p`-subgroup `P <= G`
   there is `y ∈ G` with `y^-1 P y ⊆ B_S(d)`. Hence `|P| <= N`, and `G` has at most
   `2^N` conjugacy classes of finite subgroups of prime-power order.

So either invariant obstructs contractible Rips complexes by itself:

- a torsion-free subgroup of infinite cohomological dimension, as in Thompson's `F`;
- finite `p`-subgroups of unbounded order, or infinitely many conjugacy classes of
  them.

Calibration: Thompson's group `T` fails both. It contains `F` and the rotation
subgroups `Z/2^k` for every `k` (route
`weak-automaticity-does-not-give-contractible-rips-complexes-proof`, step 3).

The argument gives nothing for finite subgroups whose order is not a prime power,
because Smith theory needs a `p`-group. From memory, not re-read: Leary, *On finite
subgroups of groups of type VF* (arXiv:math/0510682), builds groups of type VF with
infinitely many conjugacy classes of a finite subgroup of non-prime-power order, which
is why no extension of item 2 is expected.
