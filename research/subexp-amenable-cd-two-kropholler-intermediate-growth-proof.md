---
rg: 2
id: subexp-amenable-cd-two-kropholler-intermediate-growth-proof
kind: route
title: Rosset-type kernels plus the cd-2 normal-subgroup theorem classify NFS groups; the ED(X) descent lifts this to the whole generating class, and Gromov turns it into a growth statement
target: subexp-amenable-cd-two-kropholler-iff-no-intermediate-growth
requires:
  - no-free-subsemigroups-give-fg-kernels-over-ea-quotients
  - amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar
  - amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical
  - kropholler-dim-two-counterexamples-live-in-generating-classes
  - gromov-and-milnor-wolf-growth-alternatives
---

Notation as in the target.

## Imports

- **(NF)** `no-free-subsemigroups-give-fg-kernels-over-ea-quotients`. If `G` is finitely
  generated and NFS, and `G/N` is EA, then `N` is finitely generated.
- **(HNN2)** `amenable-cd-two-ascending-hnn-groups-are-baumslag-solitar`, item 2. If `H` is
  amenable with `cd H <= 2`, `N ⊴ H`, `H/N ≅ Z` and `N` is finitely generated, then `N = 1` or
  `N ≅ Z`.
- **(HNN3c)** The same node, item 3(c). If `G` is finitely generated, not solvable, amenable and
  `cd G = 2`, then no finitely generated normal subgroup of `G`, including `1`, has an infinite EA
  quotient.
- **(R)** `amenable-cd-two-nonsolvable-groups-have-trivial-ea-radical`, item 2. A finitely
  generated amenable `G` with `cd G = 2` and a nontrivial EA normal subgroup is `BS(1,m)`, `m ≠ 0`.
- **(D)** `kropholler-dim-two-counterexamples-live-in-generating-classes`, item 2. Let `X` be a
  subgroup-closed class of amenable groups and `G ∈ ED(X)` with `cd G <= 2`. If every subgroup
  of `G` lying in `X` is EA, then `G` is EA.
- **(Gr)** `gromov-and-milnor-wolf-growth-alternatives`, item 1 (Gromov).
- Standard facts:
  - Stallings–Swan: an amenable group of `cd <= 1` is `1` or `Z`.
  - Serre: a finite-index subgroup of a group of finite cd has the same cd.
  - A group containing a free subsemigroup of rank two has exponential growth. Growth passes to
    finitely generated subgroups: the ball of radius `n` in a subgroup lies in a ball of radius
    `Cn` of the ambient group.
  - Groups of subexponential growth are amenable.

## The NFS class

*Subgroups* is clear. *Quotients*: if `ū, v̄` freely generate a free subsemigroup of `G/M`, any lifts
`u, v` do too, since a coincidence of two distinct positive words in `u, v` maps to one in
`ū, v̄`.

## Lemma: `BS(1,m)` with `|m| >= 2` is not NFS

Realise `BS(1,m) = Z[1/m] ⋊ Z` as affine maps of `Q`, with `t(x) = mx` and `a(x) = x + 1`. Put
`u = t` and `v = at`, so `v(x) = mx + 1`. A positive word of length `n` in `u, v` is the map
`x ↦ m^n x + Σ_{i<n} d_i m^i`, with `d_i ∈ {0,1}` recording where `v` occurs. Words of different
lengths have different linear parts, since `|m| >= 2`. Suppose two words of the same length agree.
Then `Σ e_i m^i = 0` with `e_i ∈ {-1,0,1}` not all zero. At the lowest index `j` with `e_j ≠ 0`,
`m` divides `e_j`, which is impossible. So `⟨u, v⟩` is a free semigroup.

Conversely `BS(1,±1) ∈ {Z², Kb}` is virtually abelian, so of polynomial growth, so NFS.

## Item 1

Let `G ≠ 1` be finitely generated, amenable, NFS, with `cd G <= 2`. Then `G` is torsion-free and
infinite. If `cd G = 1`, then `G ≅ Z` and all four conditions hold. Assume `cd G = 2`.

- *(a) ⇒ (b).* `G` is a nontrivial EA normal subgroup of itself, so `G ≅ BS(1,m)` by (R). By the
  lemma, `|m| = 1`, so `G ≅ Z²` (`m = 1`) or `Kb` (`m = -1`).
- *(b) ⇒ (d).* `Z²` and `Kb = ⟨a, b | bab⁻¹ = a⁻¹⟩` both map onto `Z`. Take the subgroup `G`.
- *(d) ⇒ (a).* Let `H ≤ G` have finite index and infinite abelianization. Then `H` is finitely
  generated, amenable and NFS, with `cd H = 2` (Serre), and it maps onto `Z` with kernel `N`. By
  (NF) `N` is finitely generated, and by (HNN2) `N = 1` or `Z`. So `H` is cyclic-by-cyclic,
  hence EA. The normal core `C` of `H` has finite index in `G` and is EA, so `G` is EA.
- *(a) ⇒ (c).* `G ≅ G/1` is infinite and EA.
- *(c) ⇒ (a).* Let `G/N` be infinite and EA. By (NF), `N` is finitely generated. If `G` were
  not solvable, (HNN3c) would forbid this. So `G` is solvable, hence EA.

*The consequence for `K`.* If `K` is a finitely generated NFS two-dimensional counterexample,
then `K ≠ 1` and (a) fails. So (c) and (d) fail.

## Item 2

Put `X` = amenable NFS groups: subgroup-closed.

(⇐) Assume every finitely generated amenable NFS group of cd 2 is virtually indicable. Let
`G ∈ ED(X)` have `cd G <= 2` and let `S ≤ G` lie in `X`. Every finitely generated `F ≤ S` is
amenable and NFS, with `cd F <= 2`. If `F ≠ 1` and `cd F = 1`, then `F ≅ Z`. If `cd F = 2`,
then (d) holds for `F` by hypothesis, so `F` is EA by item 1. So `S` is a directed union of EA
groups, hence EA. By (D), `G` is EA.

(⇒) Assume every group of `cd <= 2` in `ED(X)` is EA. A finitely generated amenable NFS `F` with
`cd F = 2` lies in `X ⊆ ED(X)`, so it is EA and `F ≅ Z²` or `Kb` (item 1). Hence `F` is
indicable.

## Item 3

Put `X_0` = groups all of whose finitely generated subgroups have subexponential growth. It is
subgroup-closed, consists of amenable groups, and lies in the NFS class. By item 1 of (D)'s
target, `ED(X_0)` is the smallest class containing `X_0` closed under extensions and directed
unions. That is `SG`.

- *(i) ⇒ (iii).* Let `H` be finitely generated of intermediate growth, with `cd H <= 2`. Then
  `H ≠ 1` and `H ∈ X_0 ⊆ SG`. By (i) `H` is EA, so `H ≅ Z`, `Z²` or `Kb` by item 1, which has
  polynomial growth. Contradiction.
- *(iii) ⇒ (ii).* Let `H ≠ 1` be finitely generated of subexponential growth, with `cd H <= 2`. By
  (iii) its growth is polynomial, so `H` is virtually nilpotent by (Gr), hence EA. By item 1,
  `H ≅ Z`, `Z²` or `Kb`, which is indicable.
- *(ii) ⇒ (i).* Let `G ∈ SG` have `cd G <= 2` and let `S ≤ G` lie in `X_0`. Every finitely
  generated `F ≤ S` with `F ≠ 1` has subexponential growth and `cd F <= 2`. By (ii) it is virtually
  indicable, and it is amenable and NFS. So `F` is EA by item 1 ((d) ⇒ (a)). Hence `S` is EA, and
  `G` is EA by (D). ∎

## Calibration

- `BS(1,2)` is a finitely generated amenable group of cd 2 with an infinite EA quotient
  (`Z`) whose kernel `Z[1/2]` is not finitely generated. It is correctly excluded: it contains a
  free subsemigroup (lemma), so (NF) does not apply. If the lemma were false, (c) ⇒ (a) ⇒ (b)
  would wrongly force `BS(1,2) ∈ {Z², Kb}`.
- Grigorchuk's first group has intermediate growth and lies in `SG`. It has torsion, so infinite
  cd, which is consistent with (iii).
- `Z²` and `Kb` satisfy all of (a)–(d). `Z³` is excluded from item 1 by `cd = 3`, as it must be:
  (HNN2) is specific to cd 2.
