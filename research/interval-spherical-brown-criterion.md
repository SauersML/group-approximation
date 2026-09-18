---
rg: 2
id: interval-spherical-brown-criterion
kind: claim
title: A group acting on a highly connected union of finite poset intervals is of type FP_n, or finitely presented, if only the homologically essential intervals are counted and their stabilizers have the finiteness matching their homological degree
distinct_from:
  twisted-brin-thompson-type-fn-criterion: that is one application, to twisted Brin--Thompson groups of faithful actions; this is the abstract criterion behind it, stated for any order-preserving action on a poset.
  abstract-twisted-bt-type-fn-criterion: that is the application to abstract twisted Brin--Thompson groups; this is the general tool.
  type-a-action-gives-boone-higman-for-subgroups: that is Zaremsky's finite-presentation theorem for one family; the n = 2 homotopical part of this criterion reproves it from local data.
---

**ESTABLISHED** by `interval-spherical-brown-criterion-proof` (lane proof, assembling the
arguments of `twisted-bt-type-fn-interval-filtration-proof` and
`abstract-twisted-bt-type-fn-colored-stein-proof`). Referee c (independent second pass): **PASS**,
`research/artifacts/gq-referee-c-abstract-twisted-bt-type-fn-criterion.md` (72d2941ac), which covers this node.
Citation pass (gq-referee-b) requested. It is a variant of Brown's
criterion. Filtering by intervals is standard (Belk--Zaremsky use it for contractibility);
the graded use of stabilizers is the point. No priority claimed.

## Setting

- A group `Γ` acts by order-preserving maps on a poset `Q` with a `Γ`-invariant rank
  `ρ: Q → Z` that is strictly increasing along `<`.
- `𝓘` is a `Γ`-invariant family of finite closed intervals `[v, w]`. It is closed under
  sub-intervals, contains `[v, v]` for every `v` involved, and has bounded length
  `ρ(w) − ρ(v) ≤ L`.
- `Y = ⋃_{I ∈ 𝓘} |I| ⊆ |Q|`. Assume every chain `σ` of `Y` has `[min σ, max σ] ∈ 𝓘`.
- Call `I = [v, w]`, `v < w`, **essential of degree `e(I)`** if
  `H̃_*(|(v, w)|; Z) ≅ Z` in degree `e(I) − 2` and vanishes otherwise, and **inessential**
  if `|(v, w)|` is acyclic. Here `|∅|` has `H̃_{−1} = Z`, so covers are essential of degree 1.
- `Γ_I` denotes the stabilizer of the pair `(v, w)`.

## Statement

**(FP_n)** Suppose:
1. `Y` is `(n−1)`-acyclic;
2. every interval in `𝓘` of positive length is essential or inessential;
3. vertex stabilizers are of type `FP_n`, and `Γ_I` is of type `FP_{n−e(I)}` for every
   essential `I` with `e(I) ≤ n`;
4. there are finitely many `Γ`-orbits of vertices of `Y` and of essential intervals with
   `e(I) ≤ n`.

Then `Γ` is of type `FP_n`. Inessential intervals, and essential ones with `e > n`, may lie
in infinitely many orbits and have arbitrary stabilizers.

**(finite presentation)** Suppose instead:
1. `Y` is simply connected;
2. vertex stabilizers are finitely presented, and stabilizers of covers (intervals with
   `(v, w) = ∅`, of any length) are finitely generated;
3. there are finitely many orbits of vertices, of covers, and of non-cover intervals `I`
   for which `|(v, w)|` is disconnected.

Then `Γ` is finitely presented. Intervals whose open part is connected impose no condition.
No lattice structure, joins of atoms or grading is assumed. Covers may have any rank
difference, so the criterion applies to posets of dissections with "prime" pieces, the
non-LCM setting.

## Instances

- `SV_G` with the interval lattice of dyadic partitions: essential intervals are the grid
  intervals, with `e` equal to the number of colors
  (`stein-complex-elementary-intervals-are-grid-spheres`).
- The criterion gives `(A_n) ⇒ F_n` for faithful actions (`twisted-brin-thompson-type-fn-criterion`)
  and for all actions (`abstract-twisted-bt-type-fn-criterion`). The finite-presentation part
  reproves Zaremsky's theorem.

## Lesson for general BH

Every Thompson-like Boone--Higman envelope is a group of this shape: a full group acting on
a Stein-type poset of partitions. For such an envelope, finite presentation needs only
four inputs:
- a simply connected sublevel complex;
- finitely presented vertex stabilizers;
- finitely generated single-split stabilizers;
- finitely many orbits of the intervals whose open part is disconnected, which are the pairs
  of commuting splits.

Stabilizers of long elementary edges never matter. Nor do lcms: a dissection operad with
infinitely many primes gives covers of unbounded length, but only finitely many of them
below any rank bound. So its failure to be finitely generated obstructs finite presentation
only through the simple connectivity of the sublevel complexes (hypothesis 1), that is,
through descending links. For routes whose last open step is finite
presentation of an explicit Cantor full group (shell envelopes, Röver--Nekrashevych-type,
groupoid full groups), the interval homotopy types and these stabilizers are the only things
to compute.
