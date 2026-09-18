---
rg: 2
id: uncountably-many-ha2-actors-via-conjugacy-finite-fp2-groups
kind: route
title: "Two-sided translation of uncountably many conjugacy-finite FP_2 groups gives uncountably many faithful [HA_2] actors"
target: uncountably-many-fp2-groups-have-faithful-ha2-actions
requires:
  - uncountably-many-torsion-free-conjugacy-finite-fp2-groups
  - orbit-finite-fp2-affine-actors-are-faithful-ha2-actors
---

Let `(Γ_i)` be the family of `uncountably-many-torsion-free-conjugacy-finite-fp2-groups`.
Each `Γ_i` is torsion-free with finitely many classes, hence centreless, and of
type FP_2. By case (B) of `orbit-finite-fp2-affine-actors-are-faithful-ha2-actors`,
`G_i = Γ_i × Γ_i` is of type FP_2 and acts faithfully on `Γ_i` with type `[HA_2]`.

Counting: `Γ_i ≅ Γ_i × 1` is a finitely generated subgroup of `G_i`, and each
countable group has countably many finitely generated subgroups. So if the `G_i`
realized countably many types, so would the `Γ_i`. Hence the `G_i` realize
uncountably many isomorphism types, which is the target.

Downstream, `uncountably-many-simple-fp2-via-faithful-ha2-actors` turns this into
uncountably many simple groups of type FP_2 (first part of Problem 1.20).
