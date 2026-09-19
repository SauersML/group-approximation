---
rg: 2
id: orbit-finite-fp2-affine-actors-are-faithful-ha2-actors
kind: claim
title: "An FP_2 semidirect product S ⋊ W with W finitely generated and orbit-finite on S acts faithfully on S with type [HA_2]; so does Γ × Γ on a torsion-free conjugacy-finite FP_2 group Γ"
distinct_from:
  orbit-finite-affine-actions-are-type-a: that is the finitely presented version, giving type (A) actors for permutational Boone–Higman; this is the FP_2 version, giving [HA_2] actors for twisted Brin–Thompson groups of type FP_2, where S ⋊ W need not be recursively presented.
  centerless-fp-finitely-many-conjugacy-classes-gives-pbh: that uses the two-sided translation of a finitely presented centreless conjugacy-finite group, not known to exist when infinite; this uses it for groups of type FP_2 only, where the recursive-presentation obstruction of `conjugacy-finite-recursive-presentation-solvable-wp` does not apply.
  perfect-orbit-quotients-of-fp2-actors-are-ha2-actors: that builds [HA_2] actors from imprimitive actions by dividing out perfect normal subgroups; this reads off [HA_2] actors from transitive affine actions whose point stabilizer is the automorphism group W.
---

**ESTABLISHED** by `orbit-finite-fp2-affine-actors-are-faithful-ha2-actors-proof`.
Elementary; no novelty claimed for the computation. Not independently reviewed.

**(A) Affine case.** Let `S` be a group and `W ≤ Aut(S)` a finitely generated
subgroup with finitely many orbits on `S`. Let `Γ = S ⋊ W` act on `S` by
`(s,w)·x = s·w(x)`. If `Γ` is of type FP_2, this action is faithful and of type
`[HA_2]`. So every subgroup of `Γ` embeds in the simple group `SV_Γ` of type FP_2
(`ha2-actions-give-fp2-twisted-brin-thompson-groups`).

**(B) Inner case.** Let `Γ` be of type FP_2 with finitely many conjugacy classes
and trivial centre. Then `Γ × Γ` acting on `Γ` by `(a,b)·x = a x b^-1` is
faithful and of type `[HA_2]`. The centre hypothesis holds automatically when
`Γ` is torsion-free: a central `z ≠ 1` of infinite order gives the infinitely
many one-element classes `{z^n}`.

Consumers: `faithful-ha2-actor-via-orbit-finite-fp2-affine-actors` (Problem 1.25)
and `uncountably-many-ha2-actors-via-conjugacy-finite-fp2-groups` (Problem 1.20,
first part).

**Where it stops.** In (B), and in (A) for the subgroup `S`, only finitely many
element orders occur (`conjugacy-finite-actors-have-finitely-many-element-orders`),
so the inner case cannot reach inputs with infinitely many element orders. In (A)
the group `W` is unconstrained in this respect.
