---
rg: 2
id: hard-type-a-actors-via-seed-full-groups
kind: route
title: Hard-to-evaluate seeds with finitely presented full groups give type (A) actors, highly transitive on the seed orbit, whose orbit problem reads the seed
target: type-a-actors-with-arbitrarily-hard-word-problem
requires:
  - hard-evaluation-seeds-with-finitely-presented-full-groups
  - seed-full-groups-act-oligomorphically-on-the-seed-orbit
  - twisted-brin-thompson-wp-equals-actor-orbit-problem
---

Fix a recursive `T` and put `T+(m) = m + max_(k<=m) T(k)`.

1. **The seed.** `hard-evaluation-seeds-with-finitely-presented-full-groups`, applied to `T+`,
   gives `Γ`, `Y`, `y_*` and `s`, with `F = [[Γ ⋉ Y]]` finitely presented and
   `Stab_F(y_*)` finitely generated.
2. **The actor.** By `seed-full-groups-act-oligomorphically-on-the-seed-orbit`, `F ↷ O = Γ·y_*`
   is faithful and highly transitive. Its stabilizers are conjugate to `Stab_F(y_*)`, so the
   action is of type (A).
3. **The hardness.** `E_s(y_*)` reduces to `OP(F, O)` with linear length blow-up (item 3 there).
   So `OP(F, O)` is not decidable in time `C·T(C·ℓ) + C`.
4. **Transfer.** By the orbit-problem form of the target
   (`twisted-brin-thompson-wp-equals-actor-orbit-problem`), the word problem of `SV_F` beats `T`.
   So the target holds.

**What the route changes.** Before, the hardness had to be put into an actor's own word problem.
Here it lives in one computable configuration over a group whose word problem may be easy, and
oligomorphy is free. What remains is exactly the SEED gates (S3), P2′-type finite presentation,
and one finitely generated stabilizer. That is, the hard-actor claim merges into (SEED). `∎`
