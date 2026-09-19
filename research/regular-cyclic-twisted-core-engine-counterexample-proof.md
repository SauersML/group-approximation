---
rg: 2
id: regular-cyclic-twisted-core-engine-counterexample-proof
kind: route
title: T = Z V_Z is perfect and not finitely presented, so the engine reflection theorem forbids every finitely presented group between D(F_T) and F_T
target: regular-cyclic-twisted-core-has-non-fp-stabilizer-engine
requires:
  - stabilizer-engines-force-fp-vertex-groups
  - regular-cyclic-twisted-core-is-decidable-mif-non-fp
---

1. **Properties of `T`.** By `regular-cyclic-twisted-core-is-decidable-mif-non-fp`, `T`
   is infinite, finitely generated and simple, has solvable word problem, and is not
   finitely presented. It is countable, since it is finitely generated. So it is a
   legitimate vertex group in the engine setting.
2. **`T` is perfect.** An abelian simple group is cyclic of prime order, hence finite.
   `T` is infinite and simple, so it is nonabelian. Then `[T, T]` is a nontrivial normal
   subgroup, so `[T, T] = T`.
3. **Applying the engine theorem.** By `stabilizer-engines-force-fp-vertex-groups`
   item 4, with `B = T`, a finitely presented `E` with `D(F_T) ≤ E ≤ F_T` would make `T`
   finitely presented. That contradicts step 1. `∎`

With `k = 2`, `T` meets every hypothesis of
`simple-inputs-have-finitely-presented-stabilizer-engines`: it is infinite, finitely
generated, simple and has solvable word problem. But `D(F_T)` is not finitely
presented, so that claim is refuted.
