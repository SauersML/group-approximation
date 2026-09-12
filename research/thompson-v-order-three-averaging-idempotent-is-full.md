---
rg: 2
id: thompson-v-order-three-averaging-idempotent-is-full
kind: claim
title: The averaging idempotent of an order-three element of Thompson's V is full in its binary group algebra
distinct_from:
  thompson-v-ternary-swap-idempotent-is-full: that is the ternary target for the swap involution of V; this is the binary target for an element of order three, whose averaging idempotent exists over F_2.
  leavitt-units-carry-injective-invariant-output-automaton: that asks for a possibly nonlinear automaton over the binary Leavitt units whose output is invariant under a finite subgroup; this is the linear V-internal equation, whose solutions are corner compressions inside F_2[V].
artifacts:
  - research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md
---

**OPEN.** Let `h` in `V` be the element with prefix codes `(00, 01, 1) -> (01, 1, 00)`, of
order three, and `e_h = 1 + h + h^2` in `F_2[V]`. There are `b, c` in `F_2[V]` with
`c e_h b = 1`.

Equivalently, some left-invertible `a` in `F_2[V]` satisfies `h a = a` (Section 9 of the
artifact). Then `F_2[V]` is not directly finite
(`thompson-v-df-failure-from-order-three-averaging-fullness`), and so is `F_2[R^x]`
(`thompson-v-binary-df-failure-ascends-to-leavitt-units`).

## Attempts

- **Obstructions tried.** Consistent with the equation (Section 9 of the artifact):
  - the augmentation gives `epsilon(e_h) = 3 = 1`;
  - the identity-coefficient trace gives `tau(e_h) = 1`;
  - finite-dimensional representations of `V` are trivial;
  - the Cantor orbits have no Følner sets.
- **Leavitt level.** In `L_(F_2)(1,2)` every nonzero idempotent is full, since the algebra is
  purely infinite simple. So solutions exist after evaluation. The problem is to find them inside
  `F_2[V]`, where operators on the sequence module have balanced row and column sums (Lemma 3.1).
- **Gate.** False if `V` is sofic or `F_2`-linear sofic.
- **Support filter (w3-v-linear, 2026-09-12).** By `full-averaging-idempotent-kills-its-element-in-rank-models`
  and `thompson-v-linear-witness-supports-kill-g-in-rank-models`, a witness `b, c` forces every
  characteristic-2 rank model of `H = <h, supp b, supp c>` to kill `h`. So `h` lies in the finite
  residual of `H`, and `H` is not residually finite, LEF, sofic or `F_2`-linear sofic. `h` preserves
  the cyclic order of prefixes, so it lies in Thompson's `T`. The filter constrains `H`, not the
  ambient subgroup: a `T`-supported witness with residually finite `H` is excluded. It leaves open
  witnesses whose `H` is `T` (simple, equal to its finite residual, soficity open) or any `H` in
  which `h` survives in no known rank model.
- **Kernel copy (w3-v-linear).** `thompson-v-direct-finiteness-failures-transfer-into-kernel`: with
  `x, y` 3-cycles of depth-3 prefixes inside `[0]` and `[1]`, `q = (x+x^2)(y+y^2)` is a nonzero
  kernel idempotent. The depth-3 tail-diagonal embedding gives an injective unital map
  `F_2[V] -> qF_2[V]q` killed by the Leavitt evaluation.
- **Where it dies.** Neither result decides the target. No non-monomial candidate inside a
  non-residually-finite subgroup is known.
