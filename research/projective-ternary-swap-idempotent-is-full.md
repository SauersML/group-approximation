---
rg: 2
id: projective-ternary-swap-idempotent-is-full
kind: claim
title: The swap-averaging idempotent of the ternary Leavitt unit group modulo scalars is full in its group algebra over F_3
distinct_from:
  ternary-leavitt-swap-idempotent-is-full: that is the corner equation on the ternary unit group itself, which implies this one by projecting to a central summand; this is the equation on the quotient by the scalars F_3^x, which is the only half an automaton needs and on which the Leavitt evaluation vanishes.
  leavitt-unit-group-algebra-not-directly-finite: that is the scalar Kaplansky question for the binary unit group over F_2; this is a corner equation for an honest averaging idempotent of a different simple group in characteristic three.
artifacts:
  - research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md
---

**OPEN.** Let `PG = L_(F_3)(1,2)^x / F_3^x`, a finitely presented simple group by
`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`, let `wbar` be the image of
`w = s0 t1 + s1 t0`, and put `ebar = 2(1 + [wbar])` in `F_3[PG]`. Exhibit
`b, c in F_3[PG]` with

    c ebar b = 1.

The linear automaton of `ebar b` over `PG` is then injective with
`<wbar>`-invariant output, hence not surjective, and `PG` refutes Gottschalk's
conjecture.

## Attempts

- *Leavitt evaluation is blind here.* The evaluation `F_3[G] -> L_(F_3)(1,2)` sends
  the central involution to `-1`, so it kills this summand
  (`ternary-leavitt-swap-problem-splits-at-central-involution`). The Leavitt image
  equation gives no information about this claim.
- *The adjoint evaluation holds the equation.* `rho([g]) = g (x) (g^-1)^op` defines
  a unital ring homomorphism `F_3[PG] -> Q = R (x) R^op`. In `Q`,
  `b' = (s0 + s1) (x) (t0 + t1)^op` and `c' = (t0 + t1) (x) (s0 + s1)^op` satisfy
  `rho(ebar) b' = b'` and `c' b' = 1`, so the equation holds in `Q`. Section 7 of
  the artifact.
- *Those witnesses cannot come from the group algebra.* On `R`, every element of
  `rho(F_3[PG])` sends `1` to a scalar multiple of `1`, while `b'(1) = 1 + w`. The
  witnesses `delta(r) = s0 r t0 + s1 r t1` and `Psi(r) = 2(t0 r s0 + t1 r s1)` do
  respect that line: `Psi delta = id` and `rho(ebar) delta = delta`. It dies at
  membership. No splitting is known inside the span of the `Ad(g)`; see the
  stronger target `projective-ternary-klein-idempotent-is-full`, whose expectation is
  exactly `delta Psi`. Section 8 of the artifact.
- *No cheap obstruction.* The canonical trace of `ebar` is `2` in `F_3`, which is
  unordered. The augmentation gives `eps(ebar) = 1`. `PG` is simple and infinite,
  so it has no nontrivial finite-dimensional representation to test against.
- *What a witness must satisfy.* `PG` must be nonsofic, which holds
  (`projective-leavitt-unit-groups-mod-scalars-are-nonsofic`), and not linear sofic
  (`linear-sofic-group-algebra-is-stably-finite`), which is open. The memory of `c`
  must generate a nonamenable group
  (`amenable-decoder-memory-forces-surjectivity`). The forward table must have a
  nonsofic two-core (`forward-relations-of-a-counterexample-have-a-nonsofic-core`).
