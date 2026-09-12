---
rg: 2
id: stw07-qd-trace-positive-class-kills-qd-extension
kind: claim
title: A singular K_0-class positive on all quasidiagonal traces yields a stably finite nonquasidiagonal extension
distinct_from:
  stw07-counterexample-has-singular-trace-normal-form: that is a normal form every counterexample must have; this is a sufficient mechanism producing one from a K_0-class that separates quasidiagonal traces from the rest.
  brown-dadarlat-qd-extensions-and-k0-hahn-banach: that equates global properties of the whole class; this is a single-algebra obstruction theorem with an explicit trace hypothesis.
artifacts:
  - research/artifacts/stw07-k0-hahn-banach-trace-sign-2026-09-11.md
---

**ESTABLISHED (Theorem A of the artifact).**  Let `A` be a separable unital
quasidiagonal C\*-algebra and let `x in K_0(A)` satisfy
`Zx cap K_0^+(A) = {0}`.  Suppose `(Tr tensor tau)(x) > 0` for every
quasidiagonal tracial state `tau` of `A`.  Then:

1. every asymptotically multiplicative c.c.p. model of `A` that is not
   asymptotically zero has strictly positive `K_0`-value on `x` eventually; so
   `A` fails the K_0-Hahn--Banach property at `x`;
2. every extension `0 -> K tensor A -> E -> C(T) -> 0` with index
   `[z] -> x` is separable, unital, stably finite and not quasidiagonal;
3. if `A` is nuclear, `E` is nuclear, so `E` is a negative answer to STW
   Problem VII and a counterexample to the extension conjecture with UCT
   quotient `C(T)`.

The engine is that model values are `k_n (omega_n(x^) + o(1))` with the
trace states `omega_n` of the model accumulating only at quasidiagonal traces.
In a quasidiagonal model of `E` the lift of `z` is an approximate partial
isometry whose source and range projections have equal rank, forcing value
`0` on `x`.
