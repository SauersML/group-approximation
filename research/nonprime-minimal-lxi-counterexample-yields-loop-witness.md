---
rg: 2
id: nonprime-minimal-lxi-counterexample-yields-loop-witness
kind: claim
title: A non-prime quotient-minimal LXI counterexample gives an undetected unitary loop in a properly infinite quotient
distinct_from:
  properly-infinite-unital-algebra-not-k1-injective-exists: that claim asserts some witness exists; this one assumes a witness with a special ideal structure and manufactures a second witness of the form C(T, D) out of it.
  stw99-problem-lxi-properly-infinite-k1-injective: the root asserts no witness exists; this is a structural statement about hypothetical witnesses and does not decide the root.
artifacts:
  - research/artifacts/lxi-quotient-minimal-counterexamples-2026-09-16.md
---

**Terms.** A *witness* is a pair `(B, v)` where `B` is a unital properly infinite C\*-algebra,
`v ∈ U(B)`, `[v] = 0` in `K_1(B)` and `v ∉ U_0(B)`. It is *quotient-minimal* if `q_J(v) ∈ U_0(B/J)` for
every nonzero closed two-sided ideal `J` of `B`. `B` is *prime* if any two nonzero ideals have nonzero
intersection. For a unital `E`, a *based loop* is a continuous `l: [0,1] → U(E)` with `l(0) = l(1) = 1`.
Its class `kappa_E(l) ∈ K_1(SE)`, with `SE = C_0((0,1), E)`, is the class of the unitary `1 + (l − 1)`
of `(SE)~`.

**Statement.** Let `(B, v)` be a quotient-minimal witness, and suppose `B` is not prime. Pick nonzero
ideals `J_1, J_2` with `J_1 ∩ J_2 = 0`. Put `B_i = B/J_i` and `D = B/(J_1 + J_2)`, and let
`pi_i: B_i → D` be the induced quotient maps. Then:

1. `D ≠ 0`, so `D` is unital and properly infinite.
2. There is a based loop `l` in `U(D)` with `kappa_D(l) = 0` whose class in `pi_1(U(D), 1)` does not lie
   in the subgroup `pi_{1*} pi_1(U(B_1), 1) · pi_{2*} pi_1(U(B_2), 1)`. In particular `l` is not
   homotopic to the constant loop relative to `{0, 1}`.
3. `(C(T, D), l)` is a witness, where `l` is regarded as a unitary of `C(T, D)` via `[0,1]/{0,1} = T`.

The loop is `l = (pi_1 ∘ g_1) * (pi_2 ∘ g_2)̄` for suitable paths `g_i` in `U(B_i)` from 1 to `q_{J_i}(v)`.
Here `*` denotes concatenation and the bar reverses a path. The proof is artifact
`lxi-quotient-minimal-counterexamples-2026-09-16`, Theorem 3 and Corollary 4.
