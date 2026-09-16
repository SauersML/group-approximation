---
rg: 2
id: stw99-lxi-from-prime-case-and-loop-detection
kind: route
title: LXI follows from the prime quotient-minimal case and loop detection by K1(SD)
target: stw99-problem-lxi-properly-infinite-k1-injective
requires: [prime-quotient-minimal-k1-trivial-unitaries-are-null, properly-infinite-unitary-loops-detected-by-k1-suspension, nonprime-minimal-lxi-counterexample-yields-loop-witness]
artifacts:
  - research/artifacts/lxi-quotient-minimal-counterexamples-2026-09-16.md
---

Suppose `A` is unital and properly infinite, `u ∈ U(A)`, `[u] = 0` in `K_1(A)` and `u ∉ U_0(A)`.

**Step 1 (quotient-minimal quotient; artifact Proposition 1, after Rohde's thesis, Lemma 5.1.7).** Let `S`
be the set of closed ideals `I` with `q_I(u) ∉ U_0(A/I)`. It contains `0`. Let `C ⊆ S` be a nonempty
chain and `J` the closure of its union. If `q_J(u) ∈ U_0(A/J)`, lift through the quotient map
(`U_0` lifts, by lifting exponentials): some `w ∈ U_0(A)` has `y = w^* u ∈ 1 + J`. Since the chain is
increasing with dense union, some `I ∈ C` has `dist(y − 1, I) < 1`, so `||q_I(y) − 1|| < 1`,
`q_I(y) ∈ U_0(A/I)`, and `q_I(u) = q_I(w) q_I(y) ∈ U_0(A/I)`. That contradicts `I ∈ S`, so `J ∈ S`. Zorn's
lemma gives a maximal `I ∈ S`.

`B = A/I` is nonzero, unital and properly infinite. `v = q_I(u)` has `[v] = 0` and `v ∉ U_0(B)`. Every
nonzero ideal of `B` is `I'/I` with `I' ⊋ I`, and `B/(I'/I) = A/I'`, where `q_{I'}(u) ∈ U_0` by maximality.
So `(B, v)` is a quotient-minimal witness.

**Step 2 (case split).**
- If `B` is prime, `prime-quotient-minimal-k1-trivial-unitaries-are-null` gives `v ∈ U_0(B)`, which is a
  contradiction.
- If `B` is not prime, `nonprime-minimal-lxi-counterexample-yields-loop-witness`, item 2, gives a unital
  properly infinite `D` and a based loop `l` in `U(D)` with trivial class in `K_1(SD)` that is not null
  relative to `{0, 1}`. That contradicts `properly-infinite-unitary-loops-detected-by-k1-suspension`.

So no such `u` exists, and every unital properly infinite C\*-algebra is K1-injective.

The converse routes `prime-minimal-unitaries-null-from-lxi` and `unitary-loop-detection-from-lxi` make this
an equivalence. Neither prerequisite is currently known to be easier than LXI.
