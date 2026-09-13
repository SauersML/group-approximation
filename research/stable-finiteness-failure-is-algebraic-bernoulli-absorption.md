---
rg: 2
id: stable-finiteness-failure-is-algebraic-bernoulli-absorption
kind: claim
title: Stable finiteness fails for F_p[G] exactly when a Bernoulli shift over G algebraically absorbs a nontrivial factor of itself
distinct_from:
  stable-finiteness-failure-refutes-surjunctivity: that turns a one-sided inverse into an injective nonsurjective automaton, a topological map on one full shift; this turns the same datum into a measure conjugacy between a Bernoulli shift and its product with a nontrivial algebraic factor, and proves the converse at the algebraic level.
  bernoulli-entropy-counterexample-constraints: that proves necessary conditions on a group where base entropy fails to classify Bernoulli shifts; this identifies the algebraic self-absorption produced by a Kaplansky counterexample and the single extra property, Bernoullicity of the absorbed factor, that would make it such a failure.
  homomorphic-codes-cannot-compress-bernoulli-shifts: that excludes homomorphic codes into a smaller alphabet; this is a homomorphic conjugacy that keeps the alphabet and splits off a nontrivial factor instead.
---

**ESTABLISHED** by [[stable-finiteness-algebraic-bernoulli-absorption-proof]].

Let `G` be a countable group, `p` a prime and `n >= 1`. For a countable left `F_p[G]`-module
`M`, write `X_M = Hom(M, F_p)`, a compact abelian group with Haar measure and the dual action
`(g.x)(a) = x(g^-1 a)`. The dual of `F_p[G]^n` is the uniform Bernoulli shift `(F_p^n)^G`.
The following are equivalent.

1. `M_n(F_p[G])` is not directly finite: there are `A, B` with `BA = I != AB`.
2. There is a nonzero countable `F_p[G]`-module `M` and a continuous group isomorphism
   `(F_p^n)^G -> (F_p^n)^G × X_M` intertwining the actions.

When they hold, `M` can be taken to be `P = F_p[G]^n (I - AB)`, a nonzero finitely generated
projective module with `F_p[G]^n ≅ F_p[G]^n ⊕ P`. Moreover:

- (a) `X_P` is a nontrivial factor of `(F_p^n)^G`, and every nonzero element of `P` has a finite
  stabilizer. So `X_P` passes the test of `bernoulli-factor-algebraic-actions-have-finite-stabilizers`.
- (b) Every Bernoulli shift over `G` with base entropy at least `n log p` is measurably isomorphic
  to its product with `X_P`. This uses `bernoulli-shifts-with-equal-base-entropy-are-isomorphic`.
- (c) Suppose `X_P × b(s) ≅ b(s')` for base entropies `s != s'` with `s, s' < ∞`, where `b(h)`
  is the Bernoulli class of base entropy `h`. Then the Bernoulli shifts with base entropies
  `n log p + s` and `n log p + s'` are isomorphic, so `G` fails
  `bernoulli-shift-entropy-classifies-for-every-group`. The case `s = 0` asks that `X_P` itself
  be Bernoulli.

Over a finite field `F_q` with `[F_q : F_p] = d`, a one-sided inverse in `M_n(F_q[G])` stays one in
`M_(nd)(F_p[G])` through the regular representation of `F_q`, so the statement covers `F_q` with
`nd` in place of `n`.

**Reading.**
- A Kaplansky counterexample over a finite field makes a Bernoulli shift contain an independent,
  nontrivial algebraic factor of itself as "free information": `b ≅ b × X_P ≅ b × X_P^k` for every
  `k`. A failure of base-entropy classification is the same kind of absorption, `b(h_1) ≅ b(h_1) × b(h_2 − h_1)`,
  with a Bernoulli factor in place of `X_P`. The gap between the two problems is whether an
  absorbed factor can be taken Bernoulli.
- The Leavitt algebra's own doubling `L ≅ L ⊕ L` gives an exact self-square over the unit group
  (`leavitt-module-dual-actions-are-self-squares-off-bernoulli`), but it fails the stabilizer
  test. Inside the Bernoulli world, algebraic doubling is exactly stable finiteness failure.
- No group with `F_p[G]` not stably finite is known, so (c) is conditional twice: on a
  counterexample such as `leavitt-unit-group-algebra-not-directly-finite`, and on Bernoullicity
  of the absorbed factor. By `bernoulli-entropy-counterexample-constraints`, (c) forces
  `h^Rok_sup(G) <= n log p + min(s, s')`. That is consistent with
  `strict-automaton-bounds-rokhlin-supremum`, which bounds the supremum for the same datum.
