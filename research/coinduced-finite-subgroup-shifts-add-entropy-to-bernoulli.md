---
rg: 2
id: coinduced-finite-subgroup-shifts-add-entropy-to-bernoulli
kind: claim
title: Over every countably infinite group, a shift co-induced from a finite subgroup adds H(Y)/|F| to the base entropy of a Bernoulli shift
distinct_from:
  bernoulli-shifts-with-equal-base-entropy-are-isomorphic: that is Seward's isomorphism theorem for Bernoulli shifts, the case of co-induction from F-shifts; this extends his construction to actions co-induced from arbitrary finite F-spaces, which are not Bernoulli shifts themselves.
  bernoulli-isomorphism-collapse-set-is-a-subgroup: that organizes isomorphisms between Bernoulli shifts of different entropy on one group; this proves, on every group, isomorphisms between Bernoulli shifts and products of Bernoulli shifts with non-Bernoulli co-induced actions, at the entropy a sofic count predicts.
artifacts:
  - research/artifacts/bernoulli-negative-coinduced-ornstein-2026-09-12.md
  - research/artifacts/bernoulli-negative-induced-absorption-2026-09-12.md
---

**ESTABLISHED** by [[coinduced-finite-subgroup-shifts-add-entropy-proof]].

**Reviewed** by `ex-verify-dynamics` (§1 of `research/artifacts/ex-review-dynamics-2026-09-12.md`).
Corollary D passes. The review made two corrections, both included in the statement below.
- `G` must be infinite. For `G = F`, `Coind(Y) = Y`, and two non-isomorphic F-spaces of equal entropy can
  share a free orbit. Step 2 of the proof uses that `G/F` is infinite.
- Theorem C needs `H(nu_i|P) < ∞`. Otherwise Step 4 cancels an infinite term, and the complements can have
  different entropy. Every use in the graph has a finite free orbit `P`, so no consumer is affected.

Let `G` be a countably infinite group and `F <= G` finite. For a standard probability space `(Y, nu)` with a
measure-preserving `F`-action, let `Coind(Y)` be the space of `x: G -> Y` with `x(tf) = f^-1 . x(t)`, with
the product measure over a transversal of `G/F` and `(g.x)(t) = x(g^-1 t)`. Bernoulli shifts are the case
`Y = L^F`.

**Theorem C.** If two F-spaces `Y_1, Y_2` have equal Shannon entropy and share an `F`-invariant set `P` of
positive measure on which `F` acts freely and the two measures agree and have finite
Shannon entropy on `P`, then `Coind(Y_1) ≅ Coind(Y_2)`.

**Corollary D.** If `|F| >= 2`, `H(Y) < ∞` and `0 < H(K) < ∞`, then

    Coind(Y) × K^G ≅ M^G   whenever   H(M) = H(K) + H(Y)/|F|.

In particular a generalized Bernoulli shift `L^(G/F)` over the cosets of a finite subgroup, times any
nontrivial finite-entropy Bernoulli shift, is a Bernoulli shift with base entropy `H(K) + H(L)/|F|`.

**Proof shape.** Theorem C is Seward's proof of arXiv:1805.08279v1 Theorem 3.2 transcribed:
- a common factor records the labels in `P` and marks the other cosets;
- the marked cosets get Borel distinguished roots and an aperiodic transformation `T`;
- Ornstein's isomorphism theorem along the `T`-rows recodes the complementary labels, whose entropies agree.

Corollary D tunes the bases so that `Y × K^F` and `M^F` share one free orbit with equal point masses, then
applies Theorem C and Seward's Theorem 1.1.

**Why it matters here.** Seward's theorem only moves between Bernoulli shifts, so algebraic self-absorptions
of Bernoulli shifts (`stable-finiteness-failure-is-algebraic-bernoulli-absorption`) cannot be converted by it
into Bernoulli isomorphisms. Corollary D converts summands co-induced from finite subgroups, and the entropy it
adds is `log p` times their lifted p-adic trace. Module isomorphisms conserve that trace
(`finite-subgroup-induced-absorption-conserves-entropy`). So this theorem cannot produce a Bernoulli collapse
from algebra alone, and `induced-projective-absorption-breaks-bernoulli-classification` is vacuous.

**Sanity checks.**
- Over amenable groups the statement is consistent with Ornstein–Weiss theory. `Coind(Y)` is a factor of a
  Bernoulli shift, because every finite F-space is an equivariant factor of an F-shift with nonatomic base. A
  Følner count over cosets gives it Kolmogorov–Sinai entropy `H(Y)/|F|`, and entropy is additive on products.
- Over sofic groups `F_p[G]` is stably finite (Elek–Szabó). So the application in Theorem E has no hypothesis
  to test there, and no contradiction with sofic entropy can arise.

The novelty check was bounded. Seward's paper and the graph were read (no co-induced Ornstein statement was
found), and no wider literature search was done.
