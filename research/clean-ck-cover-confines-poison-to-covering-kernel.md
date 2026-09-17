---
rg: 2
id: clean-ck-cover-confines-poison-to-covering-kernel
kind: claim
title: Over a decidable T the marked CK cover has a decidable matrix image, so every word-problem-poisoned element lies in the covering kernel and can obstruct only the cover-layer regime
distinct_from:
  ck-cover-quotient-kernel-dichotomy: that splits maximal kernels by whether they contain the covering kernel, with no computability input; this shows that over a decidable T the matrix image is decidable, so word-problem obstructions live only in the covering kernel.
  ck-maximal-kernel-four-regimes: that classifies maximal kernels into four regimes by normal structure; this adds that no word-problem-poisoned element survives in any quotient of regimes R2-R4.
  ck-sandwich-ring-diamond-normal-form: that is the ring normal form and the decidability of EL_n(U); this applies it to the marked cover and to poisoned elements.
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that is the open existence question for maximal kernels, whose universal reading is refuted by poisoned envelopes; this shows that the poisoning mechanism cannot occur outside the covering kernel for the clean decidable marking.
---

**ESTABLISHED** by `clean-ck-cover-confines-poison-to-covering-kernel-proof`.

**Merge note (2026-09-17).** A concurrent bus lemma from
swarm-0917-w4-pull-bh-1, not in this worktree, posts
`clean-ck-cover-separates-trivial-words-from-normal-generators`. That node
proves (b) and the separability form of (c). It takes `T` from a central-twist
construction and uses a poison notion built from inseparable pairs.

This node differs in three ways:
- it takes `T` from a decidable simple host;
- it uses the pointwise WP-poison notion;
- it adds the regime statement (d) and the OPEN node
  `clean-ck-cover-has-solvable-word-problem`.

At landing, merge (b) into one node.

**Definition.** An element `c` of a group `Gamma` is **WP-poisoned** if every
quotient `Gamma/N` with `c ∉ N` has unsolvable word problem.

**Setting (clean marking).** Let `S` be a finitely generated infinite simple
group with solvable word problem, and `1 != s in S`.
- Let `H` be a finitely presented group containing `S`.
- Let `T` be a finitely presented group with `H <= [T,T]`.
- Let `U = Z[T]<p,q>/(p(1-g)q-1)` with `g = s`, and `Q = EL_4(U)`.
- Let `rho : Gamma ->> Q` be the finitely presented marked Steinberg cover of
  `ck-steinberg-marked-cover`, with kernel `K`.

Call the marking **clean** if `T` has solvable word problem.

**(a) Clean markings exist.** For every such `S` there are `H` and `T`, both
finitely presented with solvable word problem, with `S <= H <= [T,T]`.

**(b) Decidable image.** If the marking is clean, `Q` has solvable word problem
and `K` is a recursive set of words in the generators of `Gamma`.

**(c) Confinement.** If the marking is clean, every WP-poisoned element of
`Gamma` lies in `K`. In particular:
- `s` is not poisoned;
- no element of `S \ {1}` is poisoned;
- `Gamma` is poison-free as soon as `Gamma` has solvable word problem, and
  `Gamma` has solvable word problem iff equality to `1` is decidable for words
  that lie in `K`.

**(d) Regimes.** If the marking is clean, let `M` be a maximal proper normal
subgroup of `Gamma` in regime R2, R3 or R4 of `ck-maximal-kernel-four-regimes`,
so that `K <= M`. Then no poisoned element of `Gamma` survives in `Gamma/M`.
A maximal kernel whose simple quotient receives a poisoned element is in regime
R1. If `K` has no nonabelian simple quotient (the R1 killer), poisoned elements
constrain no maximal kernel at all.

**Consequence for the envelope hole.** The refutation of the universal reading
of `ck-envelope-has-a-finitely-normally-generated-maximal-kernel` amalgamates
a poisoned group along `s` into the input. That forces an undecidable `H`, and
so an undecidable `T`. By (c) that mechanism has no internal analogue for a
clean marking: there `s` survives in the decidable quotient `Q`. The tenable
restatement is therefore the clean one:

> for a clean marking, `Gamma` has a finitely normally generated maximal kernel.

By (d), the only word-problem obstruction left lives in the covering-kernel
regime R1.

**Not claimed.**
- That `Gamma` has solvable word problem
  (`clean-ck-cover-has-solvable-word-problem`, OPEN).
- That `Q` has a maximal normal subgroup with recursive, let alone finitely
  presented, quotient.
