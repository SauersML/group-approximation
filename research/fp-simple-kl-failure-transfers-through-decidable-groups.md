---
rg: 2
id: fp-simple-kl-failure-transfers-through-decidable-groups
kind: claim
title: A Kervaire--Laudenbach failure over a finitely presented simple group is a failure over a decidable group, and conversely through simple envelopes
distinct_from:
  kl-counterexample-can-be-finitely-presented: that shrinks a counterexample to finitely presented data with no control of the word problem or of simplicity; this relates finitely presented SIMPLE counterexamples to counterexamples with solvable word problem.
  kl-counterexample-can-be-two-generator-simple: that places a counterexample in a two-generator simple group through Schupp's embedding, which gives no finite presentation; this asks for a finitely presented simple envelope and records what that costs.
  boone-higman-conjecture: that is the embedding conjecture itself; this only records how its truth for one counterexample transfers the failure to a finitely presented simple group.
---

Let `D` be a nonempty set of nonzero degrees and let
"failure over `G`" mean: some `w in G * <t>` with `deg_t(w) in D` has a
non-injective coefficient map.

1. **Down.**  If failure occurs over a finitely presented simple group `S`,
   then failure occurs over a finitely generated group with solvable word
   problem.  The group is `S` itself, whose word problem is solvable by
   Kuznetsov's argument.
2. **Up.**  If failure occurs over a finitely generated group `P` and `P`
   embeds in a finitely presented simple group `S`, then failure occurs over
   `S`.
3. **Consequence.**  If `boone-higman-conjecture` holds, failure over some
   finitely presented simple group is equivalent to failure over some finitely
   generated group with solvable word problem.

A finitely presented simple counterexample would be a finitely presented
simple group that is neither hyperlinear nor MF
(`kervaire-laudenbach-holds-for-hyperlinear`, `kervaire-laudenbach-holds-for-mf`).

## The gap this names

Nothing on main produces a counterexample with solvable word problem from an
arbitrary counterexample.  The finitely presented reduction keeps the
collapse certificate but not decidability: a template `(P, w, alpha)` with
`alpha != 1` in `P` gives a counterexample over `P`, and `P` need not have
solvable word problem.  Recorded as the OPEN claim
`kl-counterexample-can-have-solvable-word-problem`, which together with
`boone-higman-conjecture` gives `kl-counterexample-can-be-finitely-presented-simple`.

Proved in `fp-simple-kl-failure-transfer-proof`.
