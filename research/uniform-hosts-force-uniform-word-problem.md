---
rg: 2
id: uniform-hosts-force-uniform-word-problem
kind: claim
title: A decidable host for a family of finite presentations, or a uniform simple-envelope algorithm on it, solves the word problem uniformly on the family
distinct_from:
  simple-envelope-forces-solvable-word-problem: that is Kuznetsov's theorem for one finitely presented simple overgroup; this is its uniform version over a computable family, plus a second clause for a single decidable host that need not be simple or finitely presented.
  compilers-cannot-drop-the-decidability-hypothesis: that says a construction producing a finitely presented simple envelope must be fed decidable inputs; this says what it must be fed uniformly, namely data from which the word problem is uniformly decidable, and a finite presentation of a decidable group is not such data.
  no-decidable-group-contains-every-fp-rf-group: that excludes one decidable host by a complexity count against one hard input; this converts a host into a uniform decision procedure and needs no hard individual input.
  complexity-bounded-host-classes-are-not-universal: that bounds the complexity of subgroups of time-bounded hosts; this is a computability transfer from a host to a family of inputs and says nothing about time.
---

**ESTABLISHED.**  Let `e -> P_e` be a computable sequence of finite
presentations, with groups `Gamma_e`, and let `e -> w_e`, `e -> v_e` be
computable sequences of words in the generators of `P_e`.  Let
`Z = {e : w_e = 1 in Gamma_e}`.

**(H) Hosts.**  If some finitely generated group `U` with solvable word problem
contains an isomorphic copy of every `Gamma_e`, then `Z` is decidable.

**(S) Simple envelopes.**  Suppose `v_e != 1` in `Gamma_e` for every `e`.  If a
partial algorithm, on every input `e`, halts with a finite presentation `Q_e`
of a simple group `S_e` and words `phi_e(x)` for the generators `x` of `P_e`
that define an injective homomorphism `Gamma_e -> S_e`, then `Z` is decidable.

Neither clause asks the algorithm, or the host, to be told anything about
`Gamma_e` beyond `P_e`.  The embedding into `U` in (H) is not assumed to be
computable, or even to vary uniformly with `e`.

**Consequence for approaches.**  A host that depends only on the family, or
an envelope computed from presentations alone, exists only over families whose
word problem is uniformly decidable from the presentation.  The obstruction is
attached to the input data, not to the complexity of the individual groups.
`polynomial-dehn-fp-groups-have-nonuniform-word-problem` supplies a family where
each group is of low complexity and the uniform problem is the halting problem.

DERIVATION
uniform-hosts-force-uniform-word-problem-proof
