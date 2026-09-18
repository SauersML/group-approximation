---
rg: 2
id: fp-simple-envelopes-not-computable-from-presentations
kind: claim
title: No algorithm computes a finitely presented simple overgroup from a finite presentation with polynomial Dehn function, or from a polynomial-time acceptor of the word problem
distinct_from:
  boone-higman-conjecture: that asks for an overgroup of each decidable input, with no uniformity; this rules out computing the overgroup from two natural kinds of input data, and is consistent with the conjecture being true.
  compilers-cannot-drop-the-decidability-hypothesis: that says a Boone-Higman compiler needs decidable inputs; this says that even on decidable inputs, of polynomial complexity, a compiler cannot work from a presentation or from an acceptor with an unknown time constant, and must consume a total decision procedure or equivalent non-uniform data.
  no-uniform-metabelian-higman-compiler: that rules out a total effective Higman compiler preserving metabelianity; this rules out partial compilers into simple finitely presented groups that are correct on a class of decidable inputs, with no preservation property.
  np-word-problem-groups-embed-in-fp-simple-polynomial-dehn-groups: that is an open non-uniform embedding statement for NP inputs; this shows that no proof of it can be uniform in the NP acceptor.
---

**ESTABLISHED (unreviewed).**  Let a *Boone--Higman output* for a finitely
generated group `G = <X>` be a finite presentation `Q` of a simple group `S`,
together with words `phi(x)` over the generators of `Q`, one for each `x in X`,
that define an injective homomorphism `G -> S`.

1. **Presentations.**  There is no partial algorithm that halts with a
   Boone--Higman output on every finite presentation whose Dehn function is
   `≼ n^18`.  All such groups have solvable word problem.
2. **Acceptors.**  There is no partial algorithm that halts with a
   Boone--Higman output on every Turing machine `M` accepting the word problem
   of a two-generated group with time function `<= C n^2` for some `C`.  All
   such groups have word problem in P.

The same holds with "simple" replaced by "with solvable word problem" and the
output extended by a decision procedure for `S`: an effective Higman-type
compiler into decidable finitely presented overgroups is ruled out on the same
inputs.

**What this kills.**  A proof of Boone--Higman, or of its NP refinement, that
builds the envelope uniformly from a presentation, from a Dehn bound known
only up to `≼`, or from an acceptor whose time constant is not given cannot
exist.  Existing positive constructions feed a total decision procedure into
the host, as in `boone-higman-thompson-simple-envelope`, or work over classes
with uniformly decidable word problem, such as hyperbolic groups.  Both are
consistent with this.  The non-uniform finite datum that must be consumed can
be as small as a halting time.

DERIVATION
fp-simple-envelopes-not-computable-from-presentations-proof
