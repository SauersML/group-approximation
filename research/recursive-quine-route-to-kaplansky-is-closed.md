---
rg: 2
id: recursive-quine-route-to-kaplansky-is-closed
kind: claim
title: Self-reference schedules the Kaplansky search but cannot supply the missing convolution identity
distinct_from:
  canonical-reverse-kleene-compiler-is-goal-equivalent: that classifies the canonical-profile compiler against finitely presented nonhyperlinearity, where the vacuous direction is a constant nonhyperlinear group; this is the direct-finiteness instance, where the vacuous direction is a constant one-sided inverse pair and the blocked recursion is packet-confined rather than microstate-confined.
  leavitt-unit-group-algebra-not-directly-finite: that is the open target itself, and it stays open; this closes two classes of attack on it without touching the question, so it removes routes rather than supplying one.
  subgroup-supported-one-sided-inverse-rigidity: that is the general lemma about where a support may sit; this applies it to the two recursive families this program actually built, and adds the separate observation that a fixed point cannot manufacture the pair either.
  inverse-packet-conjugator-must-mix-s-and-t-charts: that proves one conjugator must mix the charts, from residual finiteness of the pure-chart subgroups; this closes the recursive and self-referential route classes as a whole and says what a surviving compiler would have to do instead.
artifacts:
  - research/artifacts/kaplansky-cross-atlas-affine-lift-2026-09-07.md
  - research/artifacts/leavitt-packet-trace-and-compression-2026-08-24.md
---

Two independent statements, both negative, which together retire the
self-referential attack on `leavitt-unit-group-algebra-not-directly-finite`.

**Recursion confined to the built families cannot carry a counterexample.**
The elementary two-compressor core is LEF
(`leavitt-two-compressor-core-is-lef-and-marked-operator-mf`), and the
recursive kernel idempotents live in a locally finite packet tower
(`recursive-leavitt-kernel-packets-are-locally-finite`).  LEF and locally
finite groups are sofic, so their `F_2`-group algebras are directly finite by
Elek--Szabo.  By `subgroup-supported-one-sided-inverse-rigidity` a candidate
supported in either family is therefore dead before any search: no partner
drawn from anywhere in `F_2[Q]` can help it.

**A fixed point cannot manufacture the pair.**  Call a *reverse-Kleene
compiler for direct finiteness* a total computable map sending a machine index
`e` to a finite pair `(P_e, Q_e)` of subsets of `Q` which is a genuine
one-sided inverse pair whenever `e` halts.  Such a compiler exists **if and
only if** a counterexample already exists.  So the diagonal argument that
works elsewhere in this repository has nothing to bite on here: self-reference
is a scheduler, not an algebraic amplifier.

The usable output is a constraint on what is left.  A surviving compiler must
force a collision that genuinely crosses the two atlas charts — it may not
close its tail inside one recursive packet family, and it may not obtain the
identity coefficient by a fixed point.  That is the same conclusion
`inverse-packet-conjugator-must-mix-s-and-t-charts` reaches for one
conjugator, arrived at from the compiler side, and it is why
`leavitt-cross-atlas-eleven-term-s0-lift` anchors its support on generators of
the whole group rather than on a recursive family.
