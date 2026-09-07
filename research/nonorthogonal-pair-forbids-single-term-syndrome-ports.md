---
rg: 2
id: nonorthogonal-pair-forbids-single-term-syndrome-ports
kind: claim
title: Nonorthogonal qubit projectors prohibit exact flags charged only to their individual terms
artifacts:
  - research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md
distinct_from:
  local-syndrome-port-domination-at-each-gadget: that allows neighboring sums in a proposed amplifier; this obstructs singleton neighborhoods for an explicit two-projector instance and does not refute the larger-neighborhood construction.
  qubit-pairs-have-half-gap-and-unbounded-rounder-cost: that proves a growing lower bound on unrestricted total cost; this rules out exactification with individual-term domination at any finite constants, using the kernels of the marginal flag effects.
---

For the pair `P,Q_N` of `qubit-pairs-have-half-gap-and-unbounded-rounder-cost`
with `N > 1`, no exactifying instrument has marginal fault effects
`F_P <= c_P P` and `F_Q <= c_Q Q_N` for finite nonnegative constants.
This holds on any finite-dimensional spectator extension as well.

It applies to `F_a = W^* B_a W` from commuting dilated syndrome projectors,
because these are positive contractions. It does not prohibit charging a
flag to a sum of neighboring terms. Sections 3 and 4 of the artifact give
the full proof and the necessary covering inequality for arbitrary
incompatible sets of constraints.
