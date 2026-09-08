---
rg: 2
id: finite-injective-conservative-binary-automata-are-surjective
kind: claim
title: A binary particle-conserving cellular automaton injective on finite configurations is surjective over every group
distinct_from:
  local-decoders-bound-connected-missing-particle-witnesses: that bounds a missing cluster using a supplied decoder but does not provide its lift; this uses finite cluster matchings and a stably finite collision-operator algebra to attain every particle sector without assuming a decoder.
artifacts:
  - research/artifacts/conservative-syndrome-update-audit-2026-09-07.md
  - research/artifacts/conservative-ca-literature-and-trace-scope-2026-09-07.md
---

Let G be any group and let tau:{0,1}^G->{0,1}^G be a cellular
automaton fixing the all-zero configuration. Assume:

1. For every finitely supported x, tau(x) has the same number of ones
   as x.
2. If x,y are finitely supported and tau(x)=tau(y), then x=y.

Then tau maps each finite n-particle sector bijectively onto itself,
for every n>=0. Consequently tau is surjective on the entire full shift.

In particular, every globally injective binary particle-conserving CA is
surjective over every group. The main hypothesis is weaker than global
injectivity; the conclusion does not assert global injectivity from
injectivity on finite configurations alone.

For each fixed n, locality decomposes an input into finitely many possible
types of interacting particle clusters, up to translation. Conservation
gives a bounded-displacement perfect matching from each cluster to its
output. Finite-configuration injectivity permits the matching to respect
its finite stabilizer. Choosing matchings for the finitely many cluster
types lifts tau to an injective map on ordered n-tuples, whose choices
use only finitely many relative-coordinate equality predicates.

The lift is a partial permutation in the finite-collision operator algebra.
Its explicit transpose is an algebraic left inverse. Stable finiteness of
that algebra makes the lift surjective, and hence attains every unordered
n-particle configuration. No general implication from injectivity to an
algebraic inverse is assumed, and no nonlinear decoder is used.

The result concerns binary particle-conserving rules. It does not resolve
Gottschalk's conjecture for arbitrary nonlinear cellular automata, nor
Kaplansky's conjecture over positive-characteristic group algebras.
