---
rg: 2
id: finite-injective-charge-noncreation-forces-surjectivity
kind: claim
title: A finite-injective cellular automaton cannot strictly destroy positive charge and is surjective
distinct_from:
  finite-injective-conservative-binary-automata-are-surjective: that assumes exact binary particle conservation; this permits arbitrary finite alphabets, positive real charges, and a nonincrease inequality instead of conservation.
  finite-injective-positive-charge-automata-are-surjective: that assumes equality of total charge; this derives that equality and surjectivity from nonincrease, by filling successively larger charge levels.
artifacts:
  - research/artifacts/conservative-ca-literature-and-trace-scope-2026-09-07.md
---

Let A be a finite alphabet with a distinguished quiescent symbol 0,
let G be any group, and let tau:A^G->A^G be a cellular automaton
fixing 0^G. Give each nonzero symbol a strictly positive real charge
w(a), and put w(0)=0. For a finitely supported configuration x write

    W(x)=sum_(g in G) w(x(g)).

Suppose tau is injective on finitely supported configurations and

    W(tau(x)) <= W(x)              for every finite x.

Then equality holds for every finite x. Moreover, tau is bijective
on each finite-configuration charge sector, and is surjective on A^G.
Global injectivity is not assumed or deduced from the finite version.

Thus a globally injective strict full-shift encoder with a quiescent
state must increase every chosen positive charge on SOME finite
configuration. It cannot implement its strict embedding solely by
preserving or destroying a positive amount of stored material.

The unique zero-charge symbol matters. If several symbols have zero
charge, their full shift can carry arbitrary computation that this
charge does not control. The theorem does not cover such degenerate
charges or arbitrary automata without a charge-nonincrease hypothesis.
