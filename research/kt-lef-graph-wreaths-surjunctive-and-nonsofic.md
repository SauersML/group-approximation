---
rg: 2
id: kt-lef-graph-wreaths-surjunctive-and-nonsofic
kind: claim
title: Every Kun--Thom graph wreath with a nontrivial countable LEF lamp is surjunctive and nonsofic
distinct_from:
  kun-thom-nonsofic-wreaths-are-surjunctive: that concerns binary lamps with complete commutation; this covers every invariant commutation graph and every nontrivial countable LEF lamp, with nonsoficity proved directly for the entire class.
  marked-graph-action-not-residually-finite: that excludes one approximation hypothesis for the underlying graph action; this determines two group properties of the corresponding untwisted graph wreaths without using that hypothesis.
artifacts:
  - research/artifacts/lef-graph-wreath-surjunctivity-2026-09-12.md
---

Let `Gamma < G` be any explicit Kun--Thom Theorem E pair, let
`X = G/Gamma`, let `Lambda` be any `G`-invariant simplicial graph on `X`,
and let `A` be a nontrivial countable LEF group. Then

```text
W_Lambda = Lambda(A) semidirect G
```

is surjunctive and not sofic. If `A` is finitely generated, `W_Lambda` is
finitely generated. In particular every binary partially commutative
interpolation, from free lamps to commuting lamps, is a finitely generated
surjunctive nonsofic group.

Surjunctivity follows from residual finiteness of the actor and
`lef-lamp-graph-wreaths-are-surjunctive`. For nonsoficity choose `a != 1` in
`A`, a strict compressor `t`, and `gamma in Gamma` outside `t Gamma t^-1`.
The root lamp `a_Gamma` centralizes `Gamma`, but

```text
[t a_Gamma t^-1, gamma]
    = a_(t Gamma) (a^-1)_(gamma t Gamma) != 1.
```

Projection onto the vertex group at `t Gamma` detects this word as `a`.
Thus it is nontrivial for every graph, independent of whether the two
vertices are adjacent. This contradicts
`sofic-groups-kill-rigid-compression-defects` in any sofic ambient group.

The argument does not infer nonsoficity from a nonsofic quotient. It gives
no hyperlinearity or operator-MF conclusion and does not settle Gottschalk
surjunctivity outside this class.
