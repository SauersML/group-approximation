---
rg: 2
id: three-coset-frame-saturation-is-not-pair-functorial
kind: claim
title: Three-coset saturation does not preserve a transported Iwahori pair
distinct_from:
  iwahori-fractional-transport-integralization: that asks for a positive simultaneous rounding theorem over arbitrary types; this gives an exact level-two packet showing that separately saturating the two polar supports cannot be that theorem.
  same-side-modular-extensions-do-not-integralize-edge-transport: that uses a continuous Hadamard family after omitting the opposite Nielsen twist; this uses the actual two opposite mod-two Iwahori maps and defeats the natural three-coset core and frame constructions.
  bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair: that repairs this fixed packet by changing a defect-paid whole vertex block; this proves only that separate support saturation cannot produce the paired block automatically.
---

Let `G=PSL_2(F_2)=S_3`.  Reduce the two opposite Iwahori embeddings modulo
two and identify the lower subgroup with the upper one as in the Nielsen
coordinates `Bbar=<u,e|e^2=1>`.  Their quotient characters are

```text
chi_+(u)=chi_+(e)=1,
chi_-(u)=0,             chi_-(e)=1                    (TCF1)
```

in `C_2`: the second formula follows from
`alpha(u)=u^(-1)e`, `alpha(e)=u^(-1)e u`.

There are exact modular vertex packets and an exact common edge partial
intertwiner for which both natural index-three saturations destroy the
transported pair.  Namely take the standard two-dimensional representation
on the plus vertex and `1 direct_sum sgn` on the minus vertex.  Their pulled
edge restrictions are

```text
1 direct_sum chi_+,                1 direct_sum chi_-. (TCF2)
```

The common trivial line projection `p` is therefore an exact transported
edge projection.  On the plus packet its three-coset conditional expectation
is

```text
E_+(p)=(1/3)sum_(r in G/B) pi_+(r)p pi_+(r)^*=I_2/2,  (TCF3)
```

by irreducibility and trace preservation.  On the minus packet the same
line is the trivial `G`-summand, so

```text
E_-(p)=p.                                             (TCF4)
```

Consequently no nonconstant projection-valued spectral threshold applied
separately to `(TCF3)` and `(TCF4)` yields transported projections: the plus
output is `0` or `I_2`, while the minus output is `p`.  The literal core
intersection fails in the same way:

```text
meet_(r in G/B) pi_+(r)p pi_+(r)^*=0,
meet_(r in G/B) pi_-(r)p pi_-(r)^*=p.                 (TCF5)
```

This is already the actual opposite-Iwahori mod-two diagram, not an abstract
index-three counterexample.

Amplifying both vertices by `n` trivial summands makes the edge defect
`2/sqrt(n+2)` while the polar support misses only the one incompatible line.
Equations `(TCF3)--(TCF5)` persist on the final two-dimensional packet.
Thus the obstruction survives arbitrarily accurate normalized-HS input.
It does **not** refute repair: replacing that defect-paid packet costs
`O(1/sqrt n)`, exactly as the fixed finite-diagram theorem predicts.  What
it rules out is the proposed analytic shortcut in which one independently
cores or spectrally saturates the two large edge supports and expects their
transport relation to survive.  A successful depth-uniform argument must
round the two vertex multiplicity/extension choices jointly.

