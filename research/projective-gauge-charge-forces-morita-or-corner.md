---
rg: 2
id: projective-gauge-charge-forces-morita-or-corner
kind: claim
title: Projective gauge charge forces either Morita matrix units or a proper corner
distinct_from:
  projective-atlas-cannot-orient-transverse-branch-phase: that exhibits the concrete W to iW symmetry of the Atlas ledger; this proves the general algebraic gauge-grading statement and classifies charged escapes.
  two-chart-square-lift-recreates-schur-m2: that computes one two-chart HNN realization; this applies to every algebraic same-carrier projective observable and every full equal-carrier charged intertwiner.
  universal-atlas-ideal-cannot-force-hall-deficit: that rules out a universal rectangular isometry by finite-factor trace monotonicity; this identifies a proper rectangular corner as the only non-Morita charged carrier.
---

# Projective gauge charge forces either Morita matrix units or a proper corner

ESTABLISHED. Let `W` be a unitary representative of a projective holonomy
`[W]`, and grade algebraic expressions in `W,W^*` by

```text
charge(W)=1,       charge(W^*)=-1.                       (GCF1)
```

If an algebraic same-carrier observable `F(W)` is functorially defined by
`[W]`, then

```text
F(lambda W)=F(W)       for every lambda in U(1).         (GCF2)
```

Write the finite Laurent/star-polynomial expression as its gauge Fourier sum
`F=sum_k F_k`, where `F_k(lambda W)=lambda^k F_k(W)`. Fourier projection in
`lambda` shows that `(GCF2)` kills every `F_k` with `k != 0`. The same applies
to matrix-valued contractions of finite tensor diagrams: every surviving
diagram has total incoming and outgoing `W`-charge zero. Thus traces,
spectral projections, Gram operators, adjoint actions, rectangle products,
and arbitrary algebraic combinations of them remain phase-blind. An odd or
otherwise nonzero-charge observable cannot be manufactured functorially from
`[W]` on the same carrier.

A charged observable requires extra lift data. Suppose it is supplied by a
unitary group word `t` intertwining two carrier projections `p_0,p_1`, with

```text
t p_0 t^*=p_1.                                           (GCF3)
```

Then `v=p_1tp_0` satisfies

```text
v^*v=p_0,       vv^*=p_1.                                (GCF4)
```

If `p_0,p_1` are the two full equal-positive-multiplicity Schur carriers,
`p_0,p_1,v,v^*` are matrix units. The charged lift therefore generates the
full `M_2` joining them. It cannot orient the factor-two Schur surplus because
it has already Morita-recombined that surplus into one spin block. This is
independent of the order of `t`, the degree of the later charged polynomial,
or the finite packet used to label the two sectors.

Consequently the equal-full-carrier algebraic raw-lift gate is closed. There
are only three genuine exceptions to the argument.

1. **Unequal or proper corners.** One may have `v^*v=p_0` but
   `vv^*=r<p_1`. Then matrix units cover only `p_0+r`, leaving the complement
   `p_1-r`; this is exactly a one-sided trace-payment carrier rather than a
   Morita equivalence.
2. **A one-sided compressed group word.** A global unitary word may have a
   compression `p_1tp_0` with the desired initial support and proper final
   support without conjugating the whole carrier. The support/containment
   assertion is extra corner algebra, not a consequence of projective
   holonomy.
3. **An external central-extension line.** A chosen charged line can lift the
   projective frame without an equal companion sector. If that line has
   vanishing normalized canonical mass, however, its relations cannot orient
   a positive-density HS ledger. A positive-mass central lift is additional
   structure and is not functorially recoverable from `[W]`.

In a finite tracial algebra, the first two exceptions are necessarily the
same rank mechanism: `tau(v^*v)=tau(vv^*)`, so a proper range can occur only
inside a strictly larger target carrier. In a properly infinite completeness
model the corresponding one-sided equivalence may exist. Hence the sole
amplification-stable survivor is a genuinely one-sided charged section into
a proper larger corner, with finite-matrix trace cyclicity paying for the
missing complement. Constructing that compressed section by ordinary group
words is the new incidence gate.
