---
rg: 2
id: regular-mixing-forces-diagonal-retention-decay
kind: claim
title: Regular mixing repairs the scalar kernel only by destroying tensor self-retention
distinct_from:
  non-ce-trace-does-not-promote-to-subgroup-character-gap: that uses regular mixing to show that the abstract scalar kernel does not retain a selected canonical sector; this proves quantitative decay of every diagonal tensor fusion weight
  irs-intersection-fixed-weight-retention-collapses: that rules out retaining the IRS law as a literal measure component; this also rules out genuinely operator-algebraic retained summands after regular mixing
---

Let `G` be a hyperlinear group, let `theta` be a non-Connes-embeddable
character of `G`, and fix `0<epsilon<1`.  Put

```text
tau_epsilon=(1-epsilon) delta_G + epsilon theta.        (RMD1)
```

Then:

1. `tau_epsilon` is non-CE;
2. its scalar kernel is exactly `{e}`; and
3. its diagonal fusion coefficients satisfy

```text
d_n(tau_epsilon) -> 0.                                  (RMD2)
```

The first assertion follows because `epsilon theta<=tau_epsilon`; if
`tau_epsilon` were CE, positive-functional Radon--Nikodym domination would
make `theta` CE.  For `g!=e`,

```text
|tau_epsilon(g)|=epsilon |theta(g)| <= epsilon<1,
```

so the scalar kernel is trivial and `tau_epsilon^n->delta_G` pointwise.
Since hyperlinearity of `G` means `L(G)` is CE,
`diagonal-retention-fusion-coefficient` gives `(RMD2)`.

This simultaneously rules out the natural scalar-kernel repair for all
three standard non-CE character sources currently in Cairn:

- the non-co-hyperlinear IRS character on a free group;
- the fixed non-CE BCS character on its explicit sofic RACG host; and
- the CDI non-CE character on a residually finite property-`(T)` lattice.

Each host is hyperlinear.  Mixing with its regular character makes the
polarization quotient completely explicit, but every positive retained
weight necessarily vanishes.  Without regular mixing, a uniform retained
weight can occur only if the original scalar-kernel quotient is already
non-hyperlinear.  Hence diagonal fusion is a certificate of canonical-trace
promotion, not an independent promotion compiler for these examples.
