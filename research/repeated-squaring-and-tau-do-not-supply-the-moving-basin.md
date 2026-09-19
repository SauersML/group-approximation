---
rg: 2
id: repeated-squaring-and-tau-do-not-supply-the-moving-basin
kind: claim
title: Short repeated-squaring rows and property tau do not supply a presentation-stability basin
distinct_from:
  bounded-cycle-level-has-only-polylogarithmic-error: that determines the accuracy which the moving Iwahori target must accept; this proves that shortening the large power row and citing Cayley expansion cannot establish such acceptance.
  regular-congruence-endpoint-orbit-has-uniform-selberg-retraction: that correctly applies Selberg averaging after two exact congruence representations are authenticated; this explains why the same argument cannot authenticate them from presentation defects.
  fixed-level-bs14-compatible-basin: that asks for the actual moving repair theorem; this rules out two generic quantitative substitutes without asserting that the theorem is false.
---

There is no lower bound on normalized-HS presentation stability in terms of
only

1. a uniform spectral gap for the finite endpoint groups, and
2. the number and bounded length of relators after repeated-squaring
   compression.

Explicitly, for every `L>=1` the presentation

```text
P_L=<a_0,...,a_L |
        a_i=a_(i+1)^2 (0<=i<L), a_L=1>               (RST1)
```

presents the trivial group and every relator has length at most three.  Yet
the scalar unitary tuple

```text
A_i=exp(i pi/2^i)                                    (RST2)
```

satisfies every squaring row exactly, has terminal-row defect

```text
|A_L-1|<=pi/2^L,                                     (RST3)
```

and keeps

```text
|A_0-1|=2.                                           (RST4)
```

Thus even the trivial endpoint group--whose averaging operator has the
largest possible gap--can have an exponentially small marked presentation
basin when a power consequence is encoded by a short directed squaring
circuit.  Taking the direct product of `(RST1)` with any fixed expander
quotient family leaves the endpoint groups' original Cayley spectral gap
unchanged and preserves the same bad scalar sector.

For the Iwahori staircase, replacing the word `s^N=1` by `O(log N)`
auxiliary repeated-squaring rows therefore cannot turn a power-law-in-`N`
certificate into a polylogarithmic basin.  The compressed syntax may instead
carry an `O(1/N)` condition number, already far below the required
`(log N)^(-1/4)` scale.

Property `(tau)` remains decisive **after authentication**.  For exact
representations `rho,eta`, the left-right action

```text
beta(g)T=rho(g)T eta(g)^*
```

is a genuine unitary representation, so spectral averaging projects onto
its invariant vectors.  Before exactification, the analogous maps are only
approximately multiplicative; a Cayley-graph gap does not make their
averaging operator an approximate projection with controlled holonomy.
That missing estimate is two-dimensional presentation/filling control.
Neither a short circuit for `s^N` nor property `(tau)` supplies it.

This is a proof-method firewall, not a counterexample to the special
Iwahori moving-basin statement.  A positive proof must exploit the exact BS
core and its two correlated cubic rows, prove a genuine uniform
presentation-to-congruence authentication theorem, or supply an independent
2-dimensional filling/cocycle-expansion estimate.
