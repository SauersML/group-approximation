---
rg: 2
id: inside-corner-hecke-tests-miss-the-asynchronous-mirror-exit
kind: claim
title: Every inside-corner Hecke test misses the finite mirror exit of an asynchronous prefix return
distinct_from:
  toeplitz-range-commutator-has-a-balanced-mirror-exit: that constructs the four joint reflection characters for one range commutator; this proves blindness for an arbitrary finite coefficient algebra supported in the marked source, including mixed D8 and Hecke incidence tests.
  context-local-fanizza-exits-do-not-control-global-leakage: that separates private context exits by Bass--Serre reduced words; this gives the explicit one-unitary asynchronous prefix counterpacket after all inside-corner packets have been frozen.
  two-qubit-pauli-automorphic-cell-has-collapse-or-stationary-flow: that treats automorphic finite packet graphs; this treats the first non-automorphic coarse-to-proper-prefix conjugator and identifies its equal-rank complement escape.
  full-label-chord-normalization-kills-the-hilbert-hotel: that shows full label normalization destroys infinite completeness; this proves why tests restricted to the source corner cannot remove the mirror before that overcorrection.
---

Let `A<=M_d(C)` be any finite-dimensional unital star algebra with unit a
projection `E`.  Let `F,H in A' intersect E M_d(C) E` be orthogonal
projections with

```text
E=F+H,                    tr(H)>0.                     (ICH1)
```

Assume the ambient complement contains a projection `C<=1-E` with
`rank(C)=rank(H)`.  Choose a unitary `T` which fixes `FH`, swaps `HH` with
`CH`, and is arbitrary on the remaining complement.  Put

```text
Q=TET^*=F+C,             X=FTE.                        (ICH2)
```

Then the asynchronous prefix return has the full guarded source defect

```text
X=F,                     X^*X=F,
||X^*X-E||_2^2=tr(H).                                  (ICH3)
```

Nevertheless every inside-corner coefficient sees exactly the intended
proper range `F`.  For all `a,b in A`,

```text
aQb=aFb,                 a(Q-F)=0=(Q-F)b.             (ICH4)
```

Consequently every fixed trace polynomial or normalized-HS test assembled
from coefficients in `A` and occurrences of `Q` sandwiched between those
coefficients has exactly the same value at `Q=F+C` as at the proper infinite
model `Q=F`.  This includes:

- arbitrary finite D8, Pauli, selector, and Hecke packet refinements inside
  `E`;
- every prescribed intersection `aQb` and every inside-corner Reynolds or
  conditional-expectation moment;
- commutators of `Q` with the inside packet; and
- all context-local predicate rows whose decoded coefficients lie in `A`.

All these tests may therefore have zero defect while `(ICH3)` retains any
fixed rational forbidden mass allowed by the complement capacity.

The exact infinite model has the opposite completion.  After countable
stabilization, choose a unitary carrying `EH` onto the proper infinite
subspace `FH`; then `TET^*=F` and `X^*X=E`.  Thus the same finite list of
inside-corner identities has exact perfect completeness.  The finite mirror
is not a failure of the intended prefix incidence; it is the finite trace's
equal-rank completion of that incidence.

This kills the most direct finite D8/Hecke coupling to one asynchronous
prefix word.  To exclude the counterpacket, a new row must see

```text
C=(1-E)Q=(1-E)TET^*,                                  (ICH5)
```

or an equivalent oriented complement block.  But an exact universal demand
`C=0` together with `Q=TET^*` makes `Q<=E` in the regular factor; equal trace
then gives `Q=E` and kills `H`.  Therefore the required control of `(ICH5)`
must itself be finite-matrix-only.  Inside-corner BCS/Hecke enrichment is not
a smaller source-Gram decoder.
