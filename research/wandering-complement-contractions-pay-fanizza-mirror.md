---
rg: 2
id: wandering-complement-contractions-pay-fanizza-mirror
kind: claim
title: Wandering complement contractions pay the Fanizza mirror by finite trace capacity
distinct_from:
  fanizza-full-reflection-row-has-sharp-mirror-floor: that computes the full oriented reflection-row norm from the conjugate range; this needs no row authentication and charges only the complement exit by making many decoded copies wander.
  amenable-finite-propagation-feedback-has-folner-tail-models: that dilutes fixed local relators on Folner boundaries when a positive-density safe tail exists; here the exact Hilbert-hotel model has zero complement exit, while finite trace creates the positive exit which the moving cells count.
  multiplicity-only-fanizza-row-selection-leaves-a-mirror: that installs one equal-rank mirror after a reducing block is selected; this proves an extensive wandering-coordinate incidence would exclude that mirror without fixed-label normalization.
---

Let `H<=E` and `F=E-H` be projections in a finite tracial matrix algebra,
let `U` be unitary, and put

```text
Q=UEU^*,                 A=(1-E)Q(1-E),
h=tr(H),                 b=||QH||_2.                    (WCM1)
```

Suppose there are positive contractions `A_0,...,A_(N-1)`, each unitarily
conjugate to `A`, such that for `i!=j`

```text
||A_i^(1/2) A_j^(1/2)||_2<=eta.                        (WCM2)
```

Then

```text
tr(A)<=1/N+eta,                                           (WCM3)
h<=b^2+1/N+eta.                                          (WCM4)
```

Thus the native Fanizza value `h=1/8+o(1)` is incompatible with
`b=o(1)`, `eta=o(1)`, and `N->infinity`.  This is a genuinely oriented
finite-capacity test.  The balanced finite mirror has `A=C` and
`tr(A)=h`; making its conjugates wander forces more than unit ambient trace.
The exact infinite Hilbert-hotel completion has `Q=F`, hence `A=0`, so the
test imposes no extra cost there.

This theorem does not assert that `A` is a group-algebra projection.  Its
intended use is after finite packet exactification: `A` is a decoded positive
contraction, and ordinary moving-coordinate relations must place its
conjugates in nearly orthogonal addressed Toeplitz cells.  Literalizing
`A=0` is neither assumed nor permitted.

DERIVATION
wandering-complement-capacity-proof
