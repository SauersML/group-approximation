# Native-signal Kleene diagonal for the Fanizza family

**Date:** 2026-08-20

## Correction of orientation

The existing Boone-oriented route asks for a word which survives on the
nonhalting side and then tries to inject its separated mass into the Fanizza
signal.  This clashes with the source theorem: for `L=HALT`, the Fanizza
signal vanishes in every perfect strategy on the nonhalting side.

That vanishing is useful under the opposite recursion-theorem diagonal.
Retain the native signal involution `x_D` as the marked group word.  On the
halting side, the source tracial state has `tau((1-x_D)/2)>0`, so its GNS
representation makes `x_D` nonidentity.  On the nonhalting side,

```text
||X_D-I||_2^2=4phi((1-X_D)/2)<=4C_m epsilon.
```

After a quantitative group-to-strategy decoder, the marked group word is
therefore close to the identity in every accurate matrix tuple.

## Reverse Kleene diagonal

The fixed-point machine enumerates a van Kampen proof that its own marked word
is trivial.  If the enumeration halted, halting-side completeness would say
that the same word is nontrivial, a contradiction.  Hence the machine does
not halt; completeness of proof enumeration makes the word nontrivial, while
nonhalting-side soundness collapses it in every matrix microstate.  Canonical
trace separation then contradicts hyperlinearity.

This diagonal permits computable constants depending on the machine index.
After the fixed point is chosen, only one positive defect threshold is used.
The earlier demand for constants uniform across all machines and all possible
runtimes belongs to the opposite microstate-search diagonal and is not needed
here.

## Remaining construction

The new frontier claim `fanizza-native-signal-groupification` asks only for:

1. exact extension of BCS representations while retaining `x_D`; and
2. a finite-dimensional group-to-near-perfect-strategy decoder with a
   computable modulus for each finite `B_m`.

The S3 radical packet lane supplies every local ingredient except renewal of
the selector chart on a fresh context.  Thus
`s3-radical-chart-returns-to-fresh-context` is now a direct one-hole path to
the explicit nonhyperlinear-group goal, with neither a Boone carrier nor a
runtime-uniform tape estimate.
