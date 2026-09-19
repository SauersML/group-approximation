---
rg: 2
id: atlas-six-relator-relative-small-cancellation-audit
kind: claim
title: Five-syllable mirror pieces block every metric small-cancellation residual-finiteness theorem for the six-relator quotient
artifacts:
  - experiments/atlas_six_relator_relative_pieces.py
  - experiments/atlas-six-relator-relative-pieces.json
distinct_from:
  atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test: that says a suitable finite quotient is exactly a finite phase countermodel; this tests whether standard free-product small-cancellation proves such a quotient exists.
  atlas-six-relator-quotient-identifies-h-bridge: that asks the six relators to kill the bridge and is refuted; this asks whether residual finiteness separates the surviving bridge in a finite quotient.
  atlas-five-row-blowup-branch-is-impossible: that reduces the five-row inequality to macroscopic matrix-ultraproduct exclusion; this audits the opposite exact finite-quotient side.
---

Let

```text
Gamma_6=(A8_1*A8_2)/<<s_0,s_11,s_30,s_44,s_55,c_19243>>.
```

Extract the literal transported words from the certified Atlas packet and
use free-product syllable length.  Their cyclically reduced lengths are

```text
             s_0  s_11  s_30  s_44  s_55  c_19243
length         6     8     8     8     8        16.   (RSC1)
```

The symmetrized family has `92` distinct cyclic words.  Its maximum common
initial piece has length `5` inside a length-eight relator, so the maximum
piece ratio is exactly

```text
5/8.                                                       (RSC2)
```

There are eight maximum witnesses.  They come from a positive cyclic shift
of one of `s_11,s_30,s_44,s_55` and a cyclic shift of its inverse.  For
example, writing the exact factor-two and factor-one syllables of `s_11` as
`A,B,C,B,A,B,C,D`, the positive word and the indicated inverse shift have
the common five-syllable prefix

```text
A B C B A.                                                (RSC3)
```

Consequently the literal relative presentation fails both

```text
C'(1/6)  and  C'(1/4),                                   (RSC4)
```

indeed it fails strict `C'(lambda)` for every `lambda<=5/8`.  In particular
the `C'(1/6)` free-product cubulation and residual-finiteness theorems do not
apply, nor does the classical `C'(1/4)-T(4)` route.

The failure is not caused by proper powers: none of the six cyclic words has
a nontrivial linear period.  Under the ordinary cyclic-syllable definition
of a piece, none of the six relators can be written entirely as a product of
pieces (the exact dynamic-programming output is `null` for every minimum
piece count).  Thus the nonmetric `C(6)` condition holds vacuously in that
convention.  This does **not** imply residual finiteness or virtual
specialness: residual finiteness is the special conclusion known for the
metric `C'(1/6)` free-product condition, while finitely presented groups
satisfying weaker nonmetric small-cancellation conditions need not be
residually finite.  Hence the exact `C(6)` observation supplies no finite
bridge quotient.

## Exact audit method

`experiments/atlas_six_relator_relative_pieces.py` reconstructs the five
boundary words and `c_19243` from the stored certified words, performs exact
free-product cyclic reduction, closes under inversion and cyclic rotation,
and compares every pair of distinct symmetrized words.  Syllables are exact
`4x4` matrices over `F_2`; equality and inversion use only bit arithmetic.
The complete words and all eight maximum-piece witnesses are frozen in
`experiments/atlas-six-relator-relative-pieces.json`.

## Consequence for the Atlas route

Both marked `A8` factors and a nontrivial `H=GL_3(2)` bridge survive in
`Gamma_6`, because their images survive in its Leavitt quotient.  Therefore,
if `Gamma_6` were residually finite, finitely many finite quotients could be
combined into one finite quotient which injects both finite `A8` factors and
retains that bridge.  By
`atlas-six-relator-exact-phase-escape-is-a-finite-quotient-test`, its regular
representation would be an exact countermodel to
`atlas-five-row-operator-phase-lift`.

The explicit relators therefore leave the exact side undecided:

* no suitable finite quotient was produced by this audit;
* the standard metric small-cancellation proof of residual finiteness is
  blocked exactly by the five-syllable mirror pieces `(RSC3)`;
* the weaker `C(6)` label does not provide residual finiteness.

The appropriate next exact question is a bespoke profinite-separability or
special-cubulation theorem which uses more than the classical piece ratios.

## Literature boundary

Einstein--Ng, *Relative Cubulation of Small Cancellation Free Products*
(arXiv:2111.03008), prove residual finiteness for `C'(1/6)` small-cancellation
free products of residually finite groups.  Martin--Steenbock,
*A combination theorem for cubulation in small cancellation theory over
free products* (arXiv:1409.3678), use the same metric `C'(1/6)` hypothesis.
The present exact ratio `(RSC2)` is outside both theorems.  General nonmetric
`C(6)` controls diagrams and algorithmic properties but is not a residual-
finiteness theorem; known finitely presented non-residually-finite small-
cancellation examples prevent that inference.
