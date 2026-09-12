---
rg: 2
id: opposite-transvections-are-free-but-finite-lamp-windows-close
kind: claim
title: Opposite positive transvections form a free compression monoid, but every bounded cone-lamp window has a finite model
distinct_from:
  amenable-multi-compressors-have-a-joint-hs-telescope: That gives vanishing-boundary models for the amenable Heisenberg pair; this identifies the smallest nonamenable positive pair, proves its uniform boundary expansion, and shows why that expansion still does not give a fixed HS witness.
  coordinate-action-not-sofic: That excludes finite charts for the full Kun--Thom coset action; this gives finite exact models only for bounded positive-cone lamp windows and identifies the missing Gamma-moved-site correlations.
  kt-wreath-relative-canonical-actor-exactification: That asks for actor exactification from every canonical full-wreath microstate; this isolates the precise uniform-in-depth lamp estimate which free-monoid expansion would need but finite presentation does not provide automatically.
---

**ESTABLISHED NONAMENABLE-PAIR AUDIT.**  In the `SL_d(Z)` actor of the
explicit Kun--Thom pair (`d>=3`), put

```text
A=u_12=I+e_12,                 B=u_21=I+e_21.          (OTF1)
```

Both matrices have nonnegative entries and hence are positive compressors.
They generate a free **positive monoid**.  Indeed, on the projective half-line
`(0,infinity)`, the upper-left `2x2` blocks act by

```text
A:x |-> x+1       with image (1,infinity),
B:x |-> x/(x+1)   with image (0,1).                    (OTF2)
```

The two images are disjoint, and the standard ping-pong decoding removes the
first letter of a positive word.  Thus distinct words in `{A,B}^+` give
distinct matrices.  No one-generator semigroup is nonamenable, so `(OTF1)`
is a smallest-cardinality positive nonamenable compressor family.

Its right boundary has a uniform expansion estimate.  For every nonempty
finite set `F` of positive words, the sets `FA` and `FB` are disjoint and
both have size `|F|`.  Therefore

```text
|(FA union FB)\F|>=|F|,
sum_(S in {A,B}) |FS triangle F| >= 2|F|.              (OTF3)
```

In particular the Følner telescope of
`amenable-multi-compressors-have-a-joint-hs-telescope` cannot be extended to
this pair.

## What the boundary would pay

Suppose a block telescope indexed by `F` has the following **uniform lamp
decoder**: whenever a proposed block permutation for `S in {A,B}` does not
send the `pS` coefficient block to the `p` block, one member of a fixed test
menu has squared normalized-HS mismatch at least `kappa>0` on that entire
block.  Orthogonality of the block decomposition and `(OTF3)` then give

```text
sum_(S in {A,B}) E_S >= kappa,                          (OTF4)
```

up to the harmless convention factor in the definition of `E_S`.  Thus a
uniformly decoded canonical lamp at every boundary word would be sufficient
to destroy the joint telescope.

The quantifier “uniformly” is load bearing.  Canonical group microstates say
that for each **fixed** pair of distinct lamp words their distance tends to
`sqrt(2)`.  They do not give one finite menu which distinguishes all boundary
words in a model-dependent set `F_n` whose depths tend to infinity.  The
boundary can drift beyond every fixed test radius.

## Exact finite models of every bounded positive window

This is not merely a logical possibility.  Fix a radius `R`.  There are only
finitely many positive matrices represented by words of length at most `R`.
Residual finiteness of `SL_d(Z)` gives a finite quotient `q_R` which is
injective on that set.  In the finite Bernoulli wreath

```text
(direct_sum_(q_R(<A,B>)) C_2) rtimes q_R(<A,B>),       (OTF5)
```

use the regular actor action and the coordinate lamps.  All positive words
of length at most `R` address distinct coordinates.  Hence every actor
relation, every covariance relation among those coordinates, and every
Bernoulli mixed moment in that bounded window is exact.  In particular,
distinct lamps there have squared `2`-distance `2`, just as in the canonical
infinite model.

One may tensor `(OTF5)` with any finite actor quotient needed to separate a
fixed list of actor words; this preserves the cone-lamp table.  What it does
not preserve is the decisive Kun--Thom stabilizer geometry.  In finite
quotients the image of `Gamma` is normal, so a lamp at `A Gamma` is identified
with its `gamma`-translate for `gamma in Gamma`.  The full canonical wreath
instead requires those lamps to be distinct for
`gamma notin A Gamma A^(-1)`.  Those Gamma-moved-site correlations, not the
free positive cone itself, are exactly where the finite model fails.

Consequently nonamenability of a finite compressor family and the expansion
bound `(OTF3)` do not by themselves imply `KRE2` or a normalized-HS floor.
The sufficient estimate `(OTF4)` requires a depth-uniform decoder tying the
expanding cone boundary to the canonical `Gamma`-stabilizer lamp geometry.
Constructing that decoder without reconstructing a normalized lamp algebra
is the remaining multi-compressor seam.  Bounded canonical lamp windows have
the exact countermodels `(OTF5)`.

DERIVATION
opposite-transvection-ping-pong-and-finite-window-proof
