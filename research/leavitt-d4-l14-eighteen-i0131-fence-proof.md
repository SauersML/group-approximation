---
rg: 2
id: leavitt-d4-l14-eighteen-i0131-fence-proof
kind: route
title: Exhaust the inverse 131 carriers and cyclic boundaries
target: leavitt-d4-l14-eighteen-i0131-is-fenced
requires:
  - leavitt-d4-l14-eighteen-i0131-projection-core
  - leavitt-d4-l14-i1412-paired-minimum-block-screen-is-fenced
---

The audited all-maximal forest/state-semiring solver gives two coordinate
states for the five-syllable carrier and sixteen for the 29-syllable carrier.
Their exact coordinate-Tietze intersection has sixteen states and three
abstract residual presentations (MSI job `16685370`).

Array job `16685516` processes one joint carrier state per shard.  For each
state it substitutes the exact carrier images into the 51-syllable boundary,
enumerates every free-product cyclic cut, appends `q^-1` in each of the four
target copies, and runs the all-maximal noncrossing forest relative to the
carrier state.  Q-first Tietze elimination is performed before generic
coordinate elimination.  No shard produces a free nonempty `q`.

All but twelve of the resulting nonempty target images are killed directly,
by a same-root power gcd, by iterative primitive-root saturation, by the
previous exact length-two involution substitution, or by a relator
difference.  The twelve remaining output states occur in carrier shards 11
and 12.  In each, after primitive saturation, the target is a cyclic conjugate
of a primitive length-three word `r`, the residual contains `r^2`, and `r`
has a generator occurring exactly once.

The generalized involution step is exact.  Introduce `t=r` and `t^2=1`.  If
`r=L g R`, eliminate `g` by `g=L^-1 t R^-1`; if `r=L g^-1 R`, eliminate it by
`g=R t L`.  The implementation independently asserts both signed formulas by
rewriting sample roots to `t`, asserts that the actual root rewrites to `t`,
and treats the temporary letter as self-inverse in both free and cyclic
reduction.  In all twelve residual states the rewritten target is trivial or
a cyclic conjugate of a rewritten relator.  Audit array `16685907` reruns the
two affected shards with this exact transformation and returns zero unresolved
targets.

Consequently every carrier-and-boundary forest kills `q`.  The class is
fenced; no coefficient-group or nonhyperlinearity conclusion is inferred from
this eliminated class.
