---
rg: 2
id: fanizza-rank-gates-have-a-one-bit-character-escape
kind: claim
title: Each optimized Fanizza packet has a selector flip carrying exactly one Pauli bit
artifacts:
  - experiments/fanizza_fixed_predicate_rank_compiler.py
distinct_from:
  every-forbidden-atom-has-fixed-schur-pauli-words: that names the predicate-dependent extra factor after cutting to a forbidden atom; this gives a uniform rank-one difference between two neighboring coefficient characters at every atom.
  paired-frame-hard-characters-form-forced-two-cycle: that finds the compulsory 101-to-011 escape by exhaustive automorphisms of the support packet; this reads a one-bit escape directly from a rank-one affine coefficient matrix.
---

Write any optimized affine gate as

```text
M(x)=A_0+sum_i x_i A_i.
```

For each of the three gates in `(FSG1)`, one may choose the first selector bit
so that

```text
rank_F2 A_1=1.                                         (OBE1)
```

In fact the exact derivative-rank profiles are

```text
conjunction equality:                 (1,1,1),
conjunction graph:                    (1,1,1),
conditional three-projection split:  (1,2,1,1,1,1).   (OBE2)
```

Consequently, for every selector assignment `x`,

```text
M(x)+M(x+e_1)=A_1
```

has rank one.  The alternating commutator forms of coefficient characters
`x` and `x+e_1` therefore differ by rank two: exactly one Pauli factor.  Since
`A_1=u v^T`, fixed products of the commuting p-generators indexed by `u` and
q-generators indexed by `v` name this escape coordinate.

This gives every Fanizza predicate packet a uniform finite reverse character
which can be coupled to the E5 valuation clock.  It does not by itself orient
the flip: forgetting the valuation label again gives a two-cycle and admits a
stationary finite-character flow.  Nor does `(OBE1)` localize the escape to
forbidden atoms; that localization still uses the Schur pair words and the
shared endpoint context laws.
