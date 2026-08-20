---
rg: 2
id: conjugacy-compressed-dimension-trigger
kind: claim
title: Conjugate terminal flags remove runtime from the relator norm but not from semantic transport
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
distinct_from:
  boone-commutator-criterion-for-halting: that compresses a computation to one exact group equality; this is a normalized-HS estimate for conjugates and isolates the still-missing robust semantic comparison.
  fixed-holonomy-on-overlap-pays-relator-energy: that lower-bounds the energy of a nontrivial fixed finite-factor action; this upper-bounds a conjugate of a relator by that relator's own defect.
---

Let `r` be one fixed relator and let `c_n=a_n^(-1) r a_n`, where the words
`a_n` may encode computations of unbounded length.  For every unitary tuple
`U`,

```text
||c_n(U)-1||_2 = ||r(U)-1||_2.                                    (CCD1)
```

There is no dependence on `n`, `|a_n|`, or the runtime represented by `a_n`.
Consequently, if a compiler supplies a marked word `w`, a dimension selector
`N(d)`, and a universal constant `C` such that

```text
||w(U)-c_(N(d))(U)||_2 <= C Def(U),                                (CCD2)
```

then

```text
||w(U)-1||_2 <= (C+1) Def(U),                                     (CCD3)
```

when `Def` dominates the defect of `r`.

The exact identity `(CCD1)` solves only the terminal-flag cost.  The uniform
semantic estimate `(CCD2)` is not a consequence of conjugacy: an ordinary
van Kampen derivation from `w` to `c_n` can still accumulate error proportional
to its area.  Any HS--PCP Boone construction must prove `(CCD2)` by additional
local redundancy, recursive compression, or fixed-holonomy synchronization.

