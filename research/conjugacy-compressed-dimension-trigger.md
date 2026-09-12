---
rg: 2
id: conjugacy-compressed-dimension-trigger
kind: claim
title: Conjugate terminal flags remove runtime from the relator norm but not from semantic transport
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
  - research/artifacts/conjugacy-addressed-machine-groupification-audit-2026-08-20.md
distinct_from:
  boone-commutator-criterion-for-halting: that compresses a computation to one exact group equality; this is a normalized-HS estimate for conjugates and isolates the still-missing robust semantic comparison.
  fixed-holonomy-on-overlap-pays-relator-energy: that lower-bounds the energy of a nontrivial fixed finite-factor action; this upper-bounds a conjugate of a relator by that relator's own defect.
---

Let `r_1,...,r_s` be a fixed finite menu of prototype relators and let
`c_x=a_x^(-1) r_(j(x)) a_x`, where the address words `a_x` may encode
locations at unbounded distance in an unbounded computation.  For every
unitary tuple `U`, formal word evaluation gives

```text
||c_x(U)-1||_2 = ||r_(j(x))(U)-1||_2.                              (CCD1)
```

This does not assume that `U` is a representation: every word evaluates to a
unitary, concatenation evaluates multiplicatively, and inversion evaluates
as adjoint.  Thus

```text
c_x(U)-1=a_x(U)^* (r_(j(x))(U)-1) a_x(U),
```

and normalized Hilbert--Schmidt norm is exactly unitarily invariant.  There
is no dependence on `x`, `|a_x|`, or the runtime represented by `a_x`.
Consequently the maximum defect of any collection of addressed checks is at
most the maximum prototype defect, while its mean squared defect is merely a
convex combination of the finitely many prototype squared defects.  Neither
quantity pays address length.

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
There is a second, logically separate loss when an orbit cell has several
word names.  `stabilizer-generator-control-has-unbounded-address-loss` proves
that finite-generator control of the stabilizer gives only a stabilizer-word
length bound and that no uniform replacement follows without a spectral-gap
or rounding theorem.
