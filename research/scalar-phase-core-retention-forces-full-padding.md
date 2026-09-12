---
rg: 2
id: scalar-phase-core-retention-forces-full-padding
kind: claim
title: A scalar phase core with vanishing energy needs a full extra copy of the space if it is retained
distinct_from:
  bs14-flexible-cross-packet-boundary-reconciliation: that is the flexible boundary target itself; this refutes the retained-core reading of its second formulation and leaves the first one standing.
  inverse-conjugacy-padding-equals-multiplicity-defect: that is the general spectral count for one algebraic relation; this evaluates it on an explicit family whose presentation energy tends to zero, which is what makes it a countertest.
  flexible-hs-metric-controls-words-and-padding: that proves the sharp factor two between free and upward-only distance to a class; this exhibits an input whose upward-only distance under a retained core is bounded below while its free distance tends to zero.
artifacts:
  - research/artifacts/retained-core-and-rank-countertests-2026-09-08.md
---

**ESTABLISHED.**  In the square-free presentation of
`iwahori-square-free-bs14-presentation`, with the unnormalized energy `(FBR1)`
of `bs14-flexible-cross-packet-boundary-reconciliation`, fix `0 < theta < pi`
and put, in any dimension `d`,

```text
X = I_d,        T = I_d,        R = e^(i theta) I_d.                    (SP1)
```

`(R, T)` is an exact `BS(1,4)` representation and `X` is a unitary.  The only
nonzero energy terms are the inversion and the second cubic:

```text
E / d = 4 sin^2(theta) + 4 sin^2(3 theta / 2) = 13 theta^2 + O(theta^4).  (SP2)
```

**Retention is expensive.**  If an exact Iwahori tuple on dimension `d + k`
retains `R` as a reducing summand, then `X^ R^ X^ = R^(-1)` already follows
from `x^2 = (x r)^2 = 1`, so by
`inverse-conjugacy-padding-equals-multiplicity-defect` applied with
`m_R(e^(i theta)) = d` and `m_R(e^(-i theta)) = 0`,

```text
k >= d.                                                                 (SP3)
```

**Movement is cheap.**  Replacing `R` by `I_d` gives the trivial tuple, exact
in the original dimension, at displacement

```text
||R - I_d||_(2,d) = 2 sin(theta / 2) = O(theta).                        (SP4)
```

**What this refutes.**  Any repair statement that bounds the added dimensions
by the presentation energy *while keeping the old representation type* is
false: here `k >= d` and `C E = 13 C d theta^2 < d` for small `theta`.  In
particular the "Equivalently" reading of `(FBR2)` -- old multiplicity data plus
a vector `b` of weighted size at most `C E` landing in the Iwahori restriction
semigroup -- does not follow from `(FBR1)` and is not true; `(FBR1)`, which
asks only for displacement tending to zero, is satisfied here with `k = 0`.
The authenticated even-Weil results that prove `(FBR2)` in that node's attempts
are untouched: they never encounter a scalar packet with return phase off `1`.

The example says nothing against flexible stability itself.  It says that the
repair must be allowed to move the core before reconciling discrete
multiplicity data, which is also what
`iwahori-second-order-repair-space-is-empty` says about the directions that
movement may use.

**Scope.**  Only the retained-core reading falls.  Under the moving-core
reading of `(FBR2)` -- reconcile multiplicity data only after a displacement
that vanishes with `E/d` -- this family is repaired at `k=0` and carries no
information; that reading is open, and it is the one the attempts of
`bs14-flexible-cross-packet-boundary-reconciliation` use.  Nor is this a
refutation of the mismatch test recorded there: a genuine refutation must also
block every small-displacement motion of the core, which a scalar packet
cannot.
