---
title: STW XI audit --- transfinite cumulative compact-open filtrations (2026-08-30)
---

## Result

A continuous decreasing filtration of a compact metrisable `Z^d`-space by
an arbitrary ordinal glues quasidiagonality provided every cumulative open
support `X\Y_beta` has an invariant compact-open exhaustion, every
successor-stratum crossed product is quasidiagonal, and the terminal
closed-support crossed product is quasidiagonal.

This is strictly beyond the finite-chain result: at an omega-chain there
need not be any finite stage whose tail crossed product is known to be
quasidiagonal, so finite backward induction never starts.  Instead, the
proof builds the open-support ideals forward.  Successor steps use a
projectional two-cut extension; limit steps use norm-local approximation by
the increasing union; a final projectional cut glues the terminal quotient.

## Checks at the three stage types

At a successor stage, exactness of the amenable crossed product gives the
successor stratum as the quotient.  A compact-open subset of the cumulative
open support is actually clopen in the compact ambient space, so its
characteristic function is an invariant central projection.  Compression
of the successor ideal by that projection lands back in the already
quasidiagonal predecessor ideal.

At a limit stage, continuity of the closed supports turns the cumulative
open set into an increasing union.  Every compactly supported coefficient
is already supported at one earlier stage; finite Fourier sums then show
that the crossed-product ideal is the norm closure of the earlier ideals.
Quasidiagonality is local under injective increasing unions.  There is no
cofinality restriction: a finite subcover of a compact support has a maximum
ordinal index.  Although second countability separately implies that only
countably many successor stages can change the open support strictly, the
proof does not need to first collapse repetitions or reindex the chain.

At the terminal stage, the same cumulative compact-open exhaustion is a
central projectional approximate unit for the entire open-support ideal.
Its corners are quasidiagonal because the ideal just constructed is
quasidiagonal, and the terminal quotient is quasidiagonal by assumption.

## Sharp boundary

Exhausting each relative stratum separately is not enough for this proof.
A set which is compact-open in `Y_beta\Y_(beta+1)` can meet the boundary of
`Y_beta` and fail to be open in `X`; its characteristic function then is
not an ambient projection.  Nor does quasidiagonality of the intersection
subsystem imply quasidiagonality of any finite tail quotient, so an infinite
backward induction has no base stage.  The cumulative compact-open condition
is the precise additional hypothesis used here.

The theorem concludes quasidiagonality only.  Promoting the result to an AF
embedding would import the open exact quasidiagonal-to-AF problem.
