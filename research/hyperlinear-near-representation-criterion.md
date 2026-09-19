---
rg: 2
id: hyperlinear-near-representation-criterion
kind: claim
title: Hyperlinearity is equivalent to an essentially free amenable near representation
distinct_from:
  hyperlinear-wreath-model: that asks to construct microstates for a specific candidate; this is a general external criterion that could be used to do so
  mf-implies-hyperlinear: that concerns the norm-corona-to-tracial implication under this repository's conventions; this is an intrinsic characterization of hyperlinearity
---

Kahl--Schneider, *Hyperlinearity via amenable near representations*,
arXiv:2504.10988 (submitted 2025-04-15, revised 2026-01-05), prove:

> a group is hyperlinear if and only if it admits an essentially free
> amenable near representation.

Amenability of a unitary representation is in Bekka's sense, and the paper
first characterizes it via the existence of an orthonormal basis supporting
an invariant probability charge.  The result is the Hilbert-space analogue
of Elek--Szabo's characterization of soficity by essentially free amenable
actions, and the authors state that it answers a question of Pestov and
Kwiatkowska.  The same paper gives parallel characterizations of Kirchberg's
factorization property and of Haagerup's property.

## Why this is recorded

`hyperlinear-wreath-model` records that "the tools for proving
`R^U`-embeddability abstractly are thin".  This is a genuinely different
tool, and its witness is soft in exactly the way the dead architectures were
not: an invariant **finitely additive charge** on an orthonormal basis,
rather than a finite equivariant partition.  Every one of the eight refuted
architectures in `notes/OBSTRUCTIONS.md` §5 tried to build a finite carrier,
and `notes/FALSE_HALO_ACTION_AUDIT.md` shows why finite carriers with locally
sofic labels are circular here.  A charge can exist where no finite carrier
does, so the criterion is not obviously subject to the same collapse.

Recorded as a reusable external criterion, not as progress on any candidate.
