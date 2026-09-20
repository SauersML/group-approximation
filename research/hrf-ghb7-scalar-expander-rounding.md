---
rg: 2
id: hrf-ghb7-scalar-expander-rounding
kind: claim
title: Every fixed-gap doubled scalar-expander approximate representation of GHB2(7) rounds flexibly
distinct_from:
  ghb7-flexibly-hs-stable: That quantifies over every asymptotic representation; this restricts to six-generator doubled tuples with a fixed positive coordinate scalar gap.
  ghb7-one-edge-holonomy-absorption: That starts with genuine finite-vertex representations and two exact edge matches; this starts with approximate relators and a uniform scalar gap, which need not survive finite-vertex rounding.
artifacts:
  - research/artifacts/hyperbolic-rf-ghb7-2026-09-20.md
---

**OPEN.** For G=G_HB2(7), use generators a^+,a^-,b^+,b^-,c^+,c^-
with the original eleven relators on the plus generators and the three
copy-equality relators. Fix any c0>0. Every sequence of unitary tuples
V_n in dimensions d_n whose fourteen relator defects tend to zero and
such that

    (1/24) sum_{s in {a,b,c},sign} ||[V_s,n^sign,X]||_(2,d_n)^2
       >= c0 ||X-tr_d_n(X)I||_(2,d_n)^2

for every X must admit genuine representations pi_n:G->U(D_n),
D_n>=d_n, D_n/d_n->1, whose compressions approach all six tuple entries.

By `hrf-ghb7-expanding-block-localization`, this is equivalent to
GHB7 flexible HS stability, hence to its one-edge absorption problem.
A counterexample may be required to have d_n->infinity: bounded
dimensions round by compactness. This restriction is on the doubled
tuples; no scalar-gap transfer to one copy is assumed.

## Attempts

2026-09-20: Liu's accepted large-block theorem reduces all models to
this fixed-gap problem by weighted selection and direct-sum assembly.
It does not correct the remaining relators. Finite-group vertex rounding
is only normalized-HS close and need not preserve the gap against
unbounded HS-normalized witnesses. Commutant internality supplies no
such relator-correction estimate. The remaining task is dimension-uniform
rounding on this six-unitary class, or a fixed-gap counterexample.

The general scalar-expander rounding shortcut is refuted by
`hrf-audit-projective-internality-does-not-round`. For this particular
ambient group, however, `hrf-ghb7-scalar-relator-models-round-strictly`
rounds the subclass whose fourteen relators are exactly scalar. The
scalar-subclass proof needs no expansion assumption. The
remaining defects must escape this globally scalar subclass; induction
from a finite-index subgroup can produce nonscalar block defects.
The stronger `hrf-ghb7-central-relator-models-round-strictly` also rounds
the entire exact-central-relator subclass with a linear normalized-HS
bound and no expansion or padding. A block-scalar relator whose blocks
are permuted by generators need not be central and remains outside that
proved subclass.

ROUTES
hrf-ghb7-expander-rounding-from-stability
