---
rg: 2
id: extensive-cosystolic-index-defect
kind: claim
title: A finite presentation forcing positive-density index defects in every approximate representation
distinct_from:
  index-density-is-amplification-stable: that is the scaling remark saying density is the only normalization the amplification no-go leaves alive; this is the missing construction that would put a positive density there
  additive-index-instability: that is the no-go this construction is designed to evade, and it is established; this is an open construction target
  hs-expander-block-decomposition: that decomposes an HS model into expander blocks for the Steinberg lane; this asks for a presentation whose relator syndrome cannot be concentrated on o(n) coordinates, which is a property of the presentation rather than of one model
artifacts:
  - research/artifacts/universal-hyperlinearity-audit-2026-08-18.md
---

OPEN.  Construct a finite group presentation `<S | R>` and a constant `c > 0`
such that every unitary `S`-table with small normalized-HS relator defect
carries at least `c · n` independent index defects, `n` the matrix dimension.
By `index-density-is-amplification-stable` such an obstruction is not erased
by tensor amplification, and by `additive-index-instability` no bounded-rank
version of it can work.

The design is: read a relator violation as a **syndrome**, and use an
expansion property of the presentation complex to prevent the syndrome from
being supported on `o(n)` coordinates.  The candidate sources of that
expansion are cosystolic expanders, high-dimensional expanders, quantum LDPC
codes and locally testable codes, all of which exist precisely to make local
checks certify a global, extensive defect.

## Attempts

**Bott index in a single coordinate.**  Dead, and the reason is the whole
point of this node: a Bott/Fredholm index attached to one pair of almost
commuting matrices is a bounded-rank datum with density `O(1/n)`, invisible
to the normalized metric.  This is `additive-index-instability` and it is what
`additive-index-transducer` fell to.

**Take the obstruction from the coefficient code directly.**  Not attempted.
The obstacle to be honest about: the known cosystolic/qLDPC statements bound
the *distance of a classical or quantum code*, i.e. the weight of a violating
vector, and what is needed here is a lower bound on the rank of a defect in an
approximate *unitary representation*.  No translation between the two is in
this repository, and none is claimed by the sources; the translation is the
work.

**Deferred parts.**  No candidate presentation is proposed here.  Recording
the target and its two proved constraints is deliberate: the constraints
(`Theta(n)` density required, bounded rank excluded) are cheap to state and
expensive to rediscover, and they disqualify most of the obvious attempts
before any construction is attempted.
