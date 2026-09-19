---
rg: 2
id: oracular-2csp-mark-relative-canonical-groupifier
kind: claim
title: Groupify a finite oracular 2-CSP only relative to a surviving canonical-profile mark
distinct_from:
  bcs-projective-kernel-phase-compilation: that asks for a fixed projective phase and a quantitative finite-dimensional energy comparison; this permits an arbitrary rational mark and asks only for an ultraproduct decoder on canonical-profile maps where that mark survives.
  fanizza-canonical-profile-groupification: that groupifies the native Fanizza HALT signal; this uses the Culf--Mastel perfect-gap 2-CSP family and has no distinguished source projection.
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that asks for an exact unital corner embedding of the whole BCS algebra; this permits a representation-dependent decoded CE trace and need not define any algebra homomorphism into the group algebra.
---

Totally computably from a finite oracular 2-CSP `B`, construct a finite
alphabet, a uniformly recursively enumerable ordinary group presentation

```text
Gamma_B=<S_B | R_B>
```

and a finite rational group-algebra mark `p_B` with the following two
properties.

1. If `B` has a perfect CE tracial model, then `p_B!=0` in
   `Q[Gamma_B]`.  It is enough to exhibit one exact unitary representation
   of `Gamma_B` detecting `p_B`; the representation need not have canonical
   group trace.
2. For every canonical-profile microstate sequence for `Gamma_B`, if
   `||p_B(U_n)||_2` does not tend to zero, then a nonzero corner of the
   associated matrix ultraproduct carries a perfect CE tracial model of
   `B`.

No finite-coordinate modulus, uniform soundness constant, or exact decoder
on noncanonical representations is required.  The decoder may depend on the
ultraproduct map and on the support corner of `p_B`.

## Exact remaining content

Oracularity supplies allowed-pair PVMs and their marginal projection
identities.  Fixed finite signed packets can realize each allowed-pair block,
and canonical trace pins their Plancherel multiplicities.  What is not
supplied is simultaneous identification of the same marginal across all
incident blocks on one positive-density carrier.  After rank balancing, this
is relative-position/cycle holonomy, not a dimension-counting problem.

A valid construction may therefore use a canonical packet detector, but its
decisive relation must be a nontransport, block-escaping return around the
2-CSP incidence cycles.  A finite sheet permutation, scalar bus, or a test
that reads only individual isotypic multiplicities cannot establish clause
2.

## Attempts

- **Algebraic-corner bypass.**
  `oracular-2csp-algebraic-corner-map-is-a-canonical-groupifier` proves that
  an explicit unital map `A(B)->q Q[Gamma_B]q`, with `q` a nonzero rational
  algebraic projection, already supplies clause 2 by pulling back the
  normalized canonical corner trace.  This removes every finite-coordinate
  decoder and multiplicity modulus.  It does not construct the map: its only
  unsolved equation is equality of the shared signed marginals in one
  algebraic corner while preserving `q`.
- **Canonical local packet authentication.**  Restrict canonical microstates
  to fixed finite context subgroups and use finite-group HS stability.  This
  pins every local Plancherel type, but
  `oracular-local-block-detectors-miss-balanced-cycle-holonomy` shows that it
  leaves arbitrary equal-rank multiplicity holonomy on every chord.
- **Infinite depth/unfolding.**  Unfold the incidence graph into a tree and
  impose progressively more return relations.  This tolerates arbitrarily bad
  depthwise constants, but still needs a finite-support return carrying one
  marginal around each original cycle.  For an exact corner atlas,
  `finite-bcs-corner-diagram-is-finitely-witnessed` proves that an infinite
  recursive tail cannot be the source of that return.
- **Deferred live attack.**  Use a local authenticated packet only to name the
  common carrier, then make one chord act by a genuinely nontransport
  group-algebra operator whose kernel is equality of the two marginal sums.
  This is the qualitative canonical-profile version of the existing
  block-escaping signed-Hecke chord; no such operator is presently known.
- **Rational PZK profile.**
  `lin-pzk-tableau-rational-qc-not-qa-correlation` gives a completely
  explicit rational non-CE pair table and, after finite answer splitting,
  equal local marginal weights.  This is useful canonical target data and
  removes denominator/rank balancing for the selected trace.  It does not
  establish either clause here: pair probabilities are not algebraic
  projections in `Q[Gamma_B]`, equality of their selected traces does not
  identify incident marginal projections, and no mark or decoder on
  arbitrary canonical-profile microstates is produced.  The incidence-cycle
  holonomy remains the same nontransport operator-placement problem.
