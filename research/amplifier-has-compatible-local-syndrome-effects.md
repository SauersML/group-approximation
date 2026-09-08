---
rg: 2
id: amplifier-has-compatible-local-syndrome-effects
kind: claim
title: One amplifier syndrome construction satisfies both local energy bounds and joint fault feasibility
artifacts:
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
  - research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md
distinct_from:
  local-syndrome-port-domination-at-each-gadget: that records the port and local-cost component; this requires its same isometry and joint measurement to avoid every infeasible fault label as well.
  syndrome-conditioned-exactifier-exists: that records the recovery component for specified ports; this binds recovery feasibility and local charges to one common construction with uniform constants.
  local-syndrome-synthesis-has-an-exact-sdp-test: that is an unrestricted finite-dimensional characterization; this asks for uniform compatible effects with the physical realization needed for the amplified QMA instances.
---

For the **same** proposed polynomial-time amplifier used in
`locality-preserving-constant-combinatorial-gap` and
`amplifier-preserves-yes-energy-below-the-floor`, its relevant NO-instance
outputs admit one tuple `(W,{B_a},{N(a)},C_0,R)` with these simultaneous
properties:

1. `W` is an isometry and `B_a` are commuting syndrome projectors. The
   realization meets the terminality, bounded-horizon, and logical-algebra
   requirements of `local-syndrome-port-domination-at-each-gadget`; an
   unrestricted Naimark dilation does not establish these.
2. The flag index `a` names the Hamiltonian term `h'_a` that may be left
   unsatisfied. `W^*B_a W <= C_0 sum_(b in N(a)) h'_b`, and each term belongs
   to at most `R` neighborhoods. `C_0,R` are uniform absolute constants.
3. For the joint projector `Pi_S` of these same `B_a`,
   `W^*Pi_S W=0` whenever `intersection_(a not in S)ker h'_a={0}`.

If a construction uses gadget flags instead of term flags, it must supply
an explicit map to the term fault set and its constant multiplicity cost;
that map cannot be inferred from similar index names.

This is the still-open compatible construction, not a proved consequence
of separate existential witnesses for the two component claims. The
finite SDP criterion can audit its joint effects, but supplies no uniform
construction or physical implementation by itself.

## Attempts

- **Independent marginal bounds and recovery witnesses.** Insufficient:
  `identical-flag-marginals-can-disagree-on-exactifiability` gives identical
  local costs with opposite recovery verdicts. The whole joint measurement
  must meet the support condition.
- **Solve the joint-effect SDP.** This is an exact unrestricted criterion,
  but its global kernels and potentially exponentially many full-space
  matrices do not provide a bounded-horizon physical construction. A
  uniform construction for the amplifier is still missing.
- **Enlarge the pair's energy neighborhoods.** This permits exact recovery,
  but the matching certificates in the primal/dual artifact prove the
  optimal local constant `(N^2+1)/4`. Its growth excludes this family as
  a uniform-cost construction; it does not exclude other amplifiers.
