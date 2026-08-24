---
rg: 2
id: hs-steinberg-morita-trace-additivity-on-adaptive-blocks
kind: claim
title: Canonical HS Steinberg microstates assign additive physical mass to adaptive diagonal root blocks
distinct_from:
  hs-finite-adaptive-ring-tree-decoder: That requests actual corner operators and all partial-isometry products; this asks only for the scalar Morita-trace law sufficient for bounded carrier growth.
  orthogonal-idempotent-sum-has-a-stabilized-steinberg-conjugacy: That identifies the block sum algebraically; this must convert its two diagonal blocks into additive normalized matrix mass.
  hs-steinberg-bcs-corner-kernel-is-linear-sofic: That embeds the entire coefficient quotient in a rank ultraproduct; this asks for one finite family of dimension values and no coefficient homomorphism.
---

**OPEN MORITA-TRACE FACE.**  In canonical normalized-HS microstates of the
rank-five wordization of `finite-adaptive-selected-atom-ring-tree`, assign to
each named adaptive idempotent `e` a nonnegative physical carrier mass
`mu(e)` such that, with dimension-independent error tending to zero,

```text
mu(d_(sigma,i))=mu(a_(sigma,i)),                       (MTA1)
mu(q_sigma+d_(sigma,i))
 =mu(q_sigma)+mu(d_(sigma,i)),                         (MTA2)
mu(a_(sigma,i))
 >=tau(Q_sigma P_i)-o(1).                             (MTA3)
```

The assignment must use the prescribed seed spectral carrier and the same
decoded shared BCS tuple at every node.  It is enough on the finite set of
idempotents occurring up to the fixed depth `N`; no rank function on the
whole coefficient quotient is requested.

Equation `(MTA1)` is algebraically authenticated by
`murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness`, and the block
packet in `(MTA2)` is conjugate to the sum packet by
`orthogonal-idempotent-sum-has-a-stabilized-steinberg-conjugacy`.  The open
content is that the normalized matrix trace seen by the microstate is a
**Morita trace** on those block packets.  Abstract unitary representations
can put the two diagonal root packets on overlapping multiplicity
reservoirs, so conjugacy and finite-window spectral measures alone do not
give `(MTA2)`.

Once `(MTA1)--(MTA3)` hold, `(MFA1)` gives the same supercritical scalar
recurrence as `(FAR3)`.  The fixed depth then contradicts total mass one.

## Attempts

- **Use the nontrivial spectral support of each root word.**  Supports of
  commuting root unitaries need not be disjoint; their characters can
  overlap or cancel on the same multiplicity reservoir.
  `orthogonal-steinberg-root-spectral-support-is-not-additive` gives an
  exact full elementary-group countermodel: both coordinate idempotents and
  their sum have the same Plancherel support density `1-1/p`.
- **Use only the stabilized conjugacy.**  It proves equality between the
  sum packet and the block packet, but it does not make the two diagonal
  block packets orthogonal as operators in an arbitrary representation.
- **Decode the whole coefficient quotient.**  This would work by
  `hs-steinberg-bcs-corner-kernel-is-linear-sofic`, but is deliberately
  stronger than the finite scalar law requested here.
