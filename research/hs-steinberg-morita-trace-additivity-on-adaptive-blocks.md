---
rg: 2
id: hs-steinberg-morita-trace-additivity-on-adaptive-blocks
kind: claim
title: Canonical HS Steinberg microstates assign additive physical mass to adaptive diagonal root blocks
distinct_from:
  hs-finite-adaptive-ring-tree-decoder: That requests actual corner operators and all partial-isometry products; this asks only for the scalar Morita-trace law sufficient for bounded carrier growth.
  orthogonal-idempotent-sum-has-a-stabilized-steinberg-conjugacy: That identifies the block sum algebraically; this must convert its two diagonal blocks into additive normalized matrix mass.
  hs-steinberg-bcs-corner-kernel-is-linear-sofic: That embeds the entire coefficient quotient in a rank ultraproduct; this asks for one finite family of dimension values and no coefficient homomorphism.
  common-oriented-character-table-gives-morita-trace: That proves this face from a single payload-coupled finite PVM with oriented subset identities; constructing that PVM from the group microstate remains open.
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
- **Use one common oriented character table.**  This is sufficient by
  `common-oriented-character-table-gives-morita-trace`: disjoint subset union
  gives `(MTA2)` literally and the fixed arrow conjugators give `(MTA1)`.
  The remaining construction must couple the table orientation to the BCS
  payload.  A tensor-independent tag table cannot work because its apparent
  multiplicity gain is exactly cancelled by character-cylinder capacity.
- **Orient one edge by its three stabilized coefficient lines.**
  `three-line-first-hit-solves-local-morita-edge`
  constructs the orientation canonically and proves `(MTA1)--(MTA2)` on
  that one edge table.  What remains locally is `(TLF5)`: selected BCS mass
  must lie where the old-carrier complement and the new-range spectator
  characters are both trivial.  Globally, all outgoing edge tables must
  assign the same subset mass to their common parent.  Arbitrary
  representations can fail both requirements, so a matrix-only payload
  estimate and common orientation are still required.
- **The conditioned fiber has an exact local escape.**
  `three-line-first-hit-has-invariant-spectator-escape` charges the source
  and destination character coordinates simultaneously and is fixed by the
  arrow swap.  Therefore the finite additive table plus its normalizer cannot
  prove `(TLF5)`; a transverse multiplication row or genuinely matrix-only
  contextual constraint is necessary.
- **Two transverse E5 rows remove the spectator gauge after root detection.**
  `e5-idempotent-root-has-two-pair-extraspecial-cell` places two commuting
  Heisenberg pairs over every idempotent root.  On each nontrivial central
  root sector, their joint spectator characters are exactly uniform, so the
  double-trivial fiber has fraction `p^(-2)`.  This closes the finite
  Stone--von Neumann part of `(TLF5)`, but not the load-bearing transfer from
  the actual BCS atom `Q_sigma P_i` to nontrivial spectral support of the
  central root `x_13(a_(sigma,i))`.

The first half of that sentence is now its own minimal gate:
`bcs-atom-detects-its-e5-central-root`.  Its inequality `(BZR2)` plus the
two-pair extraspecial cell retains the fixed fraction `c_root p^(-2)` of a
selected BCS atom in a spectator-trivial source fiber.  After that local
step, the remaining Morita issue is compatibility of the parent subset
across the finite outgoing branch menu.

There is now a clean way to delete that last **outgoing-branch** issue.
`role-packed-bcs-gap-is-one-idempotent` places the `M` noncommuting forbidden
atoms in orthogonal spin-role coordinates and forms the single fixed
idempotent `B_f=sum_i R_iP_i`.  Its carrier mass is at least
`(beta/m)tau(Q)-O(sqrt(E))`, where `m=2^k>=M`.  The minimax theorem shows
that this pays exactly the same fixed-order loss as maximal selection, but
the adaptive coefficient tree becomes a unary chain with source
`a_n=q_nB_f`.  Hence no parent has several competing outgoing character
tables.  The surviving decoder is the sequential payload-to-root and
physical-carrier transfer for that one aggregate idempotent; compatibility
between successive reached carriers is still required.
