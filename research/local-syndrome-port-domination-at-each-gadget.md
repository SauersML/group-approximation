---
rg: 2
id: local-syndrome-port-domination-at-each-gadget
kind: claim
title: Each amplification gadget exposes a syndrome port dominated by the neighbouring energy
artifacts:
  - research/artifacts/qpcp-syndrome-rounding-audit-2026-08-25.md
  - research/artifacts/qpcp-paired-projector-obstruction-2026-09-07.md
  - research/artifacts/qpcp-joint-syndrome-support-2026-09-07.md
  - research/artifacts/qpcp-syndrome-primal-dual-2026-09-07.md
distinct_from:
  bounded-overlap-syndrome-energy-accounting: that is the finite incidence-counting lemma which sums local charges once they are supplied, and it is used unchanged by this region; this is the supply problem -- constructing the commuting local projectors and proving the per-port operator inequality against the neighbouring Hamiltonian terms.
  common-higher-rank-context-projections-are-syndrome-cylinders: that identifies syndrome cylinders among the common projections of a higher-rank context in the normalized-HS microstate atlas; this asks for tensor-site fault projectors dominated by a state-weighted local Hamiltonian energy, in a fixed finite-dimensional tensor product.
---

A load-bearing construction problem of the attack. The corrected converse in
`combinatorial-gap-and-rounder-give-energy-gap` identifies bare uniform
rounder cost with a NO-side energy floor only after positive constant
combinatorial gap has been supplied. That equivalence neither constructs
these ports nor supplies the hardness reduction, the YES bound, or (EX).

For the relevant NO outputs `H' = (1/m) sum_a h'_a` of the proposed
amplifier, construct an isometry
`W : H -> H_syn tensor H_data` and **mutually commuting** projectors `B_j` on
`H_syn`, indexed by syndrome fault labels, together with neighbourhoods
`N(j) subset [m]` such that

```text
W^* B_j W <= C_0 sum_(a in N(j)) h'_a,        C_0 = O(1),       (LSP1)
```

and every term `h'_a` lies in at most `R = O(1)` of the `N(j)`.  The `B_j`
must be **terminal local ports**: testable inside a bounded-radius region of
the amplified instance, with the logical subsystem left in the commutant, so
that measuring them reveals a fault pattern and not the encoded witness.
When flags name Hamiltonian terms directly, `j=a`. A gadget-indexed
construction must supply an explicit map from measured gadget faults to
term faults, with a uniform bound on its multiplicity; a common index
letter is not such a map.

Given (LSP1) and bounded occurrence,
`bounded-overlap-syndrome-energy-accounting` supplies the global (SD) with
`C = C_0 R`, and `commuting-syndrome-domination-gives-a-rounder` converts it
into the cost clause.

**Bounded horizon is part of the statement.**  Producing or testing a port
must not require propagating through a decoder whose depth grows with the
global code.  Otherwise the depth removed by
`checkpointed-syndrome-recursion-kills-depth-loss` reappears as decoder
depth and `C_0` is again not constant.

## Attempts

- **Supply one compatible construction.** The open claim
  `amplifier-has-compatible-local-syndrome-effects` binds these physical
  ports and local bounds to the joint support condition for recovery.
  `local-syndrome-synthesis-has-an-exact-sdp-test` gives an exact finite
  feasibility criterion and weak dual certificates. It does not construct
  local ports efficiently. On the paired-projector family, both-term
  neighborhoods admit recovery, but the sharp local constant is
  `(N^2+1)/4`, so this candidate still has no uniform bound.
- **Commuting flags by an unrestricted dilation.** Every joint POVM has
  commuting one-bit flags on a larger space. This supplies no bound on the
  physical realization of `W`; see
  `joint-syndrome-support-characterizes-exactifiability`.
  Even zero flags obey the displayed domination inequalities, but on a
  frustrated instance they produce an impossible empty fault set. The
  construction must also pass the joint support test for the same `W,B`.
- **Charge each flag only to its own term.** Ruled out on nonorthogonal
  qubit projector pairs by
  `nonorthogonal-pair-forbids-single-term-syndrome-ports`: finite domination
  forces each marginal flag effect below its own projector, while exactness
  forces the two effects to cover the identity. Their projector sum has
  an eigenvalue below one. This diagnoses singleton neighborhoods; the
  larger neighborhoods permitted in (LSP1) remain open.
- **Import a tracial outlier cut.**  Recorded dead as
  `syndrome-domination-by-tracial-outlier-cut-import` and killed by
  `tracial-domination-is-not-state-domination`: the corpus's cuts and
  pinching gaps are quadratic-form inequalities on the normalized-trace GNS
  space, and transporting one to a pure-witness weight costs a factor `d`.
- **Prove a per-gadget spectral gap and expect (LSP1).**  This is the shape
  `quadratic-overlay-has-uniform-linearized-synchronization-gap` already
  diagnosed in its own setting: a dimension-free *linearized* gap is
  available there and is explicitly not enough, because a Newton or
  alternating-projection argument still needs entry into one uniform
  nonlinear tube.  Here the analogue of the tube is a basin-capture or
  truncation theorem in the state-weighted geometry, and nothing supplies it.
- **Route through checkpointed anchors.**  Live, as
  `local-ports-from-checkpointed-anchors`; it moves the hole to
  `bounded-horizon-syndrome-anchor-exists` and
  `backward-syndrome-recursion-holds-for-the-amplifier`, neither of which is
  available.
