---
rg: 2
id: multicharacter-pvm-alignment-modulo-simultaneous-gauge
kind: claim
title: Align all terminal code-character leaves simultaneously modulo common conjugacy
distinct_from:
  two-code-character-cut-recenters-to-one-coordinate: that exactly aligns one binary character cut; this must aggregate all character pairs without decision-tree depth
  code-distance-upgrades-pair-energy-to-full-pinching: that assumes a commuting reference PVM is already available; this constructs the gauge-corrected reference from terminal signed contractions
  terminal-common-pinching-displacement-vanishes: that includes spike budgeting, recursive gap stopping, and terminal scaling; this is the remaining nonlinear finite-PVM alignment step after those reductions
---

OPEN.  Let `(Q_i)` be a balanced exact-parity reflection tuple with
complete-pair energy `epsilon`.  Let `(f_a)` be a finite PVM obtained from
the contraction cut tree.  After terminal signing and high-gap rounding,
refine and label its central terminal atoms by code characters `c_a`, with
total diagonal rounding energy `eta`.

Construct, allowing one simultaneous unitary gauge change and merging atoms
with the same label, a PVM `(g_b)` such that its leaves retain the required
terminal generated-adjoint gaps and

```text
(1/L)sum_i||Q_i-sum_b g_bQ_ig_b||_2^2
 <=omega(epsilon+eta),                                  (MCA1)
```

where `omega(t)->0` is independent of code length, number of represented
characters, character multiplicities, and matrix dimension.

For two leaves this is `two-code-character-cut-recenters-to-one-coordinate`.
The complete-pair linearized minor is uniformly coercive transverse to
simultaneous conjugacy, so `(MCA1)` is the nonlinear/global version of that
minor.  `sequential-character-recentering-has-decision-tree-loss` rules out
obtaining it by paying one worst-case commutator row at every binary split.
The surviving aggregation is weighted coordinate hashing:
`weighted-code-character-hash` selects
`O(log(1/eta))` rows with small total pair energy and only `eta` unresolved
off-diagonal mass.  The remaining gate is to realize that hash as one
gauge-aligned joint PVM, recorded in
`sampled-coordinate-joint-pvm-tracks-terminal-character-hash`.

## Attempts

1. **Fixed old PVM.**  Common character rotations have boundary quadratic
   in the angle and residual quartic, so the old PVM cannot be controlled
   linearly.  The PVM must move along the simultaneous-conjugacy orbit.
2. **One separator per split.**  The exact two-leaf recentering theorem makes
   each split cheap, but Kraft entropy yields a `log |D|` accumulation for a
   menu `D` of represented characters.
3. **Mixed-commutator pinching.**  Code distance controls pinching relative
   to an already commuting character PVM.  Comparing that mixed energy with
   the raw pair energy introduces the unknown pinching displacement on both
   sides and gives no absorption outside a pre-existing basin.
