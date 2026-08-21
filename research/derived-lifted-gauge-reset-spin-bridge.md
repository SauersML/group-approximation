---
rg: 2
id: derived-lifted-gauge-reset-spin-bridge
kind: claim
title: Lift the gauge reset into an equal-scale reverse Schur spin bridge
distinct_from:
  weyl-derivative-reset-preserves-schur-spin-scale: that transports the old baseline to a fixed derivative spin packet and produces the gauge implementer; this must install the next selector-dependent baseline.
  semidirect-reset-implementer-cannot-be-next-schur-phase: that rules out doing so inside the bare semidirect product; this permits a finite overgroup or finite incidence with a derived lift.
---

For the fixed gauge-doubled Fanizza predicate menu, construct a finite group
incidence which contains the Weyl derivative reset and a next Schur baseline,
such that:

1. the invariant logical products `A_xB_x` and the native signal are fixed;
2. every reset gauge implementer enters the derived subgroup on the reverse
   side and is a legal central selector coefficient there;
3. the old derivative spin type and every new baseline selector-sector spin
   type restrict to the common edge packet with the same multiplicity, so the
   normalized multiplicity currency keeps one fixed matrix scale;
4. the marked base embeds, using the gauge-orbit covariant representation for
   exact completeness; and
5. fixed finite-group exactification and overlap alignment give an
   `O(sqrt(E))` transport loss independent of ambient dimension.

A generic finite wreath envelope makes an involution derived: in
`(R times R) semidirect C_2`, with the last factor swapping the copies,

```text
[(s,1),swap]=(s,s).                                     (DLG1)
```

Thus abelianization alone is not a terminal obstruction. The open part is to
realize `(DLG1)` while matching the old and new spin restriction matrices at
equal scale. Tensoring an independent Pauli pair is not enough because it
doubles the packet scale; the lift must replace a Pauli direction or use a
balanced Morita edge.

## Attempts

- The bare semidirect product is impossible by
  `semidirect-reset-implementer-cannot-be-next-schur-phase`.
- The two-copy wreath commutator `(DLG1)` solves only derivedness. Its naive
  tensor-product placement adds a qubit and changes the current scale. The
  active finite calculation is to replace one old hyperbolic pair by this
  derived pair and compare both restriction matrices over the remaining
  codimension-two spin subgroup.
- `gauge-symmetrizing-hard-pair-cancels-paired-overlap-gap` rules out a weaker
  interpretation of the bridge: summing the two private gauge orientations
  and returning only their invariant logical product cancels the paired-frame
  scalar gap exactly.  The derived lift must therefore transport an oriented
  gauge share at equal spin scale, not merely the gauge-invariant sum.
- `pauli-quarter-holonomy-is-balanced-derived-reset` now supplies an intrinsic
  exact candidate for that oriented lift.  Two canonical quarter-carrier
  reflections generate `D_8`; their commutator has a trace-`1/8` negative
  sector on which the reflections are a balanced anticommuting Pauli pair.
  The new central sign is therefore derived and no independent tensor qubit
  is added.  The remaining work is the finite semantic incidence and
  ordinary-word exposure of the two Hecke reflections, not the local spin
  arithmetic.
- `regular-gauge-orbit-contains-equal-scale-derived-d8-reset` removes the two
  remaining local drawbacks of that candidate.  On four-point cosets already
  present in the gauge-covariant completeness orbit, the reset translation is
  the central commutator of a literal square `D_8` action.  Its negative sector
  is one balanced two-dimensional spin simple, so no tensor qubit is added and
  no Hecke reflection must be exposed as a word.  The remaining audit is now
  only the common codimension-one residual spin incidence between the old
  derivative packet and all next selector-sector baselines.
