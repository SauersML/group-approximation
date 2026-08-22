---
rg: 2
id: reset-schur-bcs-branching-atlas
kind: claim
title: A reset HNN atlas returns the full Schur BCS child carrier with polynomial HS loss
distinct_from:
  toeplitz-schur-child-masa-recurrence: that follows the satisfying-oriented Fanizza tape and must pay its inactive FDB1 sectors; this uses a fixed non-CE BCS at every level, orients each rank gate toward violation, and returns the full one-plus-violation child carrier.
  branch-reset-amalgam-preserves-mark-and-balances-types: that resets one old selector chart and preserves a mark; this must assemble those cells recurrently and retain the robust BCS violation mass at every returned level.
---

For one fixed finite BCS with a tracial state but no Connes-embeddable tracial
state, construct a finite recurrent presentation from its context-local
Schur--Clifford violation packets, groupified corrected child-center charts,
transverse resets, and HNN chart transports, with the following uniform
property.

For every finite-dimensional normalized-HS tuple of relator energy `E`, its
level-`n` returned carrier has normalized baseline-packet mass `a_n`; after
local exactification it has forbidden mass `v_n` and full `Q`-child mass
`c_n`. There are fixed `beta,C,k>0` such that

```text
v_n >= beta a_n-C(n+1)^k sqrt(E),                     (RSA1)
c_n = a_n+v_n,                                        (RSA2)
a_(n+1) >= c_n-C(n+1)^k sqrt(E).                      (RSA3)
```

Every relator is used with uniformly bounded overlap in these estimates. The
presentation also has an exact representation in which the marked word is
nonidentity and the level-zero carrier has positive mass.

The original shared BCS words must be tested before contextwise packet
correction, so `(RSA1)` is the robust noncommutative BCS gap rather than a
classical assignment gap. Different context selector charts must not be made
globally commuting. The corrected-center chart must expose the actual
child-simple labels from `(RSC2)`. Its reset removes the old selector center,
and the HNN edge aligns its complete branch-type vector with the next context
chart. Raw `q_(N+1)` eigenspaces are not admissible substitutes.

This target is deliberately finite and quantitative. It asks only for the
remaining compatibility of the already explicit reset and HNN cells around
one recurrent atlas, not for a new nonlinear scalar group word and not for
Fanizza inactive-sector payment.  The atlas must now contain a genuinely
non-type-preserving return between its HNN charts: pure HNN transport is
provably stationary by `reset-ray-hnn-return-is-stationary`.

## Attempts

- **Literal nesting:** invalidated by
  `nested-schur-multiplicity-wire-globalizes-selectors`.
- **Plain HNN return:** invalidated by
  `hnn-conjugacy-cannot-return-schur-morita-multiplicity`; the HNN edge is used
  only after child branching, to preserve and align the resulting types.
- **Raw reset then align:** invalidated by
  `raw-schur-generator-is-not-child-center`; it balances raw `q` spectra, not
  child-simple multiplicities.
- **Corrected center then align:** active. First solve
  `groupify-schur-child-center-chart`; after that,
  `hnn-selector-chart-transport-preserves-mark-and-types` supplies the valid
  type-preserving edge. The remaining atlas problem is to make these local
  corrections share one recurrent carrier while retaining `(RSA1)` with
  bounded overlap.
- **Balanced reset plus HNN alone: fails exactly.**
  `reset-ray-hnn-return-is-stationary` computes the sole reset ray.  The HNN
  edge keeps its scalar `n` fixed, whereas the `Q` child has surplus
  `2K_1n`; consequently `(RSA3)` fails at zero error.  A proper corner or
  one-sided compressor must sit between the child chart and the next full
  packet.  Selector renewal is solved, but multiplicity return is not.
- **Full reset followed by the flip-free `q`-MASA: loses the predicate
  current.** Although the words `Q_x` separate the two child supports on a
  fixed selector sector, `full-reset-makes-q-masa-negative-regular` computes
  the aggregate endpoint after the translation-symmetrized full reset. Its
  complete `K_f` character vector is a multiple of the negative regular
  character, independent of the active set of `f`. Thus the proper-corner
  actuator cannot be driven only by the bare post-reset `q`-MASA vector. It
  must cross the one-sided corner before sector averaging, or carry the
  explicit predicate-density element in addition to `K_f`.
- **Proper-corner route.**  `reset-schur-atlas-via-toeplitz-proper-corner`
  now records the corrected composition.  Its only genuinely new analytic
  input is `toeplitz-tail-retains-contextual-schur-density`: the tail must
  return the predicate-oriented density, not merely the structural Reynolds
  wall.
