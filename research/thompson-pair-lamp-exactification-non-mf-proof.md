---
rg: 2
id: thompson-pair-lamp-exactification-non-mf-proof
kind: route
title: Two-point lamp anchoring plus pair-kernel invariance kills the marked lamp
target: finite-memory-self-hash-non-mf
requires:
  - thompson-even-lamp-fp-finite-state-detector
  - thompson-pair-kernel-invariance-kills-even-lamps
  - thompson-pair-lamp-consistent-exactification
artifacts:
  - research/artifacts/finite-memory-pair-kernel-audit-2026-08-23.md
---

The detector supplies the finite presentation of `Gamma_state=I_X rtimes V`
and the marked lamp `b=b_(x_0,x_1)`, which is nontrivial in the group because
`I_X` embeds.

Let `Theta` be any norm-matrix-corona representation of `Gamma_state` and fix
unitary lifts.  For each coordinate `n` beyond the point where the finitely
many relators of `R` have defect at most `delta`, apply
`thompson-pair-lamp-consistent-exactification` to obtain an exact
commuting-involution representation `rho_n` of `I_X` anchored to the pair
words by `(PLC1)`, with actor transport `(PLC2)`.

The two constants combine below the involution threshold: a `rho_n`-killed
pair lamp is carried by an actor generator to a lamp at operator-norm distance
at most `1+eta<2` from `I`, hence to a killed lamp.  So the pair-kernel
relation of `rho_n` is invariant under a symmetric generating set of `V`, and
`thompson-pair-kernel-invariance-kills-even-lamps` makes `rho_n` trivial.
Anchoring then gives `||w_(x,y)(U^(n))-I||<=1/2` for every pair at that
coordinate, in particular for the marked lamp.

Finally `Theta(b)` is an exact involution of the corona, so
`||Theta(b)-1||` is `0` or `2`; the coordinatewise bound `1/2` excludes `2`,
so `Theta(b)=1`.  Every corona representation kills the marked lamp, which is
nontrivial in `Gamma_state`, so `b` lies in the MF radical and `Gamma_state`
is not MF.

**Relation to the sibling route.**  `thompson-even-lamp-rounding-non-mf-proof`
reaches the same target from `operator-norm-finite-state-rounding`, which asks
for a corrected finite exact joint-character state machine for the whole
module.  This route is a refinement, not an independent proof: it replaces
that hypothesis by the two-point, constant-threshold statement `(PLC1)`
--`(PLC2)`, using the involution dichotomy in place of a modulus.  Both remain
gated on the same unproved rounding phenomenon, and neither should be counted
as separate evidence for the target.
