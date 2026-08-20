---
rg: 2
id: signed-hecke-block-escaping-cycle-holonomy
kind: claim
title: Realize the balanced BCS cycle holonomy by algebraic corner unitaries escaping the finite root block
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  signed-hecke-compatible-projection-atlas-for-nonce-bcs: that states the complete projection-atlas target without normalizing its local types; this starts from the common balanced hyperoctahedral packet and isolates the remaining chord holonomy.
  s3-radical-return-via-picture-curvature: that seeks a matrix-only HS return for the approximate Fanizza compiler; this is an exact algebraic corner construction intended to promote the canonical trace directly.
---

For the balanced common packet of
`tracial-bcs-has-rational-balanced-hyperoctahedral-atlas`, construct a
finitely presented group `Gamma` containing a copy of `K_D`, put
`q=q_D`, and construct algebraic corner unitaries `V_c in qC[Gamma]q` such
that

```text
P_(c,a)=V_c (sum_(j=1)^(n_(c,a)) e_(c,a,j)) V_c^*       (BCH1)
```

form context partitions and

```text
sum_a a_x P_(c,a)=sum_b b_x P_(d,b)                      (BCH2)
```

on every overlap.  Each `V_c` may be a finite piecewise group transport as in
`(PGT1)--(PGT4)`.

At least one context diagonal algebra, equivalently at least one projection
`P_(c,a)`, must not be contained in the finite root algebra
`qC[K_D]q`; this is forced by
`root-block-piecewise-transport-cannot-host-nonce-bcs`.  Thus the chord
transport must preserve the one shared binary marginal while moving the
rest of the context matrix block into a genuinely new position in the
infinite corner.  Every projection and unitary must have finite group-word
support, and `(BCH2)` must be an exact identity, not merely a relation in a
chosen representation.

## Attempts

- **Coordinate-permutation normalizers: dead.**  They keep every conjugated
  context algebra inside `qC[K_D]q`; the root-block obstruction then produces
  a forbidden finite-dimensional BCS trace.
- **Ordinary Bass--Serre chord: insufficient.**  A stable letter can conjugate
  one balanced sign to the other, but `(BCH2)` asks that the two corner
  elements be equal.  Conjugacy alone leaves precisely the cycle holonomy.
- **Signed-kernel chord: active formulation.**  It would suffice to make the
  relative chord unitary act trivially on the shared two-block marginal while
  acting nontrivially on the rest of the context block.  A finite-group kernel
  does this only inside the root matrix algebra; the missing construction is
  an algebraic group-corner unitary with the same selective fixed algebra and
  a block-escaping range.
- **Piecewise transport: local algebra solved, equality open.**  `(PGT1)--
  (PGT4)` builds finite-support corner unitaries once source and range
  partitions are named.  No current group presentation forces the additive
  equality `(BCH2)` for the resulting sums without already assuming the
  desired compatible atlas.
- **One binary chord is solved exactly.**
  `one-binary-marginal-block-escape` uses a
  same-sign Hadamard rotation and independent free phases.  Its atom
  refinement leaves the root block while the chosen signed marginal remains
  fixed.  By `free-phase-context-escape-criterion`, a genuine BCS assignment
  atom moves exactly when that marginal has two supported assignments in one
  sign fiber.  The only remaining issue on
  `signed-hecke-simultaneous-holonomy-route` is coupling these cells so every
  incident marginal comes from one context partition.
