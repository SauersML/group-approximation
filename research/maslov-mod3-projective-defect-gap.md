---
rg: 2
id: maslov-mod3-projective-defect-gap
kind: claim
title: The two nontrivial mod-three Maslov projective sectors of Sp4(Z) have a dimension-free normalized-HS defect gap
artifacts:
  - research/artifacts/deligne-maslov-hyperlinear-strategies-2026-08-21.md
distinct_from:
  iwahori-local-global-defect-question: Iwahori asks whether two almost-compatible SL2(Z) representations can be repaired to a compatible pair; this asks only whether one fixed nonzero projective cohomology class of Sp4(Z) has any arbitrarily accurate normalized-HS models.
  exel-loring-mark-quantization: Exel--Loring quantizes a winding invariant of almost commuting matrices; this is a projective relator-energy gap for the mod-three Meyer--Maslov multiplier.
  quantum-context-frame-index: that builds parity/index from a finite contextual frame system; this uses the classical symplectic universal-cover cocycle and no BCS frame packet.
---

Fix a finite presentation of `Gamma=Sp_4(Z)` and let `alpha` be the
`Z/3`-valued multiplier obtained from the three-fold Deligne cover (equivalently
a mod-three representative of the universal-cover/Meyer--Maslov class).

Prove that there are a finite presentation window and `c>0` such that for
**every** matrix dimension `d`, every tuple of unitaries attempting to satisfy
the `alpha`-projective relations has maximum normalized-HS relator defect at
least `c`; and likewise for `alpha^2`.

Equivalently, neither nontrivial twisted sector admits a sequence of
finite-dimensional projective almost representations with defect tending to
zero.

## Attempts

- **Twisted Fox/Jacobian gap.** Linearize the projective relators with the
  multiplier held fixed.  The scalar gauge direction disappears.  A
  dimension-uniform lower bound on the twisted Jacobian, followed by a
  quantitative implicit-function/Newton argument, would isolate the empty
  exact projective representation variety.
- **Maslov curvature energy.** Choose an explicit finite family of symplectic
  elements/Lagrangians whose Meyer--Maslov cocycle sum is `1 mod 3`, and seek
  a sum-of-squares inequality converting that nonzero curvature into a lower
  bound for the relator HS energy.  The certificate must be trace-density
  sensitive; bare determinant divisibility is not enough.
- **Finite-subgroup cone atlas.** Exactify bounded torsion-subgroup tables by
  Gowers--Hatami and search for a rational positive-cone separation among
  projective irreducible multiplicities on overlaps.  A valid certificate must
  force positive-density mismatch, not merely a dimension congruence.
- **No tracial-positivity shortcut.** The twisted left-regular representation
  exists in infinite dimension, so a moment/SOS certificate valid in every
  tracial von Neumann algebra cannot exclude `alpha`.  Any separator must use
  genuinely finite-dimensional structure.
- **Falsification.** Direct nonlinear optimization in increasing dimensions
  should be run first.  If the minimum projective relator energy visibly
  decays toward zero, this claim is false and the Deligne lane must use a
  weaker positive-density/trace obstruction rather than a full sector gap.
