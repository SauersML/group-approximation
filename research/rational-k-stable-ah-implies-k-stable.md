---
rg: 2
id: rational-k-stable-ah-implies-k-stable
kind: claim
title: Rational K-stability implies K-stability for AH algebras (Vaidyanathan's AH extension question)
root: true
refuted_by:
  - rational-k-stable-simple-ah-torsion-counterexample
artifacts:
  - research/artifacts/rational-k-stability-ah-literature-boundary-2026-09-05.md
  - research/artifacts/stw59-rational-k-stability-torsion-euler-tower-2026-09-05.md
---

Published question: does rational K-stability imply integral K-stability
for an AH algebra, interpreted using compact homogeneous building
blocks? Vaidyanathan raises the AH extension of the AF/AT equivalence
in Section 20, printed page 48, of
[Sarkar's compendium](https://www.isibang.ac.in/~jay/papers/oaotINSA.pdf).
The simple unital twisted-AH case is a narrower target.

The internally reviewed construction
[rational-k-stable-simple-ah-torsion-counterexample](rational-k-stable-simple-ah-torsion-counterexample.md)
answers negatively even in that narrower class. Its simple unital
monotracial AH algebra A is rationally K-stable but has integral
stabilization kernel Z/2, while M_2(A) is K-stable. This graph status
records the full manuscript and internal review, not external peer
acceptance, formal verification, or a priority certification.

Rational K-stability concerns all positive homotopy degrees and all
adjacent matrix inclusions after rationalization. Integral K-stability
also includes degree zero. A torsion component obstruction alone
does not establish rational K-stability in positive degrees.

The AT case is settled positively. Simple unital infinite-dimensional
ordinary diagonal AH algebras are K-stable by Seth's tensorial
permanence theorem. The published pointed-RP2 counterexample for
general C*-algebras is nonunital and projectionless, so it is not an
AH limit of compact unital homogeneous blocks under this convention.
Unitization destroys its rational K-stability.

## Attempts

The earlier complex-projective Euler towers are not rationally K-stable: their free
degree-one stabilization cokernel survives rationalization. A torsion
replacement must preserve an integral obstruction under
simplicity-producing maps and verify rational stability in every
positive degree. The new proof does both: real-projective factors
give rationally acyclic bases, a mod-two fourth-power identity kills
all Euler relations including torsion contributions, and the
integral Thom product preserves the top Z/2 class through the
actual twisted maps with dense evaluation tails.
