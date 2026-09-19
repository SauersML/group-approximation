---
rg: 2
id: btb-three-line-tree-gauge-no-go-proof
kind: route
title: Put the protected BTB--E5 fiber in Schur form and align every tree-edge gauge
target: btb-three-line-tree-retains-multiplicity-return-gauge
requires:
  - binary-tetrahedral-conditional-e5-root-bridge
  - e5-idempotent-root-has-two-pair-extraspecial-cell
  - fixed-packet-correction-retains-multiplicity-gauge
  - literal-prefix-three-root-swap-retains-typed-carriers
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
---

Exactify the fixed protected packet and decompose its representation into
irreducibles.  The commutant formula gives `(BTR1)`, and every finite packet
Fourier cut has fixed outer matrix coordinates, giving `(BTR2)`.  Apply the
BTB half-root estimate and then the E5 two-pair `1/9` estimate to see that
the relevant outer cuts are nonzero and retain the advertised `1/18` mass.

The three-line swap identifies only the matching finite source and range
types.  By the fixed-packet Schur theorem its restriction is `(BTR3)`, while
the typed-carrier countermodel says that neither object identity is forced
to equal a prescribed analytic carrier.  Realize both matching objects over
the same multiplicity projection and choose the free gauge to preserve that
projection.  This proves `(BTR4)`.

For finitely many edges, take common regular multiples of every finite
vertex packet.  Their edge restrictions agree by the stationary-flow
formula.  A tree has no holonomy equation, so the preceding gauge choices
can be made independently from the root outward.  Amplifying and using the
same finite-window regular gauge character on the carrier and its complement
shows that adding fixed canonical packet moments does not distinguish the
aligned ownership.  This proves the claim.

