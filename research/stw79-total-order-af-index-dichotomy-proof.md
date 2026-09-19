---
rg: 2
id: stw79-total-order-af-index-dichotomy-proof
kind: route
title: Combine Schochet relative quasidiagonality with the projectional extension maximum
target: stw79-total-order-af-index-dr-dichotomy
requires: []
artifacts:
  - research/artifacts/stw79-index-dichotomy-2026-09-04.md
---

The artifact proves the stated result with explicit source hypotheses.
Schochet, Theorem 3.5, applies because `D` is nuclear UCT and is
quasidiagonal relative to `B` (finite decomposition rank implies ordinary
quasidiagonality; Schochet's discussion on p. 96 supplies the relative
version). The other boundary map lands in `K_1(B)=0`. The relevant UCT
extension group is `Ext^1(K_0(D),K_0(B))`: its classes are all pure because
`K_0(D)` is torsion-free. Thus the theorem's purity condition is automatic,
without any assumption on `K_1(D)`.
Consequently `delta=0` supplies an approximate unit of projections in
`J` quasicentral in the actual extension `E`. Kirchberg--Winter's
quasidiagonal-extension maximum gives `dr(E)=max(0,d)=d`.

Conversely, a nonzero subgroup of the totally ordered `K_0(B)` contains a
nonzero positive element. If it lies in `im(delta)`, exactness kills the
class of a nonzero ideal projection in `K_0(E)`. The definition of the
Grothendieck group then produces a projection equivalent to a proper
subprojection in a matrix algebra over `E`. Hence `E` is not stably finite
and cannot have finite decomposition rank or be quasidiagonal. This proves
all equivalences, with strong quasidiagonality supplied by finite
decomposition rank.

Simplicity of `J,D` and essentiality give the three-element ideal chain.
Both simple factors are non-elementary, so the algebra is nowhere
scattered. Winter--Zacharias' general extension estimate gives
`dim_nuc(E)<=0+d+1`. None of these steps assumes the open extension maximum
for nuclear dimension.
