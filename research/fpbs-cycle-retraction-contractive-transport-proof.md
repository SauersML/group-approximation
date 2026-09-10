---
rg: 2
id: fpbs-cycle-retraction-contractive-transport-proof
kind: route
title: Use the polar unitary on the surviving module and telescope the deleted-cycle cost
target: fpbs-cycle-retraction-contractive-transport
requires:
  - fpbs-relative-cycle-operator-descent
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-iteration.md
---

Section 2 supplies the operator proof. The deleted-edge module is
boundedly isomorphic to ker R. On its orthogonal complement, R is
bijective onto the retained edge module and its inverse is a
contraction. Polar decomposition gives a unitary U and |R|>=I on
this restricted domain. Transporting the compression of K by U
preserves positivity and the upper bound by I, while its trace is
Tr(K)-Tr(P_W K) and is at most Tr(R K R-star).

For cycle-supported K, restrict the polar decomposition to
Z(H) intersect W-perp. Finite path replacements give W contained
in Z(H) and R Z(H)=Z(J), so the resulting contraction is supported
on Z(J). Dimension invariance and trace splitting give the exact
cost identity. Section 3 proves its iteration and initializes it
using the required relative-operator trace identity. The proof
does not invoke or assert the missing trace-decay estimate.
