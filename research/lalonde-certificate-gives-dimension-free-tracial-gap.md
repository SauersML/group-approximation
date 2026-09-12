---
rg: 2
id: lalonde-certificate-gives-dimension-free-tracial-gap
kind: claim
title: Lalonde's rational tracial certificate gives a finite dimension-free tracial gap
artifacts:
  - research/artifacts/paulsen-harris-lalonde-tang-macmahon-source-audit-2026-08-23.md
distinct_from:
  lalonde-perfect-fd-strategy-has-no-tracial-game-state: that is the state-conversion fence; this extracts the positive normalized-HS gap available on the forbidden tracial face.
  tracial-npa-cannot-separate-canonical-trace: that rules out separating a feasible canonical group trace by standard tracial NPA; Lalonde's prescribed perfect tracial face is empty, so a finite tracial certificate can separate it.
  group-sos-certificate-survives-hs-adjoint-microstates: that transports an already word-valued group-algebra certificate; this certificate is still expressed in the game effect algebra and needs a group compiler.
---

**DERIVED CONSEQUENCE (Lalonde, arXiv:2608.05378v1, Section 4.2).**
Let `E_a^x,F_b^y` range over finite-matrix positive effects satisfying the
POVM and cross-commutation relations from Lalonde's game, and set

```text
Loss(E,F)=sum_((x,y,a,b) losing) w_(xyab) tr(E_a^x F_b^y), (LTG1)
```

with any strictly positive rational weights on the finitely many losing
events.  There is a constant `eta_L>0`, independent of matrix dimension,
such that every exact finite-matrix tracial tuple has

```text
Loss(E,F) >= eta_L.                                    (LTG2)
```

The same conclusion holds with a smaller positive constant when the
POVM and commutation relations have sufficiently small normalized-HS
defect.

Indeed, Lalonde's strengthened level-four tracial-NPA relaxation has an
exact rational dual infeasibility certificate.  In particular there is no
tracial state satisfying the algebra relations and annihilating every
losing product.  If `(LTG2)` failed, a sequence of finite matrix tuples
with loss tending to zero would yield, in a tracial matrix ultraproduct, a
trace on precisely that forbidden perfect face.  The approximate-relation
version follows by the same ultraproduct argument.  The rational dual can
in principle make the resulting inequality explicit.

This is already a universal normalized-HS obstruction on the **tracial
game algebra**.  It is not yet a group obstruction.  Lalonde's perfect
finite-dimensional strategy uses a nonmaximally entangled vector state,
so the positive completeness witness and the negative tracial certificate
live on different state faces.
