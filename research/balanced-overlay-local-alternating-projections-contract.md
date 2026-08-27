---
rg: 2
id: balanced-overlay-local-alternating-projections-contract
kind: claim
title: Balanced-overlay face and equality projections contract uniformly inside the operator tube
distinct_from:
  quadratic-overlay-has-uniform-linearized-synchronization-gap: that is an infinitesimal Jacobian estimate at an exact representation; this turns it into a nonlinear uniform contraction for the actual local-face/equality alternating scheme inside a fixed tube.
  balanced-overlay-diffuse-square-function-newton: that must enter the tube from only a diffuse row-square-function bound; this proves that no limit cycle or nonlinear loss remains after tube entry.
  complete-pair-overlay-uniform-hs-basin-capture: that asks to enter a uniform tube from small average defect; this analyzes the concrete alternating exactification maps after tube entry.
---

Let `A_L` be the product of the exact fixed-face varieties in the balanced
repeated presentation: every original parity face and every complete-pair
face is an exact bounded-size binary PVM, with occurrence variables still
separate.  Let `B_L` be the exact equality-cloud variety: all copies in each
logical cloud are one shared reflection.  Their intersection `Z_L=A_L cap
B_L` is the exact shared code-representation variety.

There are constants `r>0`, `0<rho<1`, and `C<infinity`, independent of code
length, matrix dimension, character multiplicities, and the exact base
point, with the following property.  In the operator-norm `r`-tube of
`Z_L`, choose the nearest fixed-multiplicity local metric projections
`Pi_A,Pi_B`.  One full alternating sweep satisfies

```text
dist_2(Pi_B Pi_A(x),Z_L) <= rho dist_2(x,Z_L),             (LAP1)
```

and its total squared normalized-HS movement is at most

```text
C dist_2(x,Z_L)^2.                                        (LAP2)
```

The same conclusions hold with the order of the two projections reversed.
Consequently the proposed face-exactify/equality-synchronize iteration has
no nontrivial limit cycle, multiplicity drift, or loss of transversality
inside this tube; it converges geometrically to one exact shared code PVM.

The operator-tube hypothesis is essential.  The result does not establish
`balanced-overlay-diffuse-square-function-newton`: a low average residual
square function does not identify an exact base point or put every local
coordinate in this tube.  The remaining cb row-quadratic/BMO problem is
therefore precisely global basin entry, rather than convergence of the
local alternating scheme once a basin has been selected.
