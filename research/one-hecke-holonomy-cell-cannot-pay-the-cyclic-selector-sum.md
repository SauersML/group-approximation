---
rg: 2
id: one-hecke-holonomy-cell-cannot-pay-the-cyclic-selector-sum
kind: claim
title: One Hecke multiplicity-holonomy cell cannot pay a cyclic coarse-to-fine selector sum
distinct_from:
  matrix-only-cyclic-carrier-invariance: that shows a product of the mixed selector row errors can cancel and that pure transport words do not locate fine atoms; this allows the two-cell to constrain the actual transport holonomy and proves that the last free edge gauge closes it while the selector pressure is unchanged.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs positive regular vertex and edge multiplicities before any two-cell is attached; this extends that stationary model across one square multiplicity-holonomy cell and compares its zero word energy directly with the cyclic selector sum.
  proper-packet-rank-growth-needs-compressed-two-cell: that isolates a compressed unequal-carrier return as the surviving interface; this proves that a two-cell which sees only the uncompressed product of edge intertwiners is still flat and therefore does not supply that interface.
  hecke-coset-quarter-selector-is-either-untyped-or-rank-preserving: that obstructs authenticating a quarter selector by a single finite edge; this gives the independent multi-edge obstruction even when analytic half and quarter cuts have already been chosen on every carrier.
---

**ESTABLISHED.**  A single closed Hecke transport holonomy, including one
whose edges are written as partial-swap involutions, cannot imply `(GTC4)` of
`global-marked-type-cycle-selector-decoder`.

The obstruction already occurs on one multiplicity block.  Let
`i in Z/kZ`, let `P_i` be nonzero finite-dimensional carriers, and choose

```text
e_i,f_i<=P_i,       tr(e_i)=tr(P_i)/2,
                    tr(f_i)=tr(P_i)/4.                (HHC1)
```

Assume the finite packet edges have been exactified and their label
intertwiners fixed.  On a matched isotypic block, every remaining edge
intertwiner has the form

```text
T_i=T_i^0 tensor V_i,                                  (HHC2)
```

where `V_i` is an arbitrary unitary on the common external multiplicity
space.  Suppose the only extra two-cell on this cycle prescribes the closed
multiplicity holonomy

```text
V_(k-1)...V_1V_0=W                                    (HHC3)
```

for one fixed unitary `W` (a scalar phase and a fixed finite packet operator
are included).  Choose `V_0,...,V_(k-2)` arbitrarily and set

```text
V_(k-1)=W(V_(k-2)...V_0)^(-1).                         (HHC4)
```

Then every packet edge and the two-cell are exact.  In particular their
ordinary word energy is zero.

On the other hand, for the decoded transport unitaries `U_i` obtained from
`(HHC2)`, the cyclic coarse--fine inequality is insensitive to all the
`V_i` and gives

```text
sum_i ||U_i e_i U_i^*-f_(i+1)||_2^2
  >=(1/4)sum_i tr(P_i)>0.                              (HHC5)
```

Thus no estimate

```text
sum_i ||U_i e_i U_i^*-f_(i+1)||_2^2
 <=K E_(edges+one_holonomy_cell)+eta(delta),           (HHC6)
```

with `eta(0)=0` can hold for this actuator.

## Exact finite packet countermodel

This is not merely a choice of abstract matrices.  Start with a cycle of
finite packet groups and take the positive regular stationary vertex modules
from `finite-packet-graph-atlases-have-a-regular-stationary-flow`.  Their edge
restrictions agree with a common positive integral multiplicity on every
irreducible edge type.  Choose all edge intertwiners on one such type by
`(HHC2)--(HHC4)` and arbitrarily on the other types.  The stable-letter
relations and the single attaching word are then represented exactly in a
finite matrix algebra.  Every regular packet type, hence every marked type
present in the chosen finite selector menu, still has positive multiplicity.

Writing an edge by its partial-isometry swap does not alter the argument.
Replacing `T_i` by

```text
J_(T_i)=[[1-T_iT_i^*,T_i],
          [T_i^*, -(1-T_i^*T_i)]]                     (HHC7)
```

is functorial under multiplication of the free multiplicity gauge.  The last
gauge in `(HHC4)` still closes the sole holonomy equation.  A Gram condition
which merely certifies each edge block as a partial isometry likewise leaves
the `V_i` free and does not affect `(HHC5)`.

## Boundary left by the countermodel

The established forbidden-weighted rank trimming for `(GTC5)` does not
repair this actuator.  It chooses the carriers and their half/quarter cuts
analytically inside `F_cQ_omega`; it imposes no equation on the last edge
gauge.  Likewise the one-Gram bound

```text
||F_cS_D8||_2^2<=tr(F_c)                               (HHC8)
```

shows that a valid `(GTC4)` would pay the game energy, but it does not make an
uncompressed transport holonomy selector-sensitive.

Consequently a positive two-cell must expose more than the product
`V_(k-1)...V_0`.  It must compress at least two intermediate stages by the
actual forbidden-weighted selector cuts, or impose a genuinely
matrix-coordinate condition for which the last-gauge assignment `(HHC4)` is
not available.  This is the smaller remaining interface: ordinary Hecke
transport, one partial-isometry/Gram certificate per edge, and one closed
holonomy word still do not dominate the sum of mixed selector rows.
