---
rg: 2
id: folner-multiplicity-atlases-have-vanishing-first-exit
kind: claim
title: Every fixed conductor stencil has exact rectangular atlases with vanishing first-exit mass
distinct_from:
  fixed-shift-invariance-does-not-force-flat-profile: that constructs non-Haar probability profiles which are almost translation invariant; this realizes those profiles as exact finite-dimensional isotypic atlases with equal-trace carriers and coherent partial intertwiners.
  weyl-kernel-joins-descend-two-levels-without-mass-contraction: that shows abstractly that shallow quotient mass need not contract; this gives the literal finite-rank rectangular transport architecture and computes its first-exit projections.
  polar-compression-turns-band-mismatch-into-first-exit: that bounds support loss for a compressed raw unitary; this shows that even ideal coherent supports can have total loss tending to zero without producing a fixed contraction.
---

Let `T_N=(Z/(N+1)Z)^2`, let `nu_N=mu_N tensor mu_N`, where

```text
mu_N(k)=2(k+1)/((N+1)(N+2)),                           (FSM1)
```

and fix a finite translation stencil `F subset Z^2` containing `0`.  There are exact
finite-dimensional representation atlases indexed by `g in F` with:

1. rational isotypic weights `nu_N(x-g)` in chamber `g`;
2. equal-trace carrier projections `R_g`;
3. exact partial intertwiners `V_(h,g):R_g -> R_h` which compose
   coherently on their common source; and
4. total first-exit mass bounded by

```text
1-tau(R_g)
 <= sum_(g in F) TV(nu_N,shift_g(nu_N))
 <= C_F/(N+1).                                         (FSM2)
```

In particular `tau(R_g)->1` for every fixed stencil.  The same construction
can be tensored with the four-atom algebra carrying two independent half
projections, so a fixed positive interior-overlap mass survives on all the
carriers while every conductor first-exit mass tends to zero.

Consequently no estimate of the form

```text
m_next <= (1-kappa)m+C_F firstExit,                    (FSM3)
```

with `kappa>0` independent of scale, can follow from equal carrier traces,
finite-stencil Schur matching, coherent partial transitions, and conductor
descent alone.  A contraction in the arithmetic hexagon decoder must use an
additional arithmetic input which is absent from this rectangular atlas:
the mixed-root/role-rotation relations must make the scale-type graph
non-Folner on the marked lamp sector, or an equivalent same-reservoir
multiplicity invariant must charge the surviving common carrier.

This is a no-go for a proposed *derivation* of `(AHD2)` from leakage alone,
not a countermodel to the full `SL_3(Z[1/2])` relation packet.  The latter
may still supply exactly the missing non-Folner payment.

The width growth is necessary and quantitatively sharp.
`bounded-conductor-width-pays-uniform-first-exit` proves that a profile on at
most `B` conductor depths loses at least `1/B` under a unit shift.  Thus the
present triangular atlases, with width `N+1` and loss `O(1/N)`, realize the
optimal order of rectangular escape rather than an artifact of the chosen
weights.
