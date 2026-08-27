---
rg: 2
id: finite-tag-covariance-cannot-compress-eight-slice-orbit
kind: claim
title: Finite tag covariance cannot compress the equal-rank failure orbit into its smaller parent
distinct_from:
  disjoint-tag-covariance-controls-cross-gram: that usefully charges approximate overlap once a common target representation and branch maps have been decoded; this proves that exact finite tags cannot also manufacture a target whose capacity is smaller than the summed sources.
  exact-five-fourths-projection-return-collapses-the-packet: that uses canonical trace directly for the unequal five-fourths projections; this gives the representation-theoretic obstruction for the equal-rank eight-slice orbit and any finite tag refinement.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that treats arbitrary finite restriction graphs; this isolates the elementary Schur-orthogonality mechanism at the proposed common target.
---

Let `H` be finite, let `pi_i:H->U(V_i)` be pairwise disjoint finite
representations, and let `rho:H->U(K)`.  If isometries `T_i:V_i->K` satisfy

```text
rho(h)T_i=T_i pi_i(h)                 (h in H),         (FTC1)
```

then their ranges are pairwise orthogonal and

```text
dim K >= sum_i dim V_i.                                  (FTC2)
```

Indeed, `T_i^*T_j` is an `H`-intertwiner from `pi_j` to `pi_i`, hence is
zero for `i!=j`; equivalently the range projections are orthogonal.

Apply this to the three sources `G_00,G_01,G_11` of the eight-slice packet.
Giving their disjoint bookkeeping characters pairwise inequivalent finite
tags makes `(FTC1)` force target capacity at least

```text
sum_b tau(G_b)=3 tau(P_f)/16.                           (FTC3)
```

But the intended parent slice has trace only `tau(P_f)/8`.  Therefore no
exact finite tag representation on that parent can realize all three branch
isometries.  Enlarging the parent to contain the three tag types removes the
contradiction by increasing its capacity to at least `(FTC3)`.

Consequently the three-bit book does exactly one job: it makes the actual
failure sources an equal-rank symmetry orbit.  Its character table cannot
also provide the strict return.  A literal finite-group covariance cell
would either destroy the embedded packet in the regular representation or
allocate enough complementary target types to restore stationary flow.  The
return in `shared-bcs-eight-slice-symmetric-return` must still be selected
only in Connes-embeddable finite-matrix models, or use a genuinely one-sided
infinite actuator whose exact marked witness is nontracial.
