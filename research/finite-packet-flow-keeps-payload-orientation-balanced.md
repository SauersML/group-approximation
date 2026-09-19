---
rg: 2
id: finite-packet-flow-keeps-payload-orientation-balanced
kind: claim
title: Finite packet flow cannot create the payload-oriented HNN imbalance
distinct_from:
  finite-packet-functoriality-has-positive-regular-profile: That constructs an interior regular multiplicity solution for arbitrary finite packet diagrams; this applies it to the balanced-HNN conditional-gap functional on a packet-reducing payload carrier.
  orientation-graded-mixed-returns-have-a-balanced-double: That uses one surviving orientation character; this also covers finite diagrams with orientation permutations and central selector cuts through their regular stationary profile.
  balanced-hnn-conditional-gap-forces-carrier-escape: That proves escape from an already supplied conditional imbalance; this gives the exact finite-flow countermodel in which every such packet-only imbalance is zero.
---

**ESTABLISHED FINITE-FLOW FIREWALL.**  Fix a finite diagram of finite packet
groups, subgroup restrictions, character cuts, conjugacies and HNN edge
isomorphisms.  Allow the diagram to share the finite context Reynolds groups
which name BCS assignment atoms.  Suppose every proposed exit edge uses
globally balanced source and target character projections `p_s,p_t`; thus
their canonical finite-packet traces agree.

There is an exact finite-dimensional stationary packet model in which:

1. every base irreducible packet/selector type has positive multiplicity;
2. every restriction, cut and edge matching in the finite diagram is exact;
3. the packet-reducing carrier `Q_reg` contains the full regular multiplicity
   profile in the protected central-sign sector; and
4. for every balanced edge,

   ```text
   tau(Q_reg p_s)=tau(Q_reg p_t).                      (FPO1)
   ```

Take the common regular profile

```text
m_(a,pi)=D dim(pi)/|F_a|                               (FPO2)
```

with `D` divisible by all packet orders, and use the induced auxiliary
multiplicities for every restriction and central cut.  This is compatible
with every edge isomorphism.  On the full protected regular carrier,
evaluation of a finite group-algebra projection has its canonical trace, so
global balance gives `(FPO1)`.

Tensor this packet model with any exact finite-dimensional **structural** BCS
tuple.  Such a tuple need not satisfy the forbidden equations; choose one for
which some forbidden Reynolds atom is nonzero.  The tensor carrier reduces
the shared BCS tuple and the whole finite packet diagram, and the selected
forbidden atom has positive mass.  Nevertheless every packet-only candidate
for `(BHC4)` has zero left side by `(FPO1)`.

The same conclusion holds when an orientation grading survives, by taking
the balanced double, and when finitely many orientation types are permuted:
the regular profile is invariant under those permutations.  Breaking one
grading by the standard odd selector also does not help, because its exact
balanced model is one of the stationary packet blocks.

Therefore no proof using only finite packet restriction data, central
selector cuts, balanced character HNN edges, and their finite flow equations
can derive a uniformly positive payload-oriented conditional gap.  The
companion mass required by global regular trace remains inside the same full
packet-reducing carrier.

This is a local decoder countermodel, not automatically a model of the full
protected adaptive group: path-specific infinite coefficient relations may
exclude the stationary packet block on the actual canonical reached hull.
It proves what those relations must accomplish.  They must couple the
forbidden Reynolds payload to a **nonstationary** orientation coordinate or
proper-corner return.  Adding a larger finite packet, more character cuts, or
more balanced HNN edges preserves `(FPO2)` and cannot create the scalar gap.

DERIVATION
finite-packet-payload-orientation-flow-proof

