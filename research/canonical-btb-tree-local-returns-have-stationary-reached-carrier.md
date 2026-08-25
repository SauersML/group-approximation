---
rg: 2
id: canonical-btb-tree-local-returns-have-stationary-reached-carrier
kind: claim
title: Tree-local protected BTB returns admit an exact stationary canonical reached carrier
distinct_from:
  btb-three-line-tree-retains-multiplicity-return-gauge: That aligns the Schur multiplicity gauge on arbitrary packet-reducing carriers; this applies the alignment to the fixed protected seed and proves inductively that the actual minimal-hull recursion stays stationary.
  hyperlinear-fiber-cannot-orient-btb-return: That uses a proper spectator subcarrier and therefore leaves a path-specific loophole; this uses the full canonical seed itself and closes that loophole for the tree-local return language.
  canonical-btb-finite-depth-escape-tree: That still permits cross-edge or payload-sensitive two-cells; this refutes only packets whose return rows separate edge by edge and have no multiplicity-charged cross-edge relation.
---

**ESTABLISHED TREE-LOCAL NO-GO.**  Fix any finite protected adaptive BTB
tree.  Suppose every proposed return is in the edge-local language of
`btb-three-line-tree-retains-multiplicity-return-gauge`: finite packet and
finite-subgroup covariance, one stabilized three-line/Murray--von Neumann
swap, and relations involving that edge intertwiner alone, with no word
containing two adaptive-edge intertwiners and no payload operator acting
nontrivially on their common multiplicity space.

Then the resulting packet/covariance/return subsystem has an exact
finite-dimensional specialization in which the protected seed

```text
e_0=(1-J)/2 (1+B)/2 (1-ell)/2                         (CTS1)
```

is nonzero, a chosen structural forbidden atom is nonzero, and the **actual
canonical reached carrier** is stationary:

```text
Q_sigma=e_0                                             (CTS2)
```

at every node on one reached branch.  If `F_sigma` is the positive
BTB--E5 conditioned part of that atom and `D_sigma` is its proposed returned
range, then

```text
0<tau(F_sigma),       D_sigma<=Q_sigma,
tau(Q_sigma D_sigma Q_sigma)=tau(F_sigma).              (CTS3)
```

Thus no positive overlap loss `(CBR3)` follows from any finite ordinary-group
gadget in this tree-local language, even when `(CBR3)` is required only on
the prescribed minimal-hull path rather than on arbitrary reducing
subcarriers.

To see this, use the positive regular stationary packet multiplicities at
all vertices and choose a scalar shared-BCS assignment which makes one
forbidden atom equal to one.  The regular protected sign table makes `e_0`
nonzero and gives positive multiplicity to every negative-center packet type
used by the BTB--E5 cut.  Since all shared BCS letters and all packets in the
carrier menu commute with `J,B,ell`, `e_0` already reduces that entire menu.

On each packet type, the edge return has Schur form

```text
W_lambda=C_lambda tensor U_lambda.                     (CTS4)
```

The rectangular three-line model places matching source and range objects
over the same multiplicity projection.  Choose `U_lambda` to preserve the
`e_0` multiplicity reservoir.  The tree has no cross-edge holonomy row, so
these choices can be made independently from the root outward while all
edge-local relations remain exact.  This gives `D_empty<=e_0`.  Consequently

```text
Hull(e_0 join D_empty)=e_0,                             (CTS5)
```

because `e_0` is already reducing.  The same Schur-gauge choice at the next
edge gives the induction `(CTS2)--(CTS3)` through the entire finite branch.

This is stronger than the usual spectator-amplification objection: the
countermodel does not replace a reached carrier by a proper invariant half.
It evaluates the recursion on its full fixed seed, and every child is the
minimal reducing hull specified by the construction.

The result does not refute `canonical-btb-finite-depth-escape-tree` itself.
It proves that its oriented return must leave the tree-local class.  A live
candidate must contain a multiplicity-charged word coupling at least two
adaptive edges or a genuinely payload-sensitive proper-corner row.  By
`coupled-reflections-reduce-to-the-active-gauge-profile`, such a row must
then be audited on its active gauge presentation; merely adding another
finite packet, torsion clause, or separate HNN edge remains inside the exact
countermodel above.

DERIVATION
canonical-btb-tree-local-stationary-seed-proof
