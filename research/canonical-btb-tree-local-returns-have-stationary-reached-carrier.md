---
rg: 2
id: canonical-btb-tree-local-returns-have-stationary-reached-carrier
kind: claim
title: Seed-support-preserving tree-local BTB returns admit an exact stationary canonical reached carrier
distinct_from:
  btb-three-line-tree-retains-multiplicity-return-gauge: That aligns the Schur multiplicity gauge on arbitrary packet-reducing carriers and records the complete-S3 outer exception; this applies the alignment to the fixed protected seed only when the authenticated outer factor preserves its selected type support.
  hyperlinear-fiber-cannot-orient-btb-return: That uses a proper spectator subcarrier and therefore leaves a path-specific loophole; this uses the full canonical seed itself and closes that loophole only for seed-support-preserving tree-local returns.
  canonical-btb-finite-depth-escape-tree: That still permits cross-edge or payload-sensitive two-cells and one-shot outer-type escape; this refutes only seed-support-preserving returns whose rows separate edge by edge and have no multiplicity-charged cross-edge relation.
---

**ESTABLISHED SEED-SUPPORT-PRESERVING NO-GO.**  Fix any finite protected
adaptive BTB tree.  Suppose every proposed return is in the edge-local
Schur-gauge language of
`btb-three-line-tree-retains-multiplicity-return-gauge`: finite packet and
finite-subgroup covariance, one stabilized three-line/Murray--von Neumann
swap, and relations involving that edge intertwiner alone, with no word
containing two adaptive-edge intertwiners and no payload operator acting
nontrivially on their common multiplicity space.

There is one necessary outer-support hypothesis.  On every authenticated
packet type carrying the conditioned source in `e_0`, the fixed outer
intertwiner must admit its matching target object in the same `e_0`-selected
protected-sign support.  In Schur notation, if

```text
W_lambda=C_lambda tensor U_lambda,                    (CTS0)
```

then the finite outer factor `C_lambda` must send the source cut occurring
in `e_0` to a target cut which also occurs in `e_0`; only the anonymous
multiplicity reservoir may remain to be chosen.  Call such a return
**seed-support-preserving**.

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
gadget in this seed-support-preserving tree-local language, even when
`(CBR3)` is required only on the prescribed minimal-hull path rather than on
arbitrary reducing subcarriers.

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

By the seed-support-preserving hypothesis, `C_lambda` does not move the
conditioned source outside the finite outer support selected by `e_0`.  The
rectangular three-line model places its matching source and range objects
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
In particular, it does **not** cover the complete irreducible `S_3` outer
action singled out in
`btb-three-line-tree-retains-multiplicity-return-gauge`: its second
reflection can send an `e_0`-selected outer type to an unselected type, and
no choice of `U_lambda` repairs that finite outer displacement.  That packet
can force one genuine outer-type escape.  Its complete two-dimensional
orbit is then contained in the next reducing hull, so the same palette does
not renew the escape; independent fresh palettes return to the prepaid
character-capacity obstruction.  The present theorem neither reproves nor
strengthens that separate one-shot analysis.

It proves only that an oriented return cannot come from another
seed-support-preserving Schur-gauge edge.  A reusable live candidate must
instead contain a multiplicity-charged word coupling at least two adaptive
edges, a genuinely payload-sensitive proper-corner row, or a finite outer
action together with a non-prepaid renewal mechanism.  By
`coupled-reflections-reduce-to-the-active-gauge-profile`, such a row must
then be audited on its active gauge presentation; merely adding another
seed-support-preserving packet, torsion clause, or separate HNN edge remains
inside the exact countermodel above.

DERIVATION
canonical-btb-tree-local-stationary-seed-proof
