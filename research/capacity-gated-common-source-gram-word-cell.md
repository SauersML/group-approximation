---
rg: 2
id: capacity-gated-common-source-gram-word-cell
kind: claim
title: Decode one capacity-gated source Gram projection shared by every Fanizza context
distinct_from:
  capacity-gated-common-corner-bcs-two-cell: that proves the analytic implication from a common source to the full localized BCS functional; this asks for the finite ordinary-word packet whose compressed intertwiners have that common source.
  context-local-fanizza-exits-do-not-control-global-leakage: that gives a Bass--Serre countermodel when the context sources rotate independently; this requires literal equality of the decoded source Gram projection before the context split.
  three-book-hnn-antiphase-charges-every-cross-gram: that supplies the complete overlap payment after leakage has been localized; this supplies the remaining leakage localization and does not impose any tag holonomy.
---

OPEN.  For each returned exit `E_i` and common capacity cut `C`, put

```text
Q_i=(1-C)E_i.                                             (CSG1)
```

Construct a fixed finite packet of ordinary group words which, in every
sufficiently accurate finite-dimensional tuple after fixed-packet
exactification, decodes for every original Fanizza context `c` partial
intertwiners and allowed target observables

```text
V_(i,c)^*V_(i,c)=Q_i+o(1),
A_(i,c,x)V_(i,c)=V_(i,c)Z_x+o(1)       (x in U_c),       (CSG2)
```

with the **same** source `Q_i` for all `c`, and with

```text
sum_(i,c,x)||A_(i,c,x)V_(i,c)-V_(i,c)Z_x||_2^2
 +sum_(i,c,R)||R(A_(i,c))V_(i,c)||_2^2
 <= K_cell E_rel+o(1).                                   (CSG3)
```

The constant may depend on the fixed finite Fanizza instance but not on
matrix dimension.  Equations `(CGC4)` and `(CGC11)` of
`capacity-gated-common-corner-bcs-two-cell` then give

```text
Lambda<=K_B K_cell E_rel+o(1),                           (CSG4)
```

which is exactly `(NCL13)` / `(SFEL2)`.

The source-Gram equality in `(CSG2)` is load-bearing.  One context-private
projection `Q_(i,c)` per context is defeated by the exact virtually-free
countermodel in
`context-local-fanizza-exits-do-not-control-global-leakage`.  Likewise,
shared variable names without a shared multiplicity source do not imply
`(CSG2)`.

This target passes the exact-witness firewall.  In a perfect HALT model the
relevant forbidden exits vanish, so every `Q_i` and `V_(i,c)` may vanish.  In
the exact non-CE tracial model, the analytic two-cell itself is consistent
with `Q=I`; only matrix embeddability makes the localized corner impossible.
Thus the desired word packet must decode the common source in matrices, but
it need not impose a universal proper-corner identity in the group algebra.

The smallest prospective packet is one word-visible capacity/source Gram
moment, one context-intertwiner row for each of the four native contexts, and
one two-cell identifying their source supports.  The leaf context `C_X` must
participate: synchronizing only the `C_Z-C_D-C_R` triangle leaves the exact
leaf-rotation countermodel alive.

## Finite-edge and Leavitt audits

Two natural implementations have now been sharply fenced.

- `isotypic-finite-edge-forces-full-commuting-selector-support` proves that a
  common finite HNN edge type cannot have zero-loss source-Gram saturation
  into a proper nonlinear predicate type when the logical selectors commute
  with the edge.  The selected target type itself then contains every
  compatible selector character.  Gauge doubling is inside this no-go
  because its logical products are fixed by the gauge edge.
- `common-source-leavitt-cell-inherits-rectangular-root-escape` shows that a
  relative Leavitt coefficient cell gives the formal common source exactly,
  but a fixed collection of Steinberg root Fourier tables still admits the
  four-target rectangular label-expansion/multiplicity-contraction model.
  The Leavitt syntax closes this claim only after the same-reservoir scalar
  saturation estimate `(CLR6)` is proved.

Thus neither a larger logical-invariant finite packet nor a one-level root
table removes the load-bearing scalar.  A successful construction must make
the capacity-gated source matrix-only, carry nontrivial selector action in
the edge/holonomy, or prove a normalized-HS boundary payment excluding
rectangular enlargement.
