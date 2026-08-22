---
rg: 2
id: fanizza-same-letter-compressed-row
kind: claim
title: Force one positive-density Fanizza same-letter row across a wandering HNN edge
distinct_from:
  capacity-gated-common-source-gram-word-cell: that asks one Gram projection to carry every Fanizza context and the full localized BCS leakage functional; this asks for one same-letter rectangular row and does not require a common reducing projection.
  fanizza-coherent-verifier-wandering-promotion: that wordizes the complete coherent verifier reflection on a named packet corner; this asks only for one compressed intertwining residual and permits its returned range projection to vary with the matrix model.
---

**OPEN MINIMAL WANDERING-PROMOTION ROW.**  Construct a finitely presented
Fanizza/non-CE base `B`, finite associated subgroups `A,C`, a stable letter
`t` with `tAt^(-1)=C`, a base word `a in B\(A union C)`, and a fixed packet
projection `p in C[B]` such that:

1. `[a,p]=0` and canonical packet exactification gives
   `tau(p_U)>=alpha-o(1)` for one fixed `alpha>0`;
2. every canonical-trace matrix microstate satisfies

   ```text
   ||a(U)t(U)p_U-t(U)p_Ua(U)||_2=o(1);                (FSC1)
   ```

3. the exact marked/non-CE representation needed to prove the base and
   packet are noncollapsed extends to the HNN presentation.

By `hnn-compressed-row-is-unnamed-fixed-carrier`, the commutator

```text
u=a t a^(-1)t^(-1)
```

has infinite order and `(FSC1)` makes the moving projection `t p_U t^*` an
approximate fixed space of density `alpha`.  The Fejer endpoint then proves
non-hyperlinearity.  No verifier reflection, packet-return equality, polar
part, spectral threshold, boundary-cylinder identification, or Cesaro
amplifier remains.

## Attempts

- **Existing context-local Fanizza rows do not imply `(FSC1)`.**  The exact
  finite Bass--Serre countermodel in
  `context-local-fanizza-exits-do-not-control-global-leakage` keeps every
  local bridge relator exact while a private exit has a fixed commutator with
  a shared word outside its context.  The same model violates the required
  same-letter row.
- **The two-letter dihedral row cannot simply be specialized.**
  `two-letter-dihedral-swap-wordizes-one-gram-row` controls a private letter
  `a` against a separately named shared letter `b` by imposing the ordinary
  word `ajbj` as a relator.  Setting `b=a` makes that relator the commutator
  of `a` and `j`; the proposed wandering word is then identity in the group.
  Keeping `a` and `b` distinct gives consistency energy but not the
  same-letter HNN row `(FSC1)`.
- **Spectral intersection has exactly zero guaranteed mass.**  The shared
  Fanizza letters are involutions, so canonical exactification gives two sign
  spaces of density `1/2`.  By
  `canonical-spectral-derangement-kills-same-letter-row`, an exact transporter
  may swap those halves, leaving both same-sign intersections zero and paying
  a fixed row defect.  For an order-`m` letter every canonical atom has mass
  `1/m`, and the same cyclic derangement works simultaneously on all atoms.
  Hence neither a majority argument nor a multi-type union supplies the row.
- **What remains.**  A successful cell must use the non-CE/matrix-only source
  to make one rectangular occurrence of the *same* base word intertwine
  across `t`, while the abstract HNN edge continues to identify only the
  finite packet subgroup.  This is strictly smaller than global leakage
  localization `(NCL13)` but cannot be a universal tracial block identity.
