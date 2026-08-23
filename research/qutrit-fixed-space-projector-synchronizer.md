---
rg: 2
id: qutrit-fixed-space-projector-synchronizer
kind: claim
title: One trace-only group gadget synchronizes a qutrit fixed-space projector while preserving its complement
artifacts:
  - research/artifacts/qutrit-moment-exact-psync-splice-2026-08-23.md
distinct_from:
  hybrid-rank-router-authenticates-affine-overlap-blocks: that asks a two-copy role packet to route `A,B,AB,1` and then uses rank conjugacy to charge one forbidden overlap; this asks directly for fixed-space synchronization of two order-three clocks and requires complement-flexible perfect extension.
  qutrit-diamond-robustly-synchronizes-pvms: that supplies a linear tracial PVM estimate in terms of five same-colour overlap energies; this asks to replace those energies by a fixed finite list of ordinary group-word defects.
  literal-c3-projector-equality-collapses-the-clock: that proves an exact central-character group-algebra identity is too strong; this requires a genuinely tracial certificate which does not identify the complementary eigenspaces.
  central-tagged-one-in-three-is-a-finite-lcs-or: that makes one Boolean coordinate central and branches into binary affine profiles; this keeps all three qutrit positions symmetric and introduces no Boolean central tag.
  qutrit-psync3-tensor-closure-obstruction: that refutes this endpoint by tensoring four scalar exact extensions back into the same central sector.
---

**REFUTED AS STATED.**  The requested gadget cannot exist by
`qutrit-psync3-tensor-closure-obstruction`.  The original target was to
construct one finite ordinary-group gadget with a central element
`J`, order-three interface elements `u,v`, relators `r_1,...,r_m`, and a
constant `K<infinity`, satisfying both clauses below.

### Tracial soundness

For every tracial representation in the sector `J=omega I`,

```text
||Pi_0(u)-Pi_0(v)||_2^2
 <= K sum_(j=1)^m ||r_j-1||_2^2,                        (PS3-1)
```

where `Pi_0(z)=(1+z+z^2)/3`.

### Complement-flexible perfect completeness

Whenever order-three unitaries `U,V` in a finite tracial von Neumann algebra
satisfy

```text
Pi_0(U)=Pi_0(V),                                        (PS3-2)
```

they extend, after a fixed matrix amplification if necessary, to a
zero-defect representation of the gadget with interface `(U,V)` and
`J=omega I`.  The extension must not require `U=V` or `U=V^(-1)`, and it
must remain inside the amplified input algebra so that CE inputs remain CE.

The natural target is a cyclically equivalent sum-of-squares certificate for
`(PS3-1)`.  It cannot be a literal equality in the central-character group
algebra by `literal-c3-projector-equality-collapses-the-clock`, nor can it be
an existential commuting scalar gadget by
`commuting-finite-phase-gadgets-have-affine-scalar-shadows`.

More decisively, complement-flexible completeness supplies exact
`J=omega` extensions of four scalar pairs with zero fixed projectors.  Their
tensor product returns to the `J=omega` sector but has interfaces `(1,omega)`,
whose fixed projectors differ.  Exact group representations are tensor
closed, so `(PS3-1)` then reads `1<=0`.  This rules out arbitrary
noncommuting auxiliaries and arbitrary finite relator lists, not merely the
specific attempted implementations below.

`qutrit-diamond-robustly-synchronizes-pvms` shows that the analytic
synchronization inequality already has a constant five-edge realization.
What is missing is its ordinary-word implementation with `(PS3-2)`.

## Attempts

- **Literal subgroup-average relator:** rejected because it identifies the
  entire cyclic subgroup up to phase/inversion.
- **Commuting `C_3` auxiliaries:** rejected because their scalar solution and
  projected relation sets are affine over `F_3`.
- **Five-edge colouring diamond:** gives the exact linear tracial estimate,
  but the same-colour projection overlaps are not themselves group words.
- **Hybrid rank router:** could charge each overlap once its two hybrid block
  matrices are authenticated, but that is the separate open rank-router
  endpoint rather than a construction of this smaller direct gadget.
