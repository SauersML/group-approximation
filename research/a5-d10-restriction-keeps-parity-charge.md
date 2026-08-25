---
rg: 2
id: a5-d10-restriction-keeps-parity-charge
kind: claim
title: The first native A5-to-D10 restriction face preserves the determinant-two parity charge
distinct_from:
  three-way-parity-hole-has-one-cell-repair: that proves an abstract odd support-changing margin triple repairs the minimal parity hole; this proves no exact atom at the first native congruence level supplies such an odd charge.
  bs14-native-cell-padding-preserves-lattice-charge: that gives a formal lattice-coset obstruction for an arbitrary cell support; this computes the restriction monoid of the concrete level-five Iwahori endpoint.
  bs14-global-atoms-are-moving-congruence-restrictions: that classifies native atoms as moving congruence restrictions without computing a particular restriction lattice; this computes the complete prime-five table.
---

**ESTABLISHED.**  Identify

```text
PSL_2(F_5)=A_5
```

and let `H=D_10` be the normalizer of a Sylow-five subgroup, equivalently
the image of the level-five BS core.  Write the irreducibles of `H` as

```text
1, epsilon, rho_1, rho_2,                               (ADR1)
```

where `epsilon` is trivial on rotations and negative on reflections, and
`rho_1,rho_2` are the two two-dimensional dihedral representations.  For
the five irreducibles of `A_5`, of dimensions `1,3,3,4,5`, restriction is

```text
1   |-> 1,
3   |-> epsilon+rho_1,
3'  |-> epsilon+rho_2,
4   |-> rho_1+rho_2,
5   |-> 1+rho_1+rho_2.                                  (ADR2)
```

Therefore the mod-two functional

```text
omega(m)=m_epsilon+m_(rho_1)+m_(rho_2) mod 2            (ADR3)
```

vanishes on the restriction of **every** exact `A_5` representation.  The
integral `H`-type

```text
h=epsilon+rho_1+rho_2                                  (ADR4)
```

lies in the rational cone of exact restrictions, since

```text
h=(1/2)(res(3)+res(3')+res(4)),                         (ADR5)
```

but `omega(h)=1`, so it is outside their integer lattice.  In particular

```text
h+res(V)
```

is not the restriction of an `A_5` representation for **any** exact padding
representation `V`.

This is a concrete native counterpart of the determinant-two abstract
cell.  It refutes the proposed successor in its same-level additive form:
the odd support-changing triple from
`three-way-parity-hole-has-one-cell-repair` cannot be supplied by an exact
level-five atom, no matter how much exact level-five padding is allowed.

There is nevertheless a rank-one **type-change** repair:

```text
h-epsilon+1=res(5).                                    (ADR6)
```

Thus the smallest native face supports precisely the architecture required
by flexible reconciliation: change one old one-dimensional boundary type,
then use the five-dimensional exact atom.  It does not support repair by
adding an exact atom while leaving the old type fixed.  To use `(ADR6)` in
the full BS14 theorem one must show that the residual energy pays this type
flip and its joint Gram implementation.  That analytic estimate is not a
consequence of the restriction table.

DERIVATION
a5-d10-parity-table-proof
