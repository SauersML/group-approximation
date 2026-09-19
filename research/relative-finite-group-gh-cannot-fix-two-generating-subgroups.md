---
rg: 2
id: relative-finite-group-gh-cannot-fix-two-generating-subgroups
kind: claim
title: Finite-group HS exactification cannot fix two exact generating-subgroup restrictions, and alternating correction has only quadratic gap
distinct_from:
  gowers-hatami-finite-group-hs-stability: that permits perturbing the whole approximate finite-group table; this gives canonical-regular approximate tables which are exact on two generating subgroups but have no nonzero exact joint restriction unless one subgroup action is perturbed.
  common-gh-isometry-selects-the-two-overlap-cross-coefficient: that selects the two subgroup polar comparisons near each other; this proves near equality need not contain any exact simultaneous support and computes the alternating-correction rate.
  finite-face-flatness-stops-at-fundamental-group-holonomy: that identifies global face correction with presentation stability; this is a four-dimensional fixed finite-group counterpacket to the proposed relative local preprocessing theorem.
  three-reynolds-plus-kernel-energy-has-vanishing-gap: that adds a third regular leg and all three quotient kernel-word adjoint energies, then diagonalizes the resulting full positive diagram operator; this supplies the two-leg seed.
---

**ESTABLISHED.**  Let

```text
G=C_2 x C_2=<a,b | a^2=b^2=1, ab=ba>.
```

On `C^2 tensor C^2`, with Pauli matrices `X,Y,Z`, put

```text
A=Z tensor I,       B=I tensor Z,       C=X tensor Y,
B_t=cos(2t)B+sin(2t)C,             0<t<pi/4.           (RFG1)
```

The matrices `B,C` are anticommuting Hermitian unitaries, so `B_t` is a
Hermitian unitary.  Define a table on the four normal forms by

```text
phi_t(1)=I, phi_t(a)=A, phi_t(b)=B_t, phi_t(ab)=AB_t.   (RFG2)
```

Then:

1. `phi_t` is exact on each generating subgroup `<a>` and `<b>`, and both
   restrictions are regular multiples.
2. Its normalized character is **exactly** the regular character of `G`:

   ```text
   tr(A)=tr(B_t)=tr(AB_t)=0.                            (RFG3)
   ```

3. Every multiplication defect is at most

   ```text
   delta_t=2 sin(2t)->0,                                (RFG4)
   ```

   and the commuting relator has defect exactly `delta_t`.
4. There is no nonzero subspace invariant under both `A` and `B_t` on
   which their restrictions commute.  Indeed

   ```text
   [A,B_t]=2 sin(2t) AC                                 (RFG5)
   ```

   is a nonzero scalar multiple of a unitary and hence has zero kernel.

Tensoring all matrices with `I_m` gives arbitrarily high ambient dimension,
keeps `(RFG3)--(RFG5)` unchanged in normalized Hilbert--Schmidt norm, and
still admits no nonzero exact joint invariant subspace.  Consequently there
is no relative Gowers--Hatami theorem which, after deleting or adding
`o(d)` dimensions, retains a nonzero invariant copy of the old space, fixes
both generating-subgroup actions on that copy literally, and makes their
union an exact `G`-representation.  In particular, deletion cannot leave a
`1-o(1)` exact old sector.  Ordinary Gowers--Hatami
stability is not contradicted: replacing `B_t` by `B` costs `O(t)` and
perturbs the second exact subgroup representation.

The natural alternating correction has no hidden uniform contraction.  Let

```text
E_A(T)=(T+ATA)/2,       E_(B_t)(T)=(T+B_t T B_t)/2.     (RFG6)
```

Then on the trace-zero unit vector `B`,

```text
E_A E_(B_t)(B)=cos^2(2t)B
                  =(1-delta_t^2/4)B.                   (RFG7)
```

Thus the exact contraction deficit is quadratic in the native relator
defect and tends to zero.  No dimension-free `kappa>0` can make one
alternating correction step contract the residual by `1-kappa`, even on
canonical-regular tables and even after arbitrary common amplification.

For the Kac--Moody section chart this rules out a generic relative
finite-group preprocessing theorem that freezes `P_1` and `P_3`.  Their
actions may be perturbed by `o_2(1)`—as ordinary finite-group stability
allows—but cannot in general be held literally fixed on a `1-o(1)` old
sector.  Any stronger simultaneous correction must use the native triangle
relations to control how the three subgroup perturbations fit together; it
does not follow from finite-group stability or alternating Reynolds
projections alone.

The three-leg extension is exact and quantitative:
`three-reynolds-plus-kernel-energy-has-vanishing-gap` adds a commuting third
regular involution so that the full eight-point table has exactly the regular
character.  Even after summing all three Reynolds Laplacians and all three
commuting quotient-kernel adjoint energies, the resulting finite matrix has
gap at most `1-cos(2t)+4sin^2(4t)`.  Thus merely adding the relator energies
to the alternating scheme does not repair its collapsing angle.
