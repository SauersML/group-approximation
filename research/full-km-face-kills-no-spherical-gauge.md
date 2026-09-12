---
rg: 2
id: full-km-face-kills-no-spherical-gauge
kind: claim
title: The full Kac--Moody face is identically flat on the spherical block, where every Pauli chord is zero-cost gauge
distinct_from:
  native-km-coset-coefficients-retain-spherical-pauli-absorber: that exhibits a collapsing eigenvalue for an ungauged overlap-holonomy operator on the common spherical label line; this computes the actual group-word face coefficient there and proves the apparent absorber is removable gauge, not a microstate obstruction.
  finite-face-flatness-stops-at-fundamental-group-holonomy: that identifies arbitrary face-flat overlap connections with presentation holonomy on a nontrivial common reservoir; here the reservoir carries the trivial representation of every vertex group, so the overlap connection may be replaced freely without changing any represented generator.
  relative-three-chart-correction-is-km-regular-stability: that identifies correction on the full regular branch with terminal stability; this removes only the common trivial-label gauge kernel and leaves the nonspherical regular mass problem unchanged.
  native-246-nonspherical-face-complex-has-explicit-gap: that computes all three native incidence spectra and proves a gap 1-sqrt(3q)/(q+1) after quotienting the gauge kernel identified here.
---

**ESTABLISHED.**  In the native triangle let

```text
e_ij=|P_ij|^(-1) sum_(g in P_ij) lambda_(P_ij)(g)      (FKF1)
```

be the spherical projection in a regular `P_ij` chart, amplified by an
arbitrary multiplicity space `C^m`.  Then

```text
lambda_(P_ij)(g)e_ij=e_ij              (g in P_ij).   (FKF2)
```

Consequently every actual native face word is already exactly flat on this
block.  In particular, for the tree-first free kernel basis

```text
n_a in ker(P_1*_(P_0)P_3 ->> P_13),
e pi(n_a)e=e                                               (FKF3)
```

on the common spherical summand.  The induced full-face defect operator and
its derivative on `eM_De` are both zero.  No character-table coefficient or
unreduced `P_ij`-equivariant map can act nontrivially there: between trivial
label representations it is a scalar tensored with the identity on
multiplicity.

This does **not** produce a synchronization counterpacket.  An overlap
intertwiner between two spherical summands is an arbitrary unitary in
`U(m)`.  If a chosen family of such intertwiners has a chord holonomy
`Y_t=AD_tAD_t`, replace the chord intertwiner by the identity (and choose
identity identifications on a spanning tree).  By `(FKF2)` both the old and
new maps intertwine every local group action exactly.  The replacement
changes no microstate generator, no local chart, no dimension, and no native
face word.  Thus every spherical Pauli chord has **zero correction cost**.

Equivalently, the full coupled coefficient complex has a gauge kernel

```text
1_sph tensor M_m,                                        (FKF4)
```

and coercivity must be stated after quotienting by `(FKF4)`, not by demanding
a positive eigenvalue on it.  The explicit `B_2` incidence calculation in
`native-km-coset-coefficients-retain-spherical-pauli-absorber` supplies the
orthogonal coefficient

```text
1-sqrt(2q)/(q+1)>0.                                     (FKF5)
```

Therefore the rotating Pauli benchmark gives a sharp dichotomy for the
unreduced native maps: its spherical component is freely gauge-removable,
while its nonspherical `B_2` component is uniformly gapped.  What remains is
to obtain compatible analogous estimates through the `A_1 x A_1` and `G_2`
vertices on the nontrivial regular-label complement; the full face supplies
no additional spherical actuator.

That remaining finite linear calculation is now complete:
`native-246-nonspherical-face-complex-has-explicit-gap` gives singular radii
`0`, `sqrt(2q)/(q+1)`, and `sqrt(3q)/(q+1)` for the `A_1 x A_1`, `B_2`, and
`G_2` faces respectively.  Hence the whole fixed occurrence complex has gap
`1-sqrt(3q)/(q+1)` modulo `(FKF4)`.  The residual is no longer a missing
character-table constant; it is the nonlinear placement of three separately
exactified charts into that one occurrence complex.
