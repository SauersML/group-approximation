---
rg: 2
id: binary-leavitt-finite-actor-minimal-atom-dichotomy
kind: claim
title: Finite actor atoms are Morita-neutral, while the full Leavitt parabolic orbit is infinite
invalidates:
  - binary-leavitt-atomic-return-via-minimal-finite-actor
distinct_from:
  maximal-sparse-character-atom-does-not-return-multiplicity: that audits coordinatewise maximization under a corona branch return; this gives an exact finite crossed-product countermodel to every compiler using only a finite invariant root window and its finite actor action.
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that proves the full parabolic orbit is infinite; this combines that obstruction with the complementary exact model for every finite invariant actor packet.
  simple-lamp-normalizers-have-unitary-multiplicity-fibers: that computes arbitrary multiplicity gauges for a finite simple-lamp packet; this treats finite abelian root-character atoms and shows directly that a returned atom has no binary Leavitt capacity.
artifacts:
  - research/binary-leavitt-finite-actor-minimal-atom-proof.md
---

**ESTABLISHED FINITE-ACTOR/MINIMAL-ATOM FENCE.**  Let `A` be a nonzero
finite elementary abelian `2`-group, let `K` be a finite group acting on
`A`, and fix `0!=a_0 in A`.  On `ell^2(A^)` define

```text
M_a delta_chi=chi(a)delta_chi,
P_k delta_chi=delta_(k chi),
(k chi)(a)=chi(k^(-1)a).                              (FAM1)
```

Then

```text
P_k M_a P_k^(-1)=M_(k a)                              (FAM2)
```

exactly.  Every joint character atom has rank one, and there are atoms with
`chi(a_0)=-1`.  Tensoring `(FAM1)` with any finite-dimensional unitary
representation of `K` makes every atom have the same arbitrary
multiplicity and puts an arbitrary compatible unitary gauge on its actor
returns.

Consequently least-rank selection supplies no rank inequality.  Distinct
orbit characters give orthogonal equal-rank reservoirs.  If an actor word
returns `chi`, its compression is only a unitary on the existing
multiplicity fiber.  In particular, finite root multiplication, the full
finite actor table, covariance, and a returned least-rank marked atom do not
imply operators in that atom satisfying

```text
t_i s_i=1,                         i=0,1,
s_0t_0+s_1t_1=1.                                    (FAM3)
```

Indeed `(FAM1)` is an exact finite matrix model of all those inputs, whereas
`(FAM3)` is impossible in a nonzero finite matrix algebra by the ordinary
unnormalized trace.

This finite model covers exactly the case in which a finite exactified root
window is preserved by the selected actors and only their induced finite
action and covariance are used.  The other side of the dichotomy is the
literal binary-Leavitt parabolic.  For the full last-column root module of
`St_n(L_(F_2)(1,2))`, every nontrivial character has an infinite orbit under
the upper-left vertex by
`surviving-leavitt-corona-character-has-infinite-parabolic-orbit`.  Hence a
finite invariant character packet cannot contain the coefficient orbit
which sees the Leavitt dimension obstruction.

There is also an exact syntactic obstruction to calling a genuine
opposite-root word part of this normalizer packet.  In the elementary
matrix image, on the two coordinates `(i,j)`, put

```text
x=I+qE_(ij),              y=I+E_(ji),                 (FAM4)
```

where `0!=q=q^2` and the coefficient field has characteristic two.  Since
`y^(-1)=y`, direct multiplication gives

```text
yxy^(-1)|_(i,j)=[[1+q,q],[q,1+q]].                   (FAM5)
```

This is not in the abelian upper root group containing `x`: it has both
diagonal and opposite-root entries.  Thus an actor genuinely opposite to a
selected root does not permute the joint spectral atoms of that root packet.
Actors in a complementary parabolic may normalize the packet (and may
contain opposite pairs among themselves), but then their induced action on
a fixed finite window is exactly the finite action modeled by `(FAM1)`.

Thus simultaneous exactification plus atom minimality has only two regimes:

1. close a finite invariant actor packet, where `(FAM1)` is an exact marked
   countermodel and every return is Morita-neutral; or
2. use a root-opposite actor or follow the genuine Leavitt parabolic orbit,
   which leaves the abelian spectral packet or every finite invariant root
   window and restores the mixed-occurrence/moving-boundary problem.

In the second regime, finiteness of the matrix gives returns only after the
window or word radius is allowed to grow with the coordinate.  It gives no
fixed bounded-cost return.  A bounded returned selector, if one exists,
must therefore come from an additional authenticated coefficient-sensitive
mixed/opposite-root occurrence; it cannot be inferred from minimal spectral
rank or finite actor covariance alone.

No Property `(T)`, Kazhdan projection, trace-profile assumption, or
literature theorem is used.  This is not a countermodel to the full
Steinberg presentation and does not refute the Property-`(T)`-free non-MF
goal.

DERIVATION
binary-leavitt-finite-actor-minimal-atom-proof
