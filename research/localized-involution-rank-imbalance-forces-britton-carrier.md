---
rg: 2
id: localized-involution-rank-imbalance-forces-britton-carrier
kind: claim
title: Local involution rank imbalance forces an unnamed Britton commutator carrier
distinct_from:
  twisted-disagreement-return-factors-through-localized-commutator: that assumes a positive reducing carrier on which the cross-commutator is small; this extracts such a carrier from a rank imbalance inside a larger common reducing space.
  adaptive-rectangular-kernel-column-extraction: that extracts a contraction from a rectangular kernel with a separate return estimate; here the kernel is a literal common sign eigenspace and the commutator return is exact.
  commuting-involution-mass-is-four-times-rank: that identifies mismatch mass after the two involutions already commute; this needs no prior commutation and obtains a commuting subspace from unequal local sign ranks.
---

**ESTABLISHED CONDITIONAL TERMINAL.**  Let `C,B` be self-adjoint
involutions in `M_d(C)`, and let `E` be a projection reducing both.  Put

```text
P=E(1+C)/2,                 R=E(1+B)/2,
Delta=|tau(P)-tau(R)|.                                  (LRI1)
```

There is a projection `Q<=E` with

```text
tau(Q)>=Delta,
[Q,C]=[Q,B]=0,
(CBCB-1)Q=0.                                           (LRI2)
```

More precisely, if `tau(P)>=tau(R)`, take the projection onto

```text
Ran(P) intersection Ker(R).                            (LRI3)
```

It has trace at least `tau(P)-tau(R)`, and `C=+1`, `B=-1` on its range.
For the reverse inequality use `Ker(P) intersection Ran(R)`, where
`C=-1`, `B=+1`.

Consequently, in the HNN setting of
`twisted-disagreement-return-factors-through-localized-commutator`, a fixed
finite menu of model-dependent reducing carriers with

```text
max_i |tau(E_i(1+C_i)/2)-tau(E_i(1+B_i)/2)|
   >= alpha-o(1)                                       (LRI4)
```

produces an unnamed fixed projection of mass at least `alpha-o(1)` for one
of the infinite-order Britton commutators

```text
g_i=C_i B_i C_i B_i.                                  (LRI5)
```

The successful index may depend on the microstate; finite-menu
pigeonholing and the Fejer terminal still apply.

## Canonical balanced-half fence

This lemma is **not** a new source of global rank imbalance.  For fixed
nonidentity involution words `c,b` in canonical-trace microstates,

```text
tau((1+c)/2), tau((1+b)/2) -> 1/2,                    (LRI6)
```

so their global imbalance tends to zero before `(LRI1)` is used.

The same fence applies to the usual fixed central marked carrier.  Let `J`
be a nontrivial central involution, `E_J=(1-J)/2`, and let `a` be an
involution such that all of `a,J,Ja` are nonidentity.  In the canonical
regular trace,

```text
tau(E_J)=1/2,
tau(E_J(1+a)/2)=1/4.                                  (LRI7)
```

Thus every such word is exactly balanced on the `J=-1` half.  Two ordinary
packet words `a,b` satisfying the same noncollapse conditions have zero
local rank imbalance on this fixed carrier.  Extraspecial/Clifford marked
packets make this especially rigid: their unique spin character vanishes on
every noncentral packet word, so the local involutions used by the affine
rank-jump construction are balanced.

Accordingly, the Taller--Vidick affine rank pressure does not automatically
instantiate `(LRI4)`.  It is a discrepancy of packet **multiplicity types**,
not an oriented trace imbalance between two fixed involution words.  A
balanced failure profile (in particular failure mass `1/2`) leaves every
such involution-rank checksum zero.  Converting that type discrepancy into
`(LRI4)` on a model-dependent returned carrier is another formulation of
`uniform-affine-lcs-rank-return`, not a bypass of it.

## Exact scope

The only potentially useful application is localized: `E_i` must itself be
model-dependent, and complementary sectors may balance the global canonical
traces.  If `E_i` is the evaluation of one fixed group-algebra projection,
then `(LRI4)` is a fixed canonical mixed-moment discrepancy.  Its nonzero
limit would already contradict the regular representation once `(LRI2)` and
Britton wandering are combined.  Hence a fixed named carrier cannot supply
new leverage; the source must be a genuinely finite-matrix-only decoded
packet or multiplicity sector.

