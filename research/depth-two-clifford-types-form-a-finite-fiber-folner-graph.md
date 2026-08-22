---
rg: 2
id: depth-two-clifford-types-form-a-finite-fiber-folner-graph
kind: claim
title: The deepest dyadic Clifford types form only a finite-fiber Folner graph
distinct_from:
  six-parahoric-finite-fiber-folds-remain-amenable: that permits an arbitrary abstract finite label fiber; this identifies the actual level-independent fiber supplied by Clifford theory of the last two congruence layers.
  exact-dyadic-conductor-band-has-uniform-parahoric-overlap-loss: that proves a fixed loss inside one conductor band; this shows why iterating only its last-two-layer representation labels cannot turn that loss into a uniform global gap.
  regular-congruence-depth-mixtures-remain-folner: that treats only the scalar conductor marginal; this retains the complete character-orbit type of the depth-two principal kernel.
---

For `a>=4`, put

```text
Q_a=SL_3(Z/2^a Z),
N_a=ker(Q_a -> Q_(a-2)).                                (DCF1)
```

Then `N_a` is canonically the additive group

```text
sl_3(Z/4Z),
1+2^(a-2)X  <->  X mod 4.                               (DCF2)
```

Conjugation of `Q_a` on `N_a` factors through `Q_2=SL_3(Z/4Z)`.
Consequently the Clifford-theory label of an irreducible exact-conductor
representation on its deepest two layers is an orbit in the fixed finite
set

```text
F = sl_3(Z/4Z)^hat / Q_2.                               (DCF3)
```

In particular `F` and every incidence relation on `F` induced by one of the
six Weyl-conjugate denominator/parahoric moves are independent of `a`.

After recording the `A_2` coweight coordinate, every graph built only from
conductor depth, the label `(DCF3)`, and those six local incidences is a
bounded-degree finite-fiber graph over the coweight lattice `L=Z^2`:

```text
vertices subseteq L times F,
(x,f) -> (x+v,f')       for v in W.(1,0,-1).             (DCF4)
```

Such a graph is amenable.  The ambient bounded-range graph has quadratic
growth, uniformly in the finite fiber, and every infinite component of a
bounded-degree graph of polynomial growth has Følner sets.  For the full
finite-fiber transition system, taking the whole fiber over a coweight box
`B_R` gives

```text
|boundary(B_R times F)|/|B_R times F| = O_F(1/R).        (DCF5)
```

Deleting transition edges by fixed local inverse, Weyl, triangle, or
parahoric compatibility cannot create super-polynomial growth, so every
remaining infinite component is still amenable.

Therefore a uniform-in-conductor commutant-transfer modulus cannot come from
an isoperimetric or expansion gap of the scalar-conductor/last-two-layer
type graph: that graph is amenable.  A successful representation-theoretic
proof must instead find a finite local incompatibility among those types,
retain unbounded congruence/branch history, or prove that arithmetic word
identifications decode the histories as distinct vertices of the
nonamenable affine building.  This is a no-go for the bounded-depth
EXPANSION strategy, not a construction of a full arithmetic leak.
