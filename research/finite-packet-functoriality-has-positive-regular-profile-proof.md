---
rg: 2
id: finite-packet-functoriality-has-positive-regular-profile-proof
kind: route
title: Evaluate every packet chart on a common multiple of its regular representation
target: finite-packet-functoriality-has-positive-regular-profile
requires:
  - finite-packet-graph-atlases-have-a-regular-stationary-flow
  - finite-corona-dimension-certificate-calculus
---

Choose a positive integer `D` divisible by every group order in the finite
diagram.  At a vertex labelled by `F`, take the rational regular packet

```text
V_F=(D/|F|) lambda_F.                                      (RPP1)
```

Its multiplicity at `pi in Irr(F)` is

```text
m^reg_(F,pi)=D dim(pi)/|F|,                               (RPP2)
```

which is strictly positive.

Suppose `E<=F` and let `sigma in Irr(E)`.  Frobenius reciprocity, or the
decomposition of the regular representation after restriction, gives

```text
sum_(pi in Irr(F)) [Res_E^F(pi):sigma] dim(pi)
  =[F:E] dim(sigma).                                      (RPP3)
```

Multiplying by `D/|F|` yields

```text
sum_pi [Res_E^F(pi):sigma] m^reg_(F,pi)
  =D dim(sigma)/|E|
  =m^reg_(E,sigma).                                       (RPP4)
```

Thus every restriction equation holds.  Equation `(RPP4)` is compatible
with composition of restrictions, so every refinement equation holds as
well.  An isomorphism of finite groups preserves group order, irreducible
dimension and the regular representation; hence all conjugacy and
automorphism transport equations hold.

Orthogonal decomposition is literal direct-sum additivity.  For a central
projection `z_S` corresponding to a set `S` of irreducible types, the cut
`z_S V_F` is the direct sum of the summands in `(RPP1)` indexed by `S`.
Assigning those actual multiplicities to every auxiliary cut coordinate
makes all cut and recombination equations hold.  Hence the complete vector
`m^reg` satisfies `B m^reg=0`, proving `(RPF1)`.

Now suppose `(RPF3)` held.  Pair it with `m^reg`:

```text
-m^reg_(a,pi)
  =<B^T y,m^reg>+<s,m^reg>
  =<y,Bm^reg>+<s,m^reg>
  =<s,m^reg>>=0.                                          (RPP5)
```

The left side is strictly negative by `(RPP2)`, a contradiction.  The
rational alternative in `finite-corona-dimension-certificate-calculus`
therefore places every base coordinate outside every forced-zero face of a
system generated only by the listed packet operations.
