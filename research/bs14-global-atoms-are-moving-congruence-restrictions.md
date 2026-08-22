---
rg: 2
id: bs14-global-atoms-are-moving-congruence-restrictions
kind: claim
title: Exact BS14-Iwahori atoms are restrictions of moving finite congruence irreducibles
distinct_from:
  sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair: that proves finite congruence factorization and co-density; this identifies the resulting global restriction semigroup relevant to BS14 repair.
  bs14-native-cells-cross-every-length-cutoff: that exhibits one cross-length atom; this describes all exact atoms and isolates the approximate-authentication gap.
  iwahori-uniform-infinitesimal-rigidity: that gives a uniform derivative gap at congruence points; this distinguishes that near-sector theorem from global atom extraction.
---

Let

```text
A=PSL_2(Z[1/2])
```

in its BS14-plus-involution presentation, and let `B=<R,S>` be the exact
BS core.  Every finite-dimensional unitary representation of `A` has finite
congruence image.  Therefore every exact representation is an orthogonal
sum of irreducible representations of finite quotients

```text
Q_n=im(A -> PSL_2(Z/n)),             n odd.           (GAR1)
```

If `Rep_+(Q_n)=N[Irr(Q_n)]` is the finite representation monoid and
`res_n` denotes restriction to the image of `B`, the exact BS cores which
extend through the two cubics form precisely the directed union

```text
E_B = colim_(n odd) res_n(Rep_+(Q_n)).                (GAR2)
```

Thus a correct "native cell" is not an independent scalar BS packet.  It
is the complete restriction of one irreducible congruence representation,
possibly coupling many fourth-power packet lengths and phases.  At each
fixed `n` this is a finitely generated affine monoid, but there is no fixed
finite list of atoms as `n` varies.

The full even-Weil representation at a prime `p=1 mod 4` is one such
irreducible atom in `Rep_+(PSL_2(F_p))`.  Its restriction contains the
trivial BS line and the long nonzero packets in one indivisible global
cell.  This is the representation-semigroup formulation of
`bs14-native-cells-cross-every-length-cutoff`.

There is no exact noncongruence obstruction hiding here: `(GAR1)` follows
from the finite-order unipotent argument, the normal subgroup theorem, and
Serre CSP, as already established in
`sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`.  The remaining obstruction
is entirely approximate.  To use `(GAR2)` on a near tuple, one must produce
a level `n`, a nonnegative multiplicity vector in `Rep_+(Q_n)`, and a
nearby compression of its restriction, uniformly when `n` and the
multiplicities move.

`iwahori-uniform-infinitesimal-rigidity` supplies this only after the tuple
has entered a fixed neighborhood of the congruence locus: its derivative
gap and Newton step align perturbations of an already identified atom.
It does not extract `(n,[pi])` from an arbitrary tuple uniformly far from
every exact finite-dimensional representation.  Conversely, a theorem
which extracted the global atoms from the two cubic residual polar data and
bounded the missing boundary by their Frobenius energy would itself give
the missing flexible repair.  Hence the new language is exact but not a
shortcut around the far sector.

In particular, neither packetwise saturation nor a fixed-level finite
semigroup resolves the endpoint.  The required object is a
**moving-level congruence restriction decomposition with controlled
compression boundary**.  The even-Weil family shows why that decomposition
must allow one atom to cross all chosen packet-length thresholds.

