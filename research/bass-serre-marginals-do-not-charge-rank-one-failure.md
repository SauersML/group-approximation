---
rg: 2
id: bass-serre-marginals-do-not-charge-rank-one-failure
kind: claim
title: Bass--Serre type transport preserves rank-one marginals but does not charge their contextual failure
invalidates:
  - s3-radical-linear-local-hs-payment-proof
distinct_from:
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that constructs a stationary integral type vector abstractly; this gives an exact finite-dimensional group representation and pinpoints the invalid inference from the rank-one scalar floor to intertwiner energy.
  regular-trace-blocks-exact-local-predicate-return: that uses the infinite-dimensional canonical regular trace; this produces a finite quotient and hence a finite-dimensional exact countermodel to the stated local payment theorem.
  hnn-transports-forbidden-radical-atom-types: that correctly transports the complete joint type vector of one selector--radical subgroup; this proves that such transport supplies the scalar endpoint marginals but not the missing payment.
---

Let `Y` be any finite graph of finite packet groups whose edge maps are
injective.  This includes a finite collection of HNN edges transporting the
complete groups

```text
E_a=<J,z_1,...,z_k,P_a,Q_a>                           (BMF1)
```

used by `hnn-transports-forbidden-radical-atom-types`.  Let `Gamma` be the
fundamental group of this graph of groups.  Suppose one vertex contains the
full selector subgroup

```text
D=<J,z_1,...,z_k> isomorphic to (C_2)^(k+1).           (BMF2)
```

Then `Gamma` has a finite-dimensional exact representation in which

1. every stable letter exactly transports the complete `E_a`-type vector;
2. all scalar conditional endpoint marginals required in `(RNS1)` agree
   exactly;
3. every defining-relator energy and every edge-intertwining energy is zero;
   but
4. every marked selector atom, including a designated forbidden atom, has
   positive normalized trace.

Indeed, a finite graph of finite groups has virtually free fundamental group,
hence is residually finite.  Vertex groups embed by Bass--Serre normal form.
Because their union is finite, residual finiteness supplies one finite quotient

```text
q:Gamma -> Q                                             (BMF3)
```

which is injective on every vertex group simultaneously: separate from the
identity every nonidentity element in the finite union and take the product of
the resulting quotients.  Use the left regular representation of `Q`.  Its
restriction to a vertex group `G_v` is

```text
Res_(G_v) lambda_Q = [Q:G_v] lambda_(G_v).              (BMF4)
```

Thus the two restrictions across every edge agree exactly, stable letters are
exact intertwiners, and the complete joint character multiplicities of every
`E_a` agree.  In particular the conditional traces of the `P_a,Q_a` sign
events agree at adjacent endpoints.  On the other hand, for every selector
atom

```text
e_a^-=(1-J)/2 product_i (1+a_i z_i)/2,
tr_Q(e_a^-)=1/|D|>0.                                    (BMF5)
```

The rank-one inequality is not contradicted.  It says that the three
endpoint-sharing laws carry positive **contextual failure mass**.  In the
regular type vector that mass is simply present in the corresponding endpoint
irreducible types.  It is not a multiplicity mismatch between the two sides of
an edge, since `(BMF4)` makes every edge multiplicity match exactly.

Consequently the step in
`s3-radical-linear-local-hs-payment-proof` asserting

```text
positive failed-pairing mass
  => positive weighted L1 edge-type mismatch
  => positive intertwining energy                            (BMF6)
```

is false under the hypotheses stated there.  `(RNS2)` controls scalar masses;
it does not identify any of those masses with a relator defect.  Literal
equality of endpoint projections would not repair the issue: it would still
leave the failed types populated in the exact regular representation.

The local payment statement can be salvaged only by adding an independent
non-Bass--Serre condition which makes the failed endpoint types themselves pay
energy--for example a two-cell constraining multiplicity holonomy, or a
matrix-specific compressor with no finite-dimensional stationary flow.  HNN
transport of the full selector--radical subgroup, even though it completely
solves the endpoint-marginal bookkeeping, supplies no such condition.
