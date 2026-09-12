---
rg: 2
id: km-triangle-nonflat-counterpacket-proof
kind: route
title: Separate one kernel word in a finite quotient of the virtually free tree side
target: km-triangle-local-bimodules-have-finite-nonflat-models
requires:
  - triangle-colimit-llp-reduces-to-relator-local-splitting
---

The triangle-colimit theorem proves that `G_0` is finitely generated
virtually free, hence residually finite, and that `E` embeds in `G_0`.
Fix `1!=n in N`.  Residual finiteness supplies a finite quotient

```text
phi:G_0->F
```

with `phi(n)!=1`.  By taking the product with finitely many further finite
quotients, arrange simultaneously that `phi` is injective on the finite set

```text
(P_12 union P_23)\{1}.
```

It is then injective on both finite vertex groups and on all their edge
subgroups.

Let `D` be a common multiple of `|F|` and `|P_13|`.  On a `D`-dimensional
space take

```text
rho_0=(lambda_F o phi) tensor I_(D/|F|),
rho_13=lambda_(P_13) tensor I_(D/|P_13|).              (KTC1)
```

For every finite subgroup `H` on the tree side, injectivity of `phi|_H`
and the elementary restriction formula for a finite regular representation
give

```text
rho_0|_H ~= lambda_H tensor I_(D/|H|).                 (KTC2)
```

The same formula gives `(KTC2)` for every `H<=P_13` on the second side.
In particular the restrictions to `P_1` and `P_3` are exactly unitarily
equivalent, with identical multiplicities; choose arbitrary exact
intertwiners for them.  The `P_2` overlap is already internal to `rho_0`.
These intertwiners transport every group-algebra matrix unit exactly.

There is also a choice-independent way to remove accidental fixed vectors.
The finite coset graph `N\T` from the triangle-colimit proof has fundamental
group `N`, so it has a chord because `n!=1`.  Gauge its overlap intertwiners
along a spanning tree.  Multiplying one chord intertwiner by a scalar
`zeta!=1` preserves its source, range, and every finite-group intertwining
equation.  If the previous chord holonomy is `H`, its full multiplicity
commutant torsor permits multiplication by `zeta H^*`, producing the exact
new holonomy `zeta I`.  This has no eigenvalue `1`, hence no nonzero invariant
subprojection on which that cycle closes.  The same spectral exclusion
persists under common amplification.

On the tree side,

```text
rho_0(n)=lambda_F(phi(n)) tensor I_(D/|F|) != I,
```

whereas the map `E->P_13` sends `n` to `1`.  If the `P_1` and `P_3`
intertwiners were restrictions of one unitary `W`, then, because those
subgroups generate `E`, `W` would intertwine the two representations of all
of `E`.  In particular it would conjugate `rho_0(n)!=I` to `rho_13(1)=I`, a
contradiction.  Equivalently, after gauging a spanning tree, at least one
fundamental-cycle holonomy is nontrivial.  Common amplification preserves
every assertion, completing the counterpacket proof.
