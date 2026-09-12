---
rg: 2
id: stw99-xciv-commuting-car-seed-proof
kind: route
title: Average a kernel over the finite-dimensional CAR stages
target: stw99-xciv-commuting-car-seed-has-zstable-hull
requires: []
---

Write `U` as the increasing union closure of full matrix algebras `U_n`, and
let `tau` be its unique trace.  Since `U` is nuclear, the commuting inclusions
of `A` and `U` into `B` induce a homomorphism

```text
mu:A tensor_min U -> B,       mu(a tensor u)=au.
```

We first prove that `mu` is injective; mere commutation would not by itself
justify this step for two arbitrary tensor factors.  Let `J=ker(mu)` and
suppose that `0 != x in J_+`.  The slice

```text
E(x)=(id_A tensor tau)(x)
```

is nonzero because `tau` is faithful: represent `A` faithfully and note that
every vector state applied to `E(x)` is the faithful slice by `tau` of the
corresponding positive operator-valued matrix coefficient; if all these
slices vanish, positivity and faithfulness of `tau` force `x=0`.

For an elementary tensor whose second component belongs to `U_m`, averaging
over the unitary group of any `U_n` with `n>=m` gives exactly
`E(x) tensor 1`.  Approximating a general `x` by such finite-stage tensors
therefore shows that `E(x) tensor 1` is a norm limit of convex averages of

```text
(1 tensor v)x(1 tensor v*) in J,       v in U_n.
```

Thus `E(x) tensor 1` belongs to `J`.  But `mu` is faithful on
`A tensor 1`, so `E(x)=0`, a contradiction.  Hence `mu` is injective and
`C*(A,U) ~= A tensor_min U`.

The generated algebra is separable.  Finally, the CAR algebra absorbs the
Jiang--Su algebra, so

```text
(A tensor U) tensor Z ~= A tensor (U tensor Z) ~= A tensor U.
```

It is therefore a separable unital `Z`-stable hull of `S`.

For the tensor-leg corollary, use the canonical commuting inclusions in
`R_0 bar_tensor R_1` and choose a unital CAR subalgebra of `R_1`.  The argument
above already proves faithfulness on the minimal tensor product, so no
von Neumann tensor-product or normality inference is being smuggled in.
