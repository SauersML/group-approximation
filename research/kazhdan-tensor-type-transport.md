---
rg: 2
id: kazhdan-tensor-type-transport
kind: claim
title: One-sided Kazhdan transport of asymptotic intertwiners at every tensor type
distinct_from:
  kazhdan-asymptotic-commutant-transport: That established claim is the adjoint case — type (1,1), where fixed tensors are Hilbert--Schmidt asymptotic commutants; this one quantifies over every fixed tensor type (p,q), transporting asymptotic intertwiners between distinct tensor powers.
  scaled-kazhdan-transport: That established claim varies the weight on the fixed adjoint sector; this one varies the tensor type of the sector itself, and composes with that claim to give every type at every weight.
---

Let `Gamma` be Kazhdan, `iota : Gamma -> H`, `s in H` with
`s iota(Gamma) s^{-1} <= iota(Gamma)`, and let `U_n` be an operator-norm
asymptotic unitary representation of `H` on `C^(d_n)`.  Fix a tensor type
`(p, q)`.  For every sequence of operators

```text
x_n : (C^(d_n))^(tensor q)  ->  (C^(d_n))^(tensor p)
```

that is uniformly operator-norm bounded and asymptotically intertwines the
restricted tensor powers — for each `gamma`,

```text
‖ U_n(iota gamma)^(tensor p) x_n  -  x_n U_n(iota gamma)^(tensor q) ‖_2  ->  0
```

in the normalized Hilbert--Schmidt norm of the block space
`M_(d_n^p + d_n^q)` — the `s`-translate
`U_n(s)^(tensor p) x_n (U_n(s)^(tensor q))^*` is again such an asymptotic
intertwiner.  Composing the same reduction with `scaled-kazhdan-transport`
gives the statement at every nonnegative weight, so the low-mass sectors
are covered by self-normalized weights rather than lost to the dimension
normalization.

**Reading.**  Type-`(p,q)` tensors are Hilbert--Schmidt operators
`(C^d)^(tensor q) -> (C^d)^(tensor p)`, and fixed tensors of
`U^(tensor p) tensor Ubar^(tensor q)` are exactly intertwiners.  So
one-sided Kazhdan compression cannot asymptotically create fixed tensors of
any fixed type: no asymptotic invariant vectors of macroscopic mass, no
invariant forms, no intertwiners, no invariant multilinear structures — the
asymptotic counterpart of `invariant-tensor-compression-rigidity`, and an
obstruction factory with no commutator anywhere in its statement.

**Calibrations.**  (i) For `p = q = 1` this is exactly
`kazhdan-asymptotic-commutant-transport`.  (ii) The conclusion is a 2-norm
statement on the tensor sector, so `hs-invisibility-inflation-no-go`
applies unchanged: any use toward non-MF-ness must still cross the metric
gap by an invariant corner or a self-normalized scale.  (iii) At the
dimension weight the type `(p, 0)` instance is vacuous — a bounded vector
has vanishing normalized block mass — which is precisely why the scaled
form matters.
