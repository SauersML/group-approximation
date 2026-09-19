---
rg: 2
id: finite-cross-word-hall-reflection-proof
kind: route
title: Separate finitely many cosets while increasing the Hall completion index
target: finite-cross-word-family-fits-one-hall-reflection
requires: []
---

Put `H=<R>`. It is finitely generated and has infinite index in `F`, because
`H<=K` and `F/K` is infinite. Hall's theorem, applied simultaneously to the
finite set `E`, gives a finite-index subgroup `L_0` containing `H` and none
of the `f_j`. In its free-factor formulation we may arrange

```text
L_0=H*J
```

with a nontrivial free factor `J`: equality `L_0=H` would make `H` finite
index in `F`.

Choose finite quotients of `J` of arbitrarily large order and let `L` be the
kernel of the composite

```text
L_0=H*J -> J -> C_M,                                   (HMP1)
```

where the first map kills `H`. Then `H<=L`, the index `[F:L]` tends to
infinity with `M`, and `L<=L_0` ensures `f_j notin L` for every `j`.

Let `sigma` be the left action on `ell^2(F/L)`, let `p` project onto the base
coset, and put `V=1-2p`. Elements of `R<=L` fix `p`, proving the first part
of `(HMF2)`. For each `j`, the projection

```text
p_j=sigma(f_j)p sigma(f_j)^*
```

is a rank-one projection orthogonal to `p`. Hence

```text
Ad(sigma)(f_j)V-V=2(p-p_j).                            (HMP2)
```

Its operator norm is `2`, its squared normalized Hilbert--Schmidt norm is
`8/d`, and all its ranges lie in

```text
pH + sum_j p_jH,
```

whose dimension is at most `m+1`. Conjugating `sigma` by `V` turns `(HMP2)`
into the two-vertex cross-word gap, completing the proof.

For the diagonal consequence, apply the construction at stage `n` to
`R_n,E_n` and take the cyclic quotient in `(HMP1)` large enough that
`[F:L_n]>=n(|E_n|+1)`. Every fixed kernel or cross-word label then belongs
to the appropriate window eventually. Equation `(HMP2)` shows that the
joint range of the current cross-word commutators is contained in the sum of
at most `|E_n|+1` rank-one coset projections, proving `(HMF7)`.
