---
rg: 2
id: kazhdan-tensor-type-transport-proof
kind: route
title: Block reduction of tensor types to the adjoint transport
target: kazhdan-tensor-type-transport
requires: [kazhdan-asymptotic-commutant-transport, scaled-kazhdan-transport]
---

## Why sufficient

Fix `(p, q)` and set

```text
W_n(g)  =  U_n(g)^(tensor p)  (+)  U_n(g)^(tensor q)
```

on `(C^(d_n))^(tensor p) (+) (C^(d_n))^(tensor q)`, a block space of
dimension `d_n^p + d_n^q`.

**`W_n` is an operator-norm asymptotic unitary representation of `H`.**
Each `W_n(g)` is exactly unitary.  Tensor powers are exactly
multiplicative on matrices — `(AB)^(tensor r) = A^(tensor r) B^(tensor r)`
— so the multiplicativity defect of `W_n` is

```text
max over r in {p, q} of ‖ U_n(gh)^(tensor r) - (U_n(g) U_n(h))^(tensor r) ‖,
```

and telescoping gives `‖A^(tensor r) - B^(tensor r)‖ <= r ‖A - B‖` for
contractions, so the defect is at most `max(p,q)` times the defect of
`U_n` and vanishes pointwise.  The compression data `(Gamma, iota, s)` are
untouched: they live on the group side.

**Intertwiners are off-diagonal commutants.**  Embed `x_n` as the block
matrix `A_n = [[0, x_n], [0, 0]]`.  Then `‖A_n‖ = ‖x_n‖`, uniformly
bounded, and for `V = W_n(iota gamma) = diag(V_p, V_q)`,

```text
[A_n, V]  =  [[0, x_n V_q - V_p x_n], [0, 0]],
```

so the normalized Hilbert--Schmidt norm of the commutator in
`M_(d_n^p + d_n^q)` is exactly the block-normalized intertwining defect of
`x_n`.  The hypothesis of the claim is therefore precisely that `A_n` is a
uniformly bounded Hilbert--Schmidt asymptotic commutant of the Kazhdan
image under `W_n`.

**Transport.**  `kazhdan-asymptotic-commutant-transport` applies to the
asymptotic representation `W_n` of `H` and yields that
`W_n(s) A_n W_n(s)^*` is again such an asymptotic commutant.  Computing
the conjugation blockwise,

```text
W_n(s) A_n W_n(s)^*  =  [[0,  U_n(s)^(tensor p) x_n (U_n(s)^(tensor q))^*], [0, 0]],
```

still off-diagonal, and its commutator with `W_n(iota gamma)` is again
off-diagonal with corner equal to the intertwining defect of the
translate.  Vanishing of the block commutator is therefore exactly the
claimed conclusion.

**Every weight.**  The block construction does not touch the weight:
applying `scaled-kazhdan-transport` to `W_n` and the same `A_n` in place of
the dimension-normalized theorem gives the transport of `w`-mass-bounded,
`w`-scaled asymptotic intertwiners for every nonnegative weight sequence
`w`, which is the scaled clause of the claim.
