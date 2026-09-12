---
rg: 2
id: stw99-lxvi-first-infinite-amplification-proof
kind: route
title: Stop immediately below the first infinite amplification
target: stw99-lxvi-finite-car-seed-amplification-index-is-irrelevant
requires: []
---

The second statement plainly implies the first, since an infinite unit in
`M_2(C)` says that `C` is not stably finite.

Conversely, let `A` satisfy the first statement.  Because `1_A` is finite but
`A` is not stably finite, there is a least integer `m >= 2` for which the unit
of `M_m(A)` is infinite.  Put

```text
C = M_(m-1)(A).
```

Minimality of `m` makes `1_C` finite.  The algebra `C` is simple and contains
a unital CAR algebra: if `psi:D -> A` is the given embedding, then

```text
x |-> 1_(m-1) tensor psi(x)
```

is a unital embedding `D -> C`.

Finally, `M_2(C)=M_(2m-2)(A)` has infinite unit.  Indeed, `2m-2 >= m`, and a
proper isometry in `M_m(A)` remains a proper isometry after taking its direct
sum with the identity of `M_(m-2)(A)`.  Hence `C` satisfies the second
statement.

The argument uses only matrix amplification.  In particular, it avoids the
invalid shortcut of tensoring `A` by the CAR algebra, which can destroy
finiteness of the seed projection.
