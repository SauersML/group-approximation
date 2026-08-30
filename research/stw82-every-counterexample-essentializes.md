---
rg: 2
id: stw82-every-counterexample-essentializes
kind: claim
title: Every extension counterexample has an essential-ideal presentation on the same middle algebra
---

Let

```text
0 -> I -> E -pi-> D -> 0
```

be a C*-extension, and let `tau : D -> Q(I)` be its Busby map.  Put
`K=ker(tau)` and `L=pi^(-1)(K)`.  Then

```text
L is isomorphic to I directSum K,
L is an essential ideal of E,
E/L is isomorphic to D/K.
```

Consequently

```text
dim_nuc(L) <= max(dim_nuc(I),dim_nuc(D)),
dim_nuc(E/L) <= dim_nuc(D).
```

If the original extension violates the nuclear-dimension maximum formula,
then the essential extension

```text
0 -> L -> E -> D/K -> 0
```

violates it too.  Therefore STW Problem LXXXII is equivalent to its
restriction to extensions by essential ideals.  Separability is preserved,
so together with `stw82-every-counterexample-reflects-to-a-separable-subextension`
this says that every counterexample has a separable essential-ideal witness.
