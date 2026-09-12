---
rg: 2
id: regular-paired-finite-group-relations-are-balanced-proof
kind: route
title: The regular character detects the two projection kernels exactly
target: regular-paired-finite-group-relations-are-balanced
requires: []
---

The character of the regular representation is

```text
chi_Reg(g) = |G|  if g=1,
             0    otherwise.                            (1)
```

Therefore the characters of the two `K`-representations in `(RPB1)` satisfy

```text
chi_i(k)=|G|  iff k in ker p_i.                         (2)
```

If the representations are isomorphic their characters agree, and `(2)`
forces `ker p_1=ker p_2`.

Conversely suppose the common kernel is `N`.  Each image

```text
H_i=p_i(K)
```

is isomorphic to `K/N`, so `|H_1|=|H_2|=|K/N|`.  Restricted to `H_i`, the
regular representation of `G` is

```text
Reg_G |_ H_i  ~=  [G:H_i] Reg_(H_i).                   (3)
```

Pull `(3)` back along `K->H_i`.  Both sides of `(RPB1)` are therefore

```text
[G:|K/N|] copies of the inflated regular representation Reg_(K/N).
```

Hence they are unitarily isomorphic.

Choose one unitary intertwiner `U`.  Since `U` belongs to the full intertwiner
matrix space, for every subspace `X`

```text
U(X) <= Hom_K(Reg_G o p_2,Reg_G o p_1)(X).
```

Thus the latter image has dimension at least `dim X`, proving `(RPB3)`.  Tensor
amplification preserves the same unitary intertwiner and the conclusion.
