---
rg: 2
id: universal-finite-packet-library-amenable-proof
kind: route
title: Shift one adjacent transposition through the finitary symmetric group
target: universal-finite-packet-library-can-be-amenable
requires: []
---

Let `A=Sym_fin(Z)`, let `t` act by translation, and let `s=(0,1)`. Then

```text
U=A semidirect <t>=<s,t>,
```

because the conjugates `t^k s t^(-k)` are all adjacent transpositions. The
group `A` is locally finite and `U/A` is cyclic, so `U` is amenable. Every
finite group embeds in some symmetric group, and every finite symmetric group
appears on a finite interval in `A`.

The group is ICC: a nontrivial finitary permutation has infinitely many
shift-conjugates, while an element with nonzero shift exponent has infinitely
many conjugates by finitary permutations. Hence amenability identifies `L(U)`
with `R`.

For a finite subgroup `F`, decompose `U` into left `F`-cosets. This makes
`lambda_U|_F` an infinite direct sum of `lambda_F`. The coefficient of the
identity in the usual central idempotent

```text
z_rho=(dim rho/|F|) sum_(f in F) conjugate(chi_rho(f)) f
```

is `(dim rho)^2/|F|`, proving the trace formula.

For the fixed-density overlap example, take a finite-base amenable wreath
product and translate one coordinate projection. Product trace makes distinct
coordinates independent. Orthogonal fixed-density carriers instead obey the
elementary trace budget `tau(sum_i p_i)=sum_i tau(p_i)<=1`.
