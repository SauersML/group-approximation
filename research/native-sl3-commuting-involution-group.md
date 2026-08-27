---
rg: 2
id: native-sl3-commuting-involution-group
kind: claim
title: A finitely presented arithmetic two-coordinate group has a nontrivial finite-dimensionally invisible mark
distinct_from:
  sl3-codense-coset-lamp-recursive-host: that retains the entire recursively presented coset lamp module and then uses Higman; this keeps only the base lamp and its first commuting h-conjugate and is already finitely presented.
  hnn-over-codense-kazhdan-subgroup-not-hyperlinear: that uses the unrestricted centralizer HNN extension and assumes stability of the actor; this adds the one native commuting-conjugate relation and isolates the weaker two-projection transfer gate.
---

Let `C<A` and `h` be the arithmetic pair above and define

```text
G_cc = < A,c |
         c^2=1,
         [c,s]=1 (s in S_C),
         [c,h c h^-1]=1 >,                             (GCC1)
m=[c,h]=c h c h^-1.                                    (GCC2)
```

Then:

1. `G_cc` is finitely presented;
2. `m!=1` in `G_cc`;
3. every exact finite-dimensional unitary representation of `G_cc` kills
   `m`.

For (1), use finite presentations of `A` and the finite generating set
`S_C`.  For (2), map `G_cc` onto the permutational lamp group

```text
(direct_sum_(A/C) C_2) rtimes A
```

by sending `c` to the base coset lamp.  The relations hold and `m` maps to
the product of the two distinct lamps at `C` and `hC`, so it is nontrivial.
For (3), if `rho` is finite-dimensional then

```text
rho(c) in rho(C)'=rho(A)'
```

by finite-dimensional codensity of the arithmetic pair.  Hence
`rho([c,h])=1`.

This exact package does not prove nonhyperlinearity: the missing normalized-
HS step is exactly `commuting-conjugate-involution-transfer-for-sl3-pair`.
Structurally, `native-sl3-group-is-hecke-graph-wreath-product` identifies this
presentation as a graph wreath product over the Hecke orbital graph on
`A/C`.  By `native-hecke-graph-action-is-the-permanence-firewall`, a sofic
model of that graph action would make this whole candidate sofic and refute
the desired transfer.  The nonamenable stabilizer means the current automatic
sofic-action theorems do not decide it.
