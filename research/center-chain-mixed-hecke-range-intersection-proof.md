---
rg: 2
id: center-chain-mixed-hecke-range-intersection-proof
kind: route
title: Intersect the two transported signed Hecke subgroups
target: center-chain-mixed-hecke-polars-have-exact-overlap
requires:
  - center-chain-mixed-hecke-polars-share-a1-tail
  - finite-character-hecke-intersection-formula
---

Put `u_1=B_2A_1`, `u_2=B_3A_2A_1`, and extend the character `chi` of
`H` trivially across each `K_i`.  Since `H` normalizes `K_i` and intersects
it trivially, the source projections in `(MHO1)` are the character
idempotents of the finite groups `HK_i`.  Hence the polar range projections
are

```text
P_i=u_i(ez_(K_i))u_i^(-1)=e_(L_i,chi_i),
L_i=u_i(HK_i)u_i^(-1).                                      (1)
```

We compute the two transported groups.  Write

```text
h_1=x_42(q), h_2=x_54(q), h_3=x_65(q).
```

Elementary conjugation in characteristic two gives

```text
u_1K_1u_1^(-1)=<d,v,w>,
u_1h_1u_1^(-1)=h_1d,
u_1h_2u_1^(-1)=h_2v,
u_1h_3u_1^(-1)=h_3.                                        (2)
```

Thus `L_1=H<d,v,w>`, and `chi_1` is `chi` on `H` and trivial on the
three displayed extra roots.

For the second row, conjugation by the common right `A_1` tail sends
`fc` to `f`, while conjugation by `B_3` sends `v` to `vc`; all other
displayed generators are fixed.  Moreover

```text
u_2K_2u_2^(-1)=<f,k,vc,w,s>,
u_2h_1u_2^(-1)=h_1,
u_2h_2u_2^(-1)=h_2fvc,
u_2h_3u_2^(-1)=h_3s.                                      (3)
```

It follows that

```text
L_2=H<f,k,vc,w,s>,                                        (4)
```

with transported character `chi_2=chi` on `H` and trivial on its five
extra generators.

The elementary-matrix image gives a unique collected form for both finite
groups.  Outside the six `H` coordinates, `L_1` uses the independent root
coordinates

```text
x_82(b_2), x_57(a_1), x_67(a_1),                         (5)
```

whereas `L_2` uses

```text
x_94(b_3), x_92(b_3), x_57(a_1)x_97(b_3a_1),
x_67(a_1), x_68(a_2).                                    (6)
```

Comparing the `82,94,92,97,68,57` coordinates forces every exponent in
`(5)--(6)` to vanish except the common `67` exponent.  Consequently

```text
L_1 intersect L_2=H<w>.                                  (7)
```

The transported characters agree on this intersection: both equal `chi`
on `H` and are positive on `w`.  Also

```text
|H|=64, |L_1|=64*8, |L_2|=64*32, |L_1 intersect L_2|=64*2. (8)
```

Apply `finite-character-hecke-intersection-formula` to `(1)`.  It yields

```text
||P_1P_2||_2^2=(64*2)/((64*8)(64*32))=1/8192=tau(e)/128. (9)
```

Finally `V_iV_i^*=P_i`, so cyclicity of the trace gives

```text
||V_1^*V_2||_2^2
 =tau(V_1^*P_2V_1)=tau(P_2P_1)=tau(e)/128,              (10)
```

as required.

