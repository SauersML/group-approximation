---
rg: 2
id: raw-one-hot-tensor-separation-proof
kind: route
title: Put the raw branch system and the two decoded charts on three coordinates
target: raw-incidence-and-one-hot-pvms-tensor-separate
requires: []
---

Transitivity supplies a section `s_i in G` with `s_i o=i`. Choose any
`d_i in Stab_G(o)` and set

```text
b_i=s_i d_i^(-1),                a_i=s_i.               (RIP1)
```

Then `a_i=b_i d_i`, both sections carry `o` to `i`, and the Bernoulli
coordinate permutation `d_i` fixes the base projection. This proves
`(RIO3)`.

The coordinate projections in `(RIO4)` are complete PVMs and diagonal
permutation matrices transport their labels exactly. At a basis vector with
first decoded coordinate `j`, the sign tuple `(u_i)_i` has `u_j=-1` and
`u_i=1` for `i!=j`. Therefore the Fourier joint atom for that one-hot sign
pattern is `P_j`, all other sign patterns vanish, and the same argument
applies to `(v_i)` and `Q_j`.

Product trace gives

```text
tau(P_iQ_j)=1/q^2                                     (RIP2)
```

for every `i,j`. Since equal-trace projections satisfy

```text
(1/2)||P_i-Q_i||_2^2=tau(P_i)-tau(P_iQ_i),             (RIP3)
```

summing proves `(RIO6)`. Finally the diagonal transition `T_i=d_i` permutes
the atoms of each decoded coordinate. For any target label `sigma(i)`,
product independence and Pythagoras give

```text
||(1-Q_(sigma(i)))T_iP_i||_2^2
 =tau(P_i)-1/q^2=1/q-1/q^2.                            (RIP4)
```

Summing proves `(RIO7)`.
