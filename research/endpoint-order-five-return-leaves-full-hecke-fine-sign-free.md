---
rg: 2
id: endpoint-order-five-return-leaves-full-hecke-fine-sign-free
kind: claim
title: The endpoint order-five return fixes the full Hecke source but leaves its missing fine sign free
artifacts:
  - research/endpoint-order-five-full-hecke-source-return-proof.md
distinct_from:
  endpoint-order-five-actor-has-half-gram: that proves a representation-universal one-third endpoint Gram on the coarser signed p2 source; this checks the four extra generators of the actual common Hecke source Q and isolates the remaining fine-sign freedom.
  center-chain-mixed-hecke-overlap-is-common-pauli-source: that constructs the exact full source Q for the two mixed Hecke polars in the regular packet; this audits how the new endpoint actor returns that literal signed subgroup without importing regular multiplicities.
---

**ESTABLISHED FULL-SOURCE RETURN AND SCOPED FENCE.**  Retain the endpoint
word `W`, native head `M=J_2B_3A_2`, and roots

```text
t=x_69(a_3),                 s'=x_62(a_3)
```

from `endpoint-order-five-actor-has-half-gram`.  Let

```text
L_0=<H,d,f,c,k,v,w,s>,       Q=e_(L_0,lambda_0)       (OQF1)
```

be the complete signed common Hecke source of
`center-chain-mixed-hecke-overlap-is-common-pauli-source`, where

```text
d=x_82(b_2), f=x_94(b_3), k=x_92(b_3), c=x_97(b_3a_1)
```

have positive sign in addition to `v,w,s`.

Inside the literal `GL_4(F_2)=<W,M>` block, the nontrivial full-source
return is the ordinary word

```text
R=WMWMMMMWMMMMWMWMWM.                                (OQF2)
```

Faithful sparse Leavitt conjugation gives

```text
R g R^(-1)=g                 for every displayed generator g of L_0,
R t R^(-1)=t s',             R s' R^(-1)=s'.          (OQF3)
```

Thus `R` commutes with the full signed projection `Q`, but it does not
exchange the two `s'` signs.  This is the decisive distinction between the
coarser result and the actual Hecke source: the returned `GL_3(F_2)` orbit
used for

```text
rank(p_2 meet Wp_2W) >= (1/3)rank(p_2)
```

does not reduce `Q`.

The return relation itself permits the exact two-dimensional compressed
profile

```text
s'Q=-Q,                    tQ=Z,                    RQ=X,
XZX=-Z=(t s')Q.                                      (OQF4)
```

Since `W` sends the positive `s` condition in `Q` to the positive `s'`
condition, `(OQF4)` has

```text
Q!=0,                     Q(WQW)Q=0.                 (OQF5)
```

This is a scoped countermodel to deduction from the **return relations**,
not a claimed representation of the entire moving `<L_0,W,M>` packet.
Accordingly it proves exactly the safe fence: the one-third `p_2` Gram does
not by itself give a lower bound relative to `Q`.  Closing the full-source
claim requires either an additional actor-sheet orbit which rules out
`(OQF4)`, or a literal occurrence row which pays the `s'` sign.

The shortest signed-`K_1` return which moves the fine root to the native
depth-three root also fails full-cell typing.  It is

```text
h=MMWMWMMWMMMMW,               hsh^(-1)=t,             (OQF6)
```

and faithful sparse conjugation gives

```text
hA_1h^(-1)=A_1,                hA_2h^(-1)=x_59(a_3),
hB_2h^(-1)=x_24(b_3)B_2x_94(b_3),
hB_3h^(-1)=x_25(b_3)x_85(b_2),
hJ_2h^(-1)=x_98(s_(000)t_(00)).                       (OQF7)
```

The conjugate of `J_1` is a non-Whitehead block supported on
`{2,7,8,9}`.  Hence `h` does not carry the complete depth-two native cell
to the depth-three cell: it moves the one desired arm but dresses/ejects
both dual roots and collapses `J_2` to one elementary factor.  Thus it is
not the missing same-`Q` native relative word.

No Property `(T)`, canonical trace, local computation, or Lean compilation
is used.

DERIVATION
endpoint-order-five-full-hecke-source-return-proof
