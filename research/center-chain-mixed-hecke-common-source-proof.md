---
rg: 2
id: center-chain-mixed-hecke-common-source-proof
kind: route
title: Pull the transported signed intersection back to one Pauli source
target: center-chain-mixed-hecke-overlap-is-common-pauli-source
requires:
  - center-chain-mixed-hecke-polars-have-exact-overlap
  - center-chain-mixed-hecke-polars-share-a1-tail
---

Write

```text
d=x_82(b_2),       v=x_57(a_1),       w=x_67(a_1),
f=x_94(b_3),       k=x_92(b_3),       c=x_97(b_3a_1),
s=x_68(a_2).
```

The proof of `center-chain-mixed-hecke-polars-have-exact-overlap` gives
the signed subgroups

```text
L_1=H<d,v,w>,               L_2=H<f,k,vc,w,s>.          (1)
```

Every cross commutator between the displayed extra generators is trivial
except

```text
[s,d]=x_62(q),                                      (2)
```

up to orientation.  The right side is a derived root of `H`, on which
`chi` is positive.  Conjugation by `H` preserves the seven-coordinate span
in `(1)`.  Steinberg collection therefore gives a unique form consisting
of an element of `H` followed by seven binary extra coordinates.  Hence

```text
|<L_1,L_2>|=64*2^7
           =|L_1||L_2|/|L_1 intersect L_2|.             (3)
```

It follows that `L_1L_2=<L_1,L_2>=L_2L_1`.  The two transported
characters agree on the intersection and extend to the character `lambda`
which is `chi` on `H` and positive on all seven extra coordinates; relation
`(2)` is compatible because `chi(x_62(q))=+1`.  Expanding the two normalized
signed subgroup sums now gives

```text
P_1P_2=P_2P_1=e_(<L_1,L_2>,lambda)=:P.                 (4)
```

Indeed every element of the product has exactly
`|L_1 intersect L_2|` decompositions, so its coefficient in the product is
`1/|<L_1,L_2>|` with the sign prescribed by `lambda`.

We next pull `(4)` back.  Put

```text
L_0=<H,d,f,c,k,v,w,s>                                  (5)
```

and let `lambda_0` equal `chi` on `H` and be positive on the seven
displayed extra roots.  For the `u_2` pullback, `u_2^(-1)L_2u_2=HK_2`,
where `K_2=<fc,k,v,w,s>`.  Direct conjugation also gives, modulo positive
derived roots of `H`,

```text
u_2^(-1)d u_2=d x_52(q),
u_2^(-1)v u_2=vc,
u_2^(-1)w u_2=w.                                      (6)
```

Thus the two conjugated subgroups generate `L_0`: `v` and `vc` recover
`c`, while `fc` and `c` recover `f`, and `(6)` recovers `d`.  All correction
factors in `(6)` have positive character.  Hence

```text
u_2^(-1)Pu_2=e_(L_0,lambda_0).                         (7)
```

For the `u_1` pullback, `u_1^(-1)L_1u_1=HK_1`, with
`K_1=<d,v,w>`.  Conjugating the extra generators of `L_2` supplies
`fc,k,vc,w,s` modulo positive derived roots and the already present `w`.
Together with `d,v,w`, these again recover exactly the seven roots in `(5)`
with the same signs.  Therefore

```text
u_1^(-1)Pu_1=e_(L_0,lambda_0)=u_2^(-1)Pu_2=:Q.         (8)
```

The trace of a one-dimensional character projection is the reciprocal of
the group order.  Equations `(3)` and `(8)` give

```text
tau(Q)=1/(64*2^7)=tau(e)/128.                          (9)
```

Since `P<=P_i=V_iV_i^*`, equations `(7)--(8)` imply

```text
(V_1^*V_2)^*(V_1^*V_2)=V_2^*P_1V_2=Q,
(V_1^*V_2)(V_1^*V_2)^*=V_1^*P_2V_1=Q.                (10)
```

This proves the common-source and unitary assertions.

It remains to check the Pauli action.  Conjugation by `A_1` permutes
`f` and `fc` and preserves the character in `(5)`.  Conjugation by
`B_1=x_72(b_1)` sends

```text
c |-> ck,
v |-> v x_52(q),
w |-> w x_62(q),                                      (11)
```

and fixes the other displayed generators modulo the same signed subgroup.
Both correction roots in `(11)` are positive derived roots of `H`.
Thus `A_1` and `B_1` reduce `Q`.  Their commutator is the simple root
`x_42(q)`, which acts by `-1` on `Q`, proving the Pauli assertion.

Finally let `U=u_1^(-1)u_2`.  Since the two supports in `(8)` agree,
`V_1^*V_2=UQ` and `U` normalizes `Q`.  The element `B_2` also normalizes
`(L_0,lambda_0)`: its only nontrivial corrections are `d` and positive
derived roots of `H`.  Using

```text
B_2A_1B_2=g_1A_1,             g_1=[B_2,A_1],
[A_1,B_3]=[A_1,A_2]=1,
```

we obtain

```text
B_2UQ
 =B_2A_1B_2B_3A_2A_1Q
 =g_1B_3A_2Q=:R.                                      (12)
```

The three factors on the right of `(12)` commute with `A_1`.  The factors
`B_3,A_2` commute with `B_1`, while

```text
[g_1,B_1]=x_82(b_2a_1b_1)=x_82(b_2)=d.                (13)
```

Because `dQ=Q`, equation `(13)` is trivial after compression to `Q`.
Therefore `R` commutes with both compressed Pauli generators.  Equivalently,
`U=B_2R` has conjugation action

```text
UA_1U^(-1)Q=g_1A_1Q,          UB_1U^(-1)Q=B_1Q,
```

which records the first selector root rather than erasing it as a false
commuting-tail gauge.

