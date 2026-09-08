# No first-staggered-block centralizer repair satisfies the TS word and first braid

2026-09-08. This exhausts a finite family of nonmonomial boundary changes
of the amenable seven-ray model. The family has exactly 1008 members;
none satisfies even the necessary tests `W(head3)=head3` and the first
braid on the head. It therefore gives no new marked model of `Gamma_2`.

The result applies to both the natural and contragredient head actions.
It does not exclude larger boundary changes or arbitrary representations.

## 1. The full family and why the finite shifted packet survives

Use the natural linear head and permutation tail of the
[seven-ray construction](jacobson-two-braid-seven-ray-countermodel-2026-09-08.md).
Write its stable involution as `H_0`, and write the three head basis
vectors as `q_1,q_2,q_3`. The first staggered block is

```text
S_1={A_1@1, q_2, B_3@1, A_3@1, B_2@1, B_1@1, C@1}.
```

Identify these seven vectors respectively with the usual nonzero binary
labels `1,2,3,4,5,6,7`. On this block, the three operators

```text
c_P=(I+E_13)_P,       k_P=(I+E_31)_P,       H_0
```

act as the natural seven-point permutation representation of
`x_13,x_31,w_12`. They generate a finite `GL_3(F_2)` packet. The same
description holds on every later staggered block, while the two external
head vectors are fixed.

Let `U` act only on the span of `S_1` and commute with
`K_P=<c_P,k_P>`. Define

```text
H_U=U H_0 U^(-1).
```

Then `<c_P,k_P,H_U>` is the conjugate of the same finite packet.
Also `U` commutes with the head overlap, whose nontrivial action is
supported on `q_1,q_3`. Thus `H_U` retains the involution and overlap
relations, and still has the same eventual translated-ray action as
`H_0`. A successful repair of the remaining relations would therefore
still generate an amenable group. The calculation below shows that no
repair in this family succeeds.

## 2. Why there are exactly 1008 changes of basis

In the first staggered block put

```text
t_0=q_2,
t_1=A_1+A_3+B_2,       t_2=B_3+B_1+C,
v_0=A_1+B_2,           v_1=A_3+B_2,
w_0=B_3+C,             w_1=B_1+C,
```

where all six named non-head vectors have level one. These seven
vectors are a basis. The `t` vectors are fixed by `K_P`. The pairs
`(v_0,v_1)` and `(w_0,w_1)` carry identical irreducible natural
two-dimensional representations of `GL_2(F_2)`. Their endomorphism
ring is `F_2`, and neither has a nonzero intertwiner to or from the
trivial module. Consequently

```text
Aut_(K_P)(span S_1)=GL_3(F_2) x GL_2(F_2),
|Aut_(K_P)(span S_1)|=168*6=1008.
```

The first factor acts on `(t_0,t_1,t_2)`. The second applies the same
mixing matrix to `(v_0,w_0)` and `(v_1,w_1)`. Thus the enumeration
below covers every linear change in the specified centralizer, not
merely permutation changes or a sample of matrices.

## 3. The necessary tests exclude the entire family

Retain the packet definitions

```text
k=k_Q k_P,           z=z_Q z_P,
b=(w_23,w_23),       W=[[H_U c_P H_U,k],H_U z H_U] z.
```

The exact computation gives

| Necessary conditions | Number of changes U |
| --- | ---: |
| Complete centralizer family | 1008 |
| `W q_3=q_3` | 16 |
| `W q_3=q_3` and first braid fixes the head | 0 |

The 16 changes passing the first test have the following complete
description. Encode columns of a matrix on the three `t` vectors by
binary integers. Its column triple is one of

```text
(2,4,5), (2,5,4), (3,4,5), (3,5,4),
(4,2,3), (4,3,2), (5,2,3), (5,3,2).
```

The two-dimensional multiplicity matrix is either the identity or the
swap, with columns `(1,2)` or `(2,1)`. All 16 satisfy

```text
U^(-1)q_2=t_1+t_2.
```

Their transported head vector `H_U q_2` is one of the following four
vectors, with `epsilon` independently either zero or one:

```text
A_1+B_3+B_1+C + epsilon*q_2,
A_1+B_3+A_3+B_2 + epsilon*q_2.                        (1)
```

None is fixed by `b`: in the first line `b` exchanges the unequal
`B_2,B_3` coordinates, and in the second it moves the `A_3@1`
coordinate to `A_2@1`, outside `S_1`. A head `q_2` term, if present,
also moves to `q_3`.

Since `H_U` fixes `q_1,q_3`, the first braid on the head is equivalent
to `b(H_U q_2)=H_U q_2`. Indeed `H_U b` sends
`q_2` to `q_3`, then to `H_U q_2`; its next image returns to `q_2`
exactly under that condition. Thus (1) explicitly rejects all 16
remaining changes. No test on the other rays is needed to prove the
obstruction.

## 4. The dual vector does not repair the natural head

The seven-point module contains the dual natural module spanned by
`f_i=sum_(x_i=1) e_x`. In particular `f_2=t_0+t_2` is `K_P`-fixed.
The transvection `U_0=I+t_2 tensor t_0^*` is an allowed involutive
change and sends `q_2` to `f_2`.

Its orientation is wrong for the required head transport. In coordinates
conjugated by `U_0`, the head root has target `f_2`, the transported
root has target `H_0 f_2=f_1`, and the shifted element `u=x_21`
fixes `f_1`. Hence its commutator with that transported head root is
trivial. The remaining commutator factor fixes `q_3` and cannot cancel
the nonzero head-root contribution to `W q_3`. The exhaustive table
agrees: none of the 144 changes with `U^(-1)q_2=f_2` passes
`W q_3=q_3`.

Changing the head itself to the contragredient representation does not
produce another family to search. The group automorphism
`g |-> (g^(-1))^T` on these row-and-column-finite operators fixes
every tail permutation and `H_0`, sends the natural head to the dual
head, and sends `U` to `U^(-T)`. The latter ranges over the same
1008-element centralizer, because `c_P,k_P` are permutation matrices.
It preserves every displayed group relation. Therefore existence of
a dual-head repair would imply existence of a natural-head repair,
which the complete check excludes.

## 5. Exact replay and remaining scope

The [stdlib verifier](../../experiments/jacobson_staggered_centralizer_repair_audit.py)
enumerates both general linear groups, constructs their action in the
displayed basis, checks invertibility and both centralizer generators,
and evaluates the expanded group words directly on binary vectors.
Its [MSI output](jacobson-staggered-centralizer-repair-audit-2026-09-08.json)
records all 16 surviving matrices and their failing first-braid vectors.
The final replay used one Python process, an 18-second CPU cap and
a 20-second wall timeout; it finished in 0.309102 seconds.

```text
script SHA256:
11b8d65b8c77be2a9b4c9646ddfee5f2d8a97203db6ba9d93a4f304a015b6840

MSI replay command, from the remote repository:
timeout 20 /usr/bin/python3.12 experiments/jacobson_staggered_centralizer_repair_audit.py
```

The finite-module decomposition and word conventions were independently
audited. This is exact computational evidence for the complete specified
family, with explicit rejection witnesses; no formal proof checker is
claimed. Larger finite supports, other shifted modules, and general
norm-matrix-corona representations remain outside this result.
