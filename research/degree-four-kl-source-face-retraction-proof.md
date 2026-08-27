---
rg: 2
id: degree-four-kl-source-face-retraction-proof
kind: route
title: Retract the four orbit cells onto a Coxeter cycle retaining the distance-two commutator
target: degree-four-kl-source-face-retraction
requires:
  - leavitt-omega-has-an-explicit-distorted-target
  - kl-test-word-conjunction-fence
---

## The four lifts

Write the candidate as

```text
W=r t e t a t^(-1)c t^2 b t^(-1)d t p t.             (DG1)
```

Its degree is four.  In the degree-four kernel put `z=t^4` and index the
coefficient copies modulo four.  Direct Schreier rewriting gives

```text
R0=r0 e1 a2 c1 b3 d2 p3 z,
R1=r1 e2 a3 c2 z b0 z^(-1)d3 z p0,
R2=r2 e3 z a0 z^(-1)c3 z b1 d0 p1,
R3=r3 z e0 a1 c0 b2 d1 p2.                            (DG2)
```

Each relator has `z`-degree one, as required.  On setting `z=1`, all four
reduce uniformly to

```text
Ri=r_i e_(i+1) a_(i+2) c_(i+1)
       b_(i+3) d_(i+2) p_(i+3),                       (DG3)
```

with indices modulo four.

## A target group with exactly the relevant root-orbit geometry

Let `A_Gamma` be the right-angled Coxeter group on involutions
`C_j`, `j in Z/20`, where `C_j` and `C_k` commute unless
`k-j=+2` or `-2` modulo twenty.  Let `P` generate `C_20` and shift the
vertices, and put

```text
H=A_Gamma semidirect <P>,       P C_j P^(-1)=C_(j+1).
```

Set `C=C_0` and `D=P^2 C P^(-2)=C_2`.  The special subgroup on
`{C_0,C_2}` is `C_2*C_2`, because those vertices are not joined by an edge.
The graph-product normal-form theorem therefore gives

```text
[C,D] != 1 in H.                                      (DG4)
```

This choice retains more than torsion: it satisfies every commutation
relation among the cycle conjugates of `x_13(s_0)` which follows merely from
disjoint Steinberg root supports.  The distance-two pair is deliberately the
one noncommuting Steinberg chain.

## The retraction

Map `z` to `1`, and in all four copies put

```text
a_i=b_i=1,      q_i=1,
(p0,p1,p2,p3)=(P,P^(-1),P,P^(-1)),
r_i=q_i p_i=p_i,

c0=C,           c1=c2=c3=1,
d0=D,           d1=d2=d3=1,

e0=C,           e1=e2=1,       e3=D.                 (DG5)
```

Every named root packet maps to an involution and every `p_i` has order
twenty.  The definitions are respected:

```text
b_i=r_i^2 a_i r_i^(-2)=1,
d_i=p_i^2 c_i p_i^(-2),
r_i=q_i p_i,
[a_i,b_i]=1.                                          (DG6)
```

The same-copy commutations among `a,c,e` also hold; in the only copy where
both `c_i,e_i` are nontrivial they are equal.  Relations involving the
permutation orbit of `c` or `e` hold in `H` by its defining graph.

Substitution in `(DG3)` now gives, in order,

```text
R0=P P^(-1)=1,
R1=P^(-1)P=1,
R2=P D D P^(-1)=1,
R3=P^(-1)C C P=1.                                    (DG7)
```

But `(DG4)` says that the desired outer boundary
`[c0,d0]=[C,D]` survives.  Hence it is not a product of conjugates of the
four orbit relators and the listed source/definition/torsion/commutation
relations.

The scope is important.  The actual packet set `{a,e,q,p}` generates the
whole Leavitt elementary group.  Sending `a,q` to `1` while retaining the
images in `(DG5)` need not extend to a homomorphism of a full coefficient
copy.  Thus `(DG5)` identifies the exact missing input--global within-copy
Leavitt coupling--rather than proving injectivity of the actual relative
presentation.
