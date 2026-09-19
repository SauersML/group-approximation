---
rg: 2
id: stw99-lxxvi-dimension-drop-homotopy-pullback-proof
kind: route
title: Kill the endpoint classes and use vanishing of the ambient pi6 obstruction
target: stw99-lxxvi-dimension-drop-subalgebra-kills-s6-class
requires:
  - stw99-lxxvi-unital-matrix-subalgebra-kills-s6-class
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

The unitary group of `M_2(I_(p,q))` is the homotopy pullback

```text
P=U(2p) times^h_(U(2pq)) U(2q),                        (2)
```

where the two maps amplify by the opposite endpoint identity matrices.
Concretely, a point of `P` is a pair of endpoint unitaries together with a
path in `U(2pq)` joining their images.  The scalar map `U(2)->P` sends `u`
to

```text
u tensor 1_p,        u tensor 1_q,
```

with the constant path at `u tensor 1_p tensor 1_q`, after the fixed tensor
flip identifying the two ambient images.

The homotopy-pullback fibration

```text
Omega U(2pq) -> P -> U(2p) times U(2q)
```

gives the exact segment

```text
pi_6(U(2pq)) -> pi_5(P)
 -> pi_5(U(2p)) directSum pi_5(U(2q)).                  (3)
```

Both endpoint images of `alpha` vanish by
`stw99-lxxvi-unital-matrix-subalgebra-kills-s6-class`, since `p,q>=2`.
Therefore the scalar image of `alpha` in `pi_5(P)` lies in the image of the
left-hand group in (3).

That group is zero.  The unitary stable-range fibration

```text
U(n)->U(n+1)->S^(2n+1)
```

makes `pi_6(U(2pq))->pi_6(U)` an isomorphism because
`6<4pq`.  Bott periodicity gives

```text
pi_6(U)=0.
```

Exactness of (3) now forces the scalar image of `alpha` to vanish in
`pi_5(P)=pi_5(U(M_2(I_(p,q))))`.

Finally, a unital embedding `I_(p,q)->D` factors the scalar inclusion
`C->D`.  Functoriality of matrix unitary groups and homotopy sends the zero
class just obtained to zero in `pi_5(U(M_2(D)))`, proving (1).

For completeness, when `gcd(p,q)=1`, a projection `e in I_(p,q)` has one
rank `d`; its endpoint forms force `q|d` and `p|d`.  Since `0<=d<=pq`, only
`d=0,pq` occur.  This proves the projectionlessness assertion used to
separate the new hypothesis from unital matrix divisibility.
