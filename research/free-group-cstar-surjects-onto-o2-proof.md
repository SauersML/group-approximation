---
rg: 2
id: free-group-cstar-surjects-onto-o2-proof
kind: route
title: Generate the Cuntz algebra by three Julia unitaries and apply free universality
target: properly-infinite-cstar-quotient-is-compatible-with-fp-mf-group
requires: []
---

Let `O_2` have canonical generators `S_0,S_1` satisfying

```text
S_i^* S_j=delta_(ij)1,          S_0S_0^*+S_1S_1^*=1.        (PIQ4)
```

First identify `M_2(O_2)` with `O_2`.  The formulas

```text
Phi([a_ij])=sum_(i,j=0,1) S_i a_ij S_j^*,
Psi(x)=[S_i^* x S_j]_(i,j=0,1)                              (PIQ5)
```

define inverse unital star homomorphisms.  Multiplicativity of `Phi` follows
from `S_j^*S_k=delta_(jk)`, and the two inverse identities follow from both
relations in `(PIQ4)`.

We now give three unitary generators of `M_2(O_2)`.  Put

```text
D=diag(1,-1),               x_r=S_r/2,
U_r=[[x_r,(1-x_rx_r^*)^(1/2)],
     [(1-x_r^*x_r)^(1/2),-x_r^*]],             r=0,1.       (PIQ6)
```

The standard Julia-operator multiplication, using

```text
x_r(1-x_r^*x_r)^(1/2)=(1-x_rx_r^*)^(1/2)x_r,
```

shows that each `U_r` is unitary.  Let `B=C*(D,U_0,U_1)` and put

```text
p=(1+D)/2=e_11,             q=(1-D)/2=e_22.
```

Then

```text
pU_rp=x_r e_11,
pU_rq=b_r e_12,             b_r=(1-x_rx_r^*)^(1/2).         (PIQ7)
```

Since `||x_r||=1/2`, `b_r` is invertible.  The element `b_r e_11` and its
inverse belong to `B` by continuous functional calculus applied to
`x_r e_11`.  Hence `(PIQ7)` gives `e_12 in B`, and adjoints give
`e_21 in B`.  Also `2pU_rp=S_r e_11` lies in `B`.  Multiplying by the matrix
units gives

```text
S_r e_ij=e_(i1)(S_r e_11)e_(1j) in B                       (PIQ8)
```

for all `i,j,r`.  Since `S_0,S_1` generate `O_2`, `(PIQ8)` proves

```text
C*(D,U_0,U_1)=M_2(O_2).                                   (PIQ9)
```

Apply `Phi` and set

```text
W=Phi(D),                 V_r=Phi(U_r).
```

These are three unitaries generating `O_2`.  By the universal property of
the full group C-star algebra on three free unitaries, sending the free
generators to `W,V_0,V_1` gives the surjection `(PIQ1)`.

The target is not directly finite because `(PIQ4)` gives `(PIQ2)` and
`1-S_0S_0^*=S_1S_1^*!=0`.  On the other hand Choi's theorem embeds
`C*(F_3)` faithfully into a product of matrix algebras.  Coordinatewise
stable finiteness and injectivity make `C*(F_3)` stably finite.  Finally,
`F_3` is residually finite.  For each word ball choose one finite quotient
injective on that ball, and use its left regular permutation representation.
Every fixed nonidentity word is then nontrivial at all sufficiently large
coordinates.  A nonidentity element in a finite-group regular representation
has operator-norm distance at least `sqrt(3)` from the identity: on each
nontrivial cyclic orbit its spectrum contains all roots of unity of its
order, one of which is at distance at least `sqrt(3)` from `1`.  Hence the
resulting norm-matrix-corona homomorphism is faithful, and `F_3` is
operator-MF.  This proves every assertion of the claim.
