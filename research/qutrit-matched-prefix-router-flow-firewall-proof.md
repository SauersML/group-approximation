---
rg: 2
id: qutrit-matched-prefix-router-flow-firewall-proof
kind: proof
title: Factor every matched prefix router through one scalar potential and solve all line flows uniformly
target: qutrit-matched-prefix-router-family-is-one-finite-hnn-chart
requires:
  - qutrit-full-leavitt-prefix-conjugator-realizes-phase-star
  - amenable-edge-hnn-preserves-hyperlinearity
---

## One rectangular equivalence suffices

For `s!=0` the permutation `h_(r,s)=J^rZ^s` translates the last leaf
coordinate by

```text
r-su_1.
```

Exactly one value of `u_1` makes this translation zero. Thus every
`h_(r,s)` has nine pointwise fixed leaves, six three-cycles, and the
additional fixed `star` coordinate. Over `F_2` all six oriented
generators have the same normal form

```text
N_h=I_16 direct-sum (I_6 tensor kappa),
kappa=[0 1; 1 1].                                       (QMF5)
```

Choose scalar matrices `P_(r,s) in GL_28(F_2)` with

```text
P_(r,s)^(-1) h_(r,s) P_(r,s)=N_h.
```

Let `P_J` and the explicit prefix matrix `D` be those in the proof of
the single-router theorem, so

```text
P_J^(-1)JP_J=N_J,                 DN_J=N_hD.
```

Then

```text
g_(r,s)=P_(r,s) D P_J^(-1)                              (QMF6)
```

is invertible over the binary Leavitt algebra and conjugates `J` to
`h_(r,s)`.

Fix `u_0=(r_0,s_0)` and put

```text
B_(r,s)=P_(r,s)P_(r_0,s_0)^(-1) in K=GL_28(F_2).
```

Equation `(QMF6)` immediately gives

```text
g_(r,s)=B_(r,s)g_(r_0,s_0),
g_(r,s)g_(r',s')^(-1)=B_(r,s)B_(r',s')^(-1).            (QMF7)
```

This proves `(QMF1)` and `(QMF2)`. In particular, for a cyclic list
`u_0,u_1,...,u_l=u_0`,

```text
product_(i=0)^(l-1) (g_(u_(i+1))g_(u_i)^(-1))=1
```

is merely the telescoping identity for the scalar potentials `B_u`.
The construction has not produced an infinite-coefficient return word.

## The full character-flow system

Let a finite-dimensional representation be exact on `C=<J,Z>`, and
let `p_(a,b)` denote the joint spectral projection on which

```text
J=omega^a,                 Z=omega^b.
```

Write `w_(a,b)=tr_n(p_(a,b))`. If a unitary `G_(r,s)` satisfies

```text
G_(r,s) J G_(r,s)^*=J^rZ^s,
```

then it sends the `omega^p` spectral projection of `J` onto the
`omega^p` spectral projection of `J^rZ^s`. Equality of their normalized
ranks is exactly

```text
sum_(b in F_3) w_(p,b)
  =sum_(a,b in F_3: ra+sb=p) w_(a,b).                   (QMF8)
```

This is `(QMF3)`. Both affine lines in `(QMF8)` contain three points.
Consequently `w_(a,b)=c` solves the equation for every `p,r,s`
simultaneously. Normalizing the total weight gives `c=1/9`.

This stationary point is not an artificial padding sector. In a
canonical microstate, finite-group exactification on `C` gives

```text
w_(a,b)=1/9+o(1)
```

for all nine characters. Thus every matched-router rank equality is
already asymptotically balanced by the required canonical distribution.
For the active source plane `J=omega`, a fixed router selects one target
cell inside that plane and has two further target cells in the other
`J`-spectral planes. Those two cells have total uniform capacity `2/9`,
exactly enough to receive the Hall leakage. Different routers carry
different unitaries, so scalar rank bookkeeping supplies no
orthogonality between their leaked ranges.

## The finite-edge HNN cover

The finite scalar group `K=GL_28(F_2)` contains `J`, every
`h_(r,s)`, every `B_(r,s)`, and the finite qutrit head. Let
`g_0=g_(r_0,s_0)`. There is a surjective homomorphism

```text
widehat(Gamma)=<K,U | UJU^(-1)=h_(r_0,s_0)>
       -> <K,g_0> <= GL_28(L),                U |-> g_0. (QMF9)
```

The associated subgroups `<J>` and `<h_(r_0,s_0)>` both have order
three. Hence `widehat(Gamma)` is a finite-edge HNN extension of the
finite group `K` and is hyperlinear by amenable-edge HNN permanence.

There is also a literal exact finite-dimensional packet for all relations
displayed so far. In the left regular representation of `K`, the two
nonidentity order-three elements `J` and `h_(r_0,s_0)` have identical
spectral multiplicities. Choose a unitary `U` conjugating them. Set

```text
G_(r,s)=lambda_K(B_(r,s))U.
```

Then all finite-group relations in `K`, all six conjugacy relations, and
all pair-ratio and telescoping relations `(QMF7)` hold exactly. The
restriction to `C` is a multiple of its regular representation, so its
nine character weights are precisely uniform.

The map in `(QMF9)` is not claimed injective, and hyperlinearity does not
pass to arbitrary quotients. Accordingly this does not decide the
concrete Leavitt subgroup. It proves the narrower statement needed here:
the complete matched prefix family, its natural pair ratios, every
potential-cycle relation, and every scalar character-weight inequality
have an exact uniform countermodel. A load-bearing relation must see a
non-scalar relative prefix equivalence, not merely another target line
with the same `D`.
