---
rg: 2
id: relative-fd-face-and-normal-toric-quotient-proof
kind: route
title: Identify the perfect-state face and compute the phase-safe normal quotient
target: toric-gap-is-a-relative-fd-central-word-face
requires: []
---

Let `G=G_A x G_B`, let `B` be the finite central phase group, and suppose a
finite game is torically determined by finitely many clauses
`h_i=(beta_i,g_i)` in `B x G`.  Write `H=<h_i>`.  When `H intersect B={1}`,
projection identifies `H` with the graph of a character `chi:K->B`, where
`K=proj_G(H)`.  Define

```text
F_(K,chi)={phi : phi(chi(k)k)=1 for every k in K}.
```

It is enough to impose the equations for the clause generators: for a state
`phi`, equality `phi(u)=1` for a unitary `u` says that the GNS cyclic vector
is fixed by `u`, and hence it is fixed by every word in those generators.

We first prove the exact finite-dimensional face criterion

```text
omega_qa=1
  iff F_(K,chi) intersects closure(S_fd(G)).             (RFP1)
```

If finite-dimensional strategies have values tending to one, their vector
states have a weak-star cluster point.  Each of the finitely many losing
projection products has limiting expectation zero, so the cluster state is
perfect.  Toric determination says exactly that its GNS vector is fixed by
all clauses, placing it in `F_(K,chi)`.

Conversely, take `phi` in the displayed intersection.  Membership in the
face and toric determination make `phi` a perfect state.  Every losing
projection product is a finite linear combination of group elements.  Since
there are finitely many such products, finite-dimensional vector states
converging weak-star to `phi` approximate all their expectations
simultaneously.  Their losses therefore tend to zero, proving
`omega_qa=1` and `(RFP1)`.  Thus a strict toric `qc/qa` gap is precisely
failure of finite-dimensional approximation on the whole clause-character
face, rather than nonapproximation of one selected state.

It remains to compute what normal phase safety does to the clause words.
Write

```text
r_i=(beta_i,a_i,b_i) in B x G_A x G_B
```

and let `N` be their normal closure.  In the quotient by `N`, the equality
`beta_i a_i b_i=1` makes `a_i b_i` central.  The player factors commute, so
for `x in G_A` and `y in G_B`,

```text
[a_i b_i,x]=[a_i,x],   [a_i b_i,y]=[b_i,y].            (RFP2)
```

Consequently the quotient factors through

```text
A_0=G_A/<<[a_i,x]>>,   B_0=G_B/<<[b_i,y]>>,             (RFP3)
```

where it suffices to use finite generating sets for `x` and `y`.  The images
`abar_i` and `bbar_i` are central in these quotients.  Therefore the residual
clauses are central and their normal closure is simply

```text
Z=< (beta_i,abar_i,bbar_i) >
    <= B x Z(A_0) x Z(B_0).
```

Both constructions impose exactly the original normal closure relations, so
their universal properties give

```text
(B x G_A x G_B)/N  ~=  (B x A_0 x B_0)/Z.              (RFP4)
```

The original phase copy of `B` embeds in this quotient exactly when
`Z intersect B={1}`.  Equivalently, if `E` is free abelian on the clause
indices and

```text
alpha(n)=prod_i (abar_i,bbar_i)^(n_i),
beta(n)=prod_i beta_i^(n_i),
```

then phase safety is `ker(alpha)<=ker(beta)`: precisely the condition that
the scalar labels factor through the central subgroup `im(alpha)`.  Hence
normal phase safety retains only central one-player word data, while toric
soundness remains exactly the relative finite-dimensional face exclusion in
`(RFP1)`.
