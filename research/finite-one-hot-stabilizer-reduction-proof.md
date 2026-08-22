---
rg: 2
id: finite-one-hot-stabilizer-reduction-proof
kind: route
title: Restrict the finite transformation groupoid to the one-hot orbit
target: finite-one-hot-algebraic-corners-reduce-to-stabilizers
requires: []
---

The coordinate-permutation action sends `e_q` to `e_(gq)`, so `Y` is
invariant.  Hence `z=1_Y` is a central projection of the crossed product and
the corner is the crossed product of the restricted finite action:

```text
z (L^infinity(K) rtimes Lambda) z
   = ell^infinity(Y) rtimes Lambda.
```

It splits over the finitely many orbits.  Fix a transitive orbit
`O={q_1,...,q_n}`, put `H=Stab_Lambda(q_1)`, and choose `r_i in Lambda` with
`r_i q_1=q_i`.  If `p_i=1_{e_(q_i)}`, the usual transformation-groupoid
matrix units are

```text
E_ij=p_i u_(r_i r_j^(-1)) p_j.
```

They satisfy `E_ij E_jk=E_ik` and `E_ij^*=E_ji`.  Moreover

```text
p_1 (ell^infinity(O) rtimes Lambda) p_1
   = closure span {p_1 u_h:h in H}
   ~= L(H).
```

Every groupoid arrow in the transitive restriction factors through these
matrix units and one isotropy arrow.  Therefore

```text
ell^infinity(O) rtimes Lambda ~= M_n(L(H)),
```

which proves `(FOH1)` after summing over the orbits.

If every `H_O` were hyperlinear, every `L(H_O)` would be Connes embeddable;
finite matrix amplification and finite direct sums preserve Connes
embeddability.  The displayed one-hot corner would then be Connes embeddable,
so restricting its trace along any unital trace-preserving map from `B`
would give a Connes-embeddable tracial state on `B`, a contradiction.  Thus
some `H_O` is nonhyperlinear.

Finally, the coordinates of product Haar measure on `K_I` are independent.
In the `i`-th factor there are `p^(|Q_i|)` vectors and exactly `|Q_i|`
basis vectors.  Finite intersections of the one-hot events therefore have
measure equal to the corresponding finite product.  Continuity from above
gives `(FOH2)`.  If that product tends to zero, `1_(Y_I)=0` in the Haar
von Neumann algebra, so it cannot be the unit of a positive trace corner.

