---
rg: 2
id: coprime-power-pair-pro-p-normal-form-proof
kind: route
title: Separate power-pair pinches by cyclic-syllable normal forms in a free pro-p group
target: coprime-power-pair-phase-hnn-is-residually-finite
requires:
  - hnn-mark-collapse-requires-profinite-edge-incompatibility
  - power-pair-pro-p-graph-has-gcd-saturation
---

Fix a prime `p` not dividing `mn`, and write `Fhat_p` for the free pro-`p`
completion of `F`.  The substitutions `phi_m` and `phi_n` extend to
automorphisms of `Fhat_p`: on the Frattini quotient they are multiplication
by the nonzero scalars `m` and `n`, respectively.  Put

```text
beta=phi_n phi_m^(-1) in Aut(Fhat_p).                   (CPH3)
```

Since `gcd(m,n)=1`, `power-pair-pro-p-graph-has-gcd-saturation` gives the
discrete graph-intersection identity

```text
Graph(beta) intersect (F times F)
 ={(phi_m(a),phi_n(a)):a in F}.                         (CPH4)
```

We next make `(CPH4)` finite.  A finitely generated pro-`p` group has a
neighborhood basis at the identity consisting of open characteristic
subgroups: given an open normal subgroup, intersect its finite orbit under
the automorphism group.  Hence, for any finite list of pairs
`(u_j,v_j) in F times F` outside the right side of `(CPH4)`, there is an open
characteristic subgroup `C normal Fhat_p` such that in the finite `p`-group

```text
Q=Fhat_p/C
```

all inequalities

```text
q(v_j)!=beta_bar(q(u_j))                                (CPH8)
```

hold.  We may simultaneously require any finite list of nonidentity elements
of `F` to survive.  Because `C` is characteristic, `phi_m`, `phi_n`, and
`beta` descend to automorphisms of `Q`.

Finally let `w` be a nonidentity Britton-reduced word in `(CPH1)`.  For every
intervening base syllable `(u,v)`:

- forbidden membership in the source subgroup `F times 1` is witnessed by
  `v!=1`, which can be retained in `Q`;
- forbidden membership in the target power-pair graph is retained by
  `(CPH8)` and `(CPH4)`.

Choose one characteristic `C` handling all these finitely many tests (and a
nontrivial base coordinate if `w` has no stable letter).  The kernel of the
source parameter map to `Q times Q` is `F intersect C`.  The kernel of the
target parameter map is

```text
phi_m^(-1)(C) intersect phi_n^(-1)(C)=F intersect C,    (CPH9)
```

because both substitutions preserve `C` and induce automorphisms of `Q`.
Thus the edge isomorphism descends exactly.  Every forbidden pinch survives,
so the image of `w` is Britton reduced and nonidentity in an HNN extension
of the finite base `Q times Q`.  Such an HNN extension is virtually free and
residually finite.  A further finite quotient separates the image of `w`,
proving residual finiteness of `(CPH1)`.
