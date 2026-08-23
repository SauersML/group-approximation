---
rg: 2
id: iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree
kind: claim
title: The Iwahori dual inclusion graph is finite-quotient fusion, not the Bruhat--Tits tree
distinct_from:
  pure-dyadic-regular-iwahori-mixtures-have-a-uniform-half-loss: that gets expansion after overlaying the upper and opposite conductor coordinates with Plancherel weights; this proves one restriction/induction graph alone has closed selected-irrep sectors and no Kesten gap.
  dyadic-radial-shell-couplings-have-one-third-boundary: that computes expansion for spatial Iwahori orbits in the Bruhat--Tits tree; this distinguishes the representation-category graph and proves the spatial Kesten intuition cannot be transferred to it.
  depth-two-clifford-types-form-a-finite-fiber-folner-graph: that treats SL3 last-two-layer orbit labels over a coweight lattice; this gives an exact rank-one fusion identity and literal zero-boundary Clifford sectors at each finite level.
---

Let

```text
G_a=SL_2(Z/2^a),       B_a<G_a
```

be the upper Iwahori image, and let `R_a` be the restriction matrix from
`Irr(G_a)` to `Irr(B_a)`. The index is three. Put

```text
P_a=C[G_a/B_a].                                         (DIF1)
```

Then

```text
(R_a^*R_a)_(pi,sigma)
 = <pi, sigma tensor P_a>_(G_a).                        (DIF2)
```

Thus `R_a^*R_a` is the fusion matrix of the three-dimensional permutation
object `P_a`. It is not adjacency on the spatial three-regular
Bruhat--Tits tree. The Perron eigenvalue is `dim(P_a)=3`, so the top singular
value of `R_a` is `sqrt(3)`.

More importantly, `P_a` is inflated from

```text
G_a/ker(G_a->SL_2(F_2)) = SL_2(F_2)=S_3.               (DIF3)
```

Hence it is trivial on the principal congruence kernel

```text
K_a=ker(G_a->SL_2(F_2)).
```

If two `G_a`-irreducibles are joined by fusion with `P_a`, their restrictions
to `K_a` have the same Clifford orbit of irreducible constituents. Therefore
the dual inclusion graph splits as a disjoint union of closed sectors indexed
by those `G_a`-orbits. On every nonempty sector `C`, the restricted dimension
vector

```text
d_C=(dim(pi))_(pi in C)
```

is a Perron vector with eigenvalue three:

```text
(R_a^*R_a)d_C=3d_C.                                    (DIF4)
```

For `a>=2` there are nontrivial sectors in addition to the inflated/trivial
kernel sector. Consequently the eigenvalue three has multiplicity greater
than one and there is no bound by `2sqrt(2)<3` on the complement of the
global dimension vector. Each selected nontrivial sector has exactly zero
weighted boundary in the one-sided representation-category graph.

For `a>=2`, the same conclusion is visible on the newest congruence layer. Its additive
Clifford module is `sl_2(F_2)`, and the dual conjugation action of `S_3` has
orbit sizes

```text
1,1,3,3.                                               (DIF5)
```

Tensoring by `P_a` cannot change any of these orbit labels.

Therefore a Kesten argument on one restriction/induction correspondence
cannot control selected non-Plancherel irreducibles. The only possible dual
expansion must come from overlaying the upper fusion decomposition with the
**opposite Nielsen-shifted** decomposition. The regular theorem proves that
this overlay expands after Plancherel averaging, but `(DIF2)--(DIF5)` show
why that fact does not automatically extend to one selected Clifford sector.
The remaining theorem must quantify how the anisotropic commensuration moves
the full Clifford orbit together with its projective inertia representation;
the spatial tree norm supplies no substitute.
