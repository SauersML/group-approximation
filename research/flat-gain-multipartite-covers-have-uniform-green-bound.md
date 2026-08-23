---
rg: 2
id: flat-gain-multipartite-covers-have-uniform-green-bound
kind: claim
title: Flat gain covers of multipartite clique complexes have the base Green bound
distinct_from:
  multipartite-triangle-curl-has-uniform-infinity-green-bound: that computes the untwisted base Green operator; this proves every genuine finite gain cover is gauge-equivalent to disjoint copies of that operator.
  proper-torus-reynolds-is-edge-refinement: that shows the arithmetic label refinement omits the deck translates of every triangle; this proves deck degree alone is harmless when all those translates are present.
  right-u-reynolds-has-torus-hecke-blocks: that gives the nontrivial harmonic blocks of the incomplete arithmetic refinement; this treats flat gain/local-system blocks on a genuine cover.
---

**ESTABLISHED; FLAT-GAIN NO-GO.**  Let `X_(r,m)` be the clique complex of
the complete `r`-partite graph `K_(m,...,m)`, with `r>=3`.  Let `K` be any
finite deck group and assign gains

```text
g_(xy) in K,              g_(yx)=g_(xy)^(-1)           (FGC1)
```

to its oriented edges.  Assume the gain is flat on every triangle:

```text
g_(xy) g_(yz) g_(zx)=1.                                (FGC2)
```

Then there are vertex labels `t_x in K` such that

```text
g_(xy)=t_x^(-1)t_y.                                    (FGC3)
```

Indeed `X_(r,m)` is the join of `r` nonempty discrete spaces.  A join of
`r>=3` nonempty discrete spaces is simply connected.  Equation `(FGC2)`
says exactly that the gain of a path is unchanged by each triangular
homotopy, so its value from one fixed base vertex to `x` is path
independent.  Taking that value as `t_x` proves `(FGC3)`.

Consequently the regular `K`-cover defined by `(FGC1)` is gauge-isomorphic
to the trivial cover

```text
X_(r,m) x K.                                           (FGC4)
```

The gauge map sends `(x,k)` to `(x,t_x k)` and is a permutation of the
lifted coordinates, hence an isometry for both the counting Hilbert norm
and the infinity norm.  Under this gauge, triangle curl is the direct sum
of `|K|` copies of the untwisted operator:

```text
delta_(1,gain) ~= direct_sum_(k in K) delta_1.         (FGC5)
```

The same statement holds after applying any unitary representation of
`K`: every twisted local-system block is unitarily gauge-equivalent to an
untwisted block (using the supremum over vertices of the coefficient
Hilbert norm).  In particular this applies isometrically to every scalar
character block.  Functional calculus in `(FGC5)` gives the identical
decomposition for the Moore--Penrose inverse.  Therefore, on the regular
cover in scalar coordinates,

```text
||delta_(1,gain)^dagger||_(infinity -> infinity)
 =||delta_1^dagger||_(infinity -> infinity)
 <=1+2(r+1)/(r(r-1))<=7/3,                             (FGC6)
```

where the inverse domain has its inherited range infinity norm.  The
bound is completely independent of `|K|` and of the chosen flat gains.

Thus deck degree and character phases cannot themselves create a divergent
multipartite Green kernel.  Any bad proper-subtorus mode must use a failure
of `(FGC2)` or, as in the actual Reynolds refinement, the absence of most
triangle lifts.  This is why the nontrivial torus-character Hecke blocks
cannot be replaced by an ordinary flat local system.
