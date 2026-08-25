---
rg: 2
id: binary-leavitt-nonzero-roots-have-uniform-corona-rank-scale
kind: claim
title: All nonzero binary-Leavitt roots have one uniform corona rank scale
distinct_from:
  full-leavitt-idempotent-defect-saturation: that proves the marked complementary-idempotent root normally generates every root, with an explicit two-commutator formula; this adds the reverse formula for every nonzero coefficient and records the resulting uniform two-sided corona rank comparison.
  finite-order-normal-generation-controls-corona-rank-scale: that compares any two torsion elements using coefficient-dependent normal words; this supplies normal words of length four in both directions uniformly over every nonzero binary-Leavitt coefficient.
  torsion-normal-generator-has-full-support-corona-core: that reblocks one torsion normal generator to positive density; this shows that after that reblocking every fixed nonzero elementary root has a common positive density floor.
artifacts:
  - research/binary-leavitt-uniform-root-rank-proof.md
  - research/commuting-double-commutator-has-direct-mark-overlap.md
  - research/involution-normal-product-forces-one-factor-overlap.md
---

Let `L=L_(F_2)(1,2)`, put `q=s_1t_1`, and let `n>=4`.  For every nonzero
`a in L` and every elementary root `x_ij(a)` of `St_n(L)`, each of

```text
x_ij(a),                    x_13(q)                    (URR1)
```

is a product of at most four conjugates of the other or its inverse.  The
constant four is independent of `a`, of its Leavitt normal-form length, and
of the root indices.

Consequently, for every norm-matrix-corona representation `rho`, let `p_a`
and `p_q` be the nontrivial spectral projections of the involutions
`rho(x_ij(a))` and `rho(x_13(q))`.  Then

```text
[p_a] <= 4[p_q],                  [p_q] <= 4[p_a]       (URR2)
```

in Murray--von Neumann order.  In coordinate rank germs,

```text
rank(p_a)<=4 rank(p_q),           rank(p_q)<=4 rank(p_a) (URR3)
```

eventually.  Thus the comparison constant between the marked root and
**every** nonzero root is universal rather than coefficient dependent.

After applying `torsion-normal-generator-has-full-support-corona-core` to the
marked root, suppose its active projection has normalized rank at least
`1/L_0`.  Every fixed nonzero elementary root in the reblocked model then has

```text
liminf rank(p_a)/d >= 1/(4L_0).                         (URR4)
```

There is also a uniform direct cross-overlap consequence for every root
position disjoint from the two indices of the marked root.  In particular,
let `p_a` be the active projection of `x_42(a)` and let `p_q` be that of
`x_13(q)`.  The displayed double-commutator output commutes with both of its
conjugating roots, so

```text
tau(p_a p_q) >= tau(p_a)/16 >= tau(p_q)/64.            (URR5)
```

in an exact finite-dimensional representation.  For rounded involutions in
an asymptotic matrix model, both inequalities hold up to `o(1)`.  Thus the
overlap is with the original marked carrier, not an unspecified conjugate of
it.

No Property T, stability, trace expansion, or literature input is used.

This still does not collapse a diffuse root spectrum.  The Haar
representation of an infinite elementary abelian root group gives every
nonzero involution active trace `1/2`, fully compatible with `(URR4)`.  Also,
the coordinate after which `(URR3)` holds may depend on `a`; the theorem does
not permit choosing a coefficient after inspecting the matrix coordinate.
The rank comparisons `(URR2)--(URR4)` still apply to every root position;
only the direct marked overlap `(URR5)` uses a position disjoint from
`{1,3}`.  Even there it does not identify two native scale transports with
one another: two root carriers can each have a positive but disjoint slice
inside the much larger marked carrier.  The remaining decoder must use the
uniform rank/overlap scale together with a mixed-root return or a uniformly
authenticated moving coefficient, rather than infer an atom or a common
gauge from the density floor alone.

DERIVATION
binary-leavitt-uniform-root-rank-proof
