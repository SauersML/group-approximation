---
rg: 2
id: commuting-lamp-mf-radical-is-level-even
kind: claim
title: The MF radical of the commuting-lamp quotient is the level-even lamp subgroup
root: true
distinct_from:
  commuting-lamp-quotient-not-mf: That established claim exhibits one nontrivial radical element; this one computes the whole radical.
  corona-hs-radical-is-finite-residual: That established claim computes the tracial-shadow set as `L_0`; this one proves the operator-norm radical is exactly the same subgroup on this group.
  commuting-lamp-quotient-structure: That established claim identifies the isomorphism type of the group; this one computes its MF radical.
  universal-mf-quotient: That is the generic existence theorem for the universal MF quotient; this one computes that quotient explicitly for one concrete group.
  commuting-lamp-quotient-mf: That resolved claim asks whether the group itself is MF; this one gives the stronger exact radical computation.
---

**Resolved 2026-08-23.**

```text
Rad_MF(W/<zeta>) = L_0,
```

where `L_0` is the level-even lamp subgroup.  Equivalently the universal MF
quotient is

```text
(directSum_(n in Z) C_2) semidirect V,
```

which is residually finite.

## Canonical self-cover proof

The missing self-similarity is not special to the affine coordinates.  For any
one-sided compressor `s Gamma s^-1 <= Gamma`, the homogeneous space `G/Gamma`
has the canonical `G`-equivariant surjective self-cover

```text
r_s(g Gamma) = g s^-1 Gamma.
```

For the affine pair, with `s=tau` and the coordinates from
`commuting-lamp-quotient-structure`, this is exactly

```text
r(n,y) = (n-1,2y),       y in (Z[1/2]/Z)^3.
```

The compression-torsion collapse kills the kernel of the induced lamp
pushforward `R`.  By `radical-automorphization`, every norm-corona
representation then factors through every `R^m`, so the stable kernel
`union_m ker(R^m)` lies in `Rad_MF`.

Now `r^m(n,y)=(n-m,2^m y)`.  Every dyadic-torus element has finite 2-power
order, so two sites are eventually merged iff they lie on the same level.
Therefore the stable pushforward kernel is precisely `L_0`.  This gives the
lower bound `L_0 <= Rad_MF`.

The quotient by `L_0` is the established residually finite level quotient, so
it is MF; the exact-quotient criterion gives the reverse inclusion and hence
equality.

The generic established theorem `wreath-compression-mf-radical` also implies
the same conclusion after identifying the affine quotient with its compression
wreath.  The self-cover route is retained because it supplies the missing
conceptual self-similarity directly and works as a reusable one-compressor
renormalization principle.
