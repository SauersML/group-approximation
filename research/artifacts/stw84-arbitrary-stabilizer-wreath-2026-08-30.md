# Audit: arbitrary-stabilizer permutation wreath bound

Date: 2026-08-30

## Result

For every countable locally finite lamp group `L`, every countable abelian
group `A` of finite rational rank `r`, and every permutation action
`A curvearrowright S`, the generalized wreath product

```text
(direct_sum_S L) rtimes A
```

has nuclear dimension at most `2(r+1)9^r-1` when `r>=1`; its dimension is
zero when `r=0`.  The quotient onto `A` supplies the matching lower bound
`r` in positive rank.

## Finite-stage principle

The full action may have infinitely many stabilizer types.  A finite
approximation does not see all of them.  If its actor is a finitely generated
subgroup `V<=A` and its initial lamp support meets the sites
`s_1,...,s_m`, the required invariant coordinate set is

```text
union_(l<=m) V s_l.
```

Because `A` is abelian, the stabilizer in `V` of every point in the orbit
`V s_l` is the single subgroup `V intersection A_(s_l)`.  The stage therefore
has at most `m` types and the finite-menu theorem applies verbatim.  Its
constant depends only on `rank_Q(V)`, not on the number of types or on the
simultaneous-saturation index.  This uniformity is exactly what is needed by
the directed-union theorem.

## Strictness test

Take

```text
A=Z^2,
H_n=Z(1,n),
S=disjoint_union_(n in Z) A/H_n.
```

Every `H_n` is infinite.  For `m!=n`, `H_m intersection H_n=0`, so the two
rank-one groups are not commensurable.  There are infinitely many types and
no positive-rank subgroup common with finite index to all of them.  Hence the
previous finite-stabilizer, global finite-menu, and common-core statements do
not cover this action, while the new theorem does.

## Boundary audit

Abelianness and the permutation-lamp form remain load-bearing.  For a
nonabelian actor, stabilizers along one orbit are conjugate rather than equal,
so even one orbit can expose infinitely many literal subgroup types to the
finite-menu theorem.  More importantly, an arbitrary locally finite kernel
need not decompose into homogeneous coordinate tensor orbits at all.  Thus
the result does not settle unrestricted locally-finite-by-abelian extensions.
