---
rg: 2
id: continuum-cylinder-via-characteristic-witness-kernels
kind: route
title: Characteristic subgroups of the free witness kernel fill the literal cylinder
target: continuum-nonisomorphic-non-mf-cylinder
requires:
  - literal-witness-kernel-free
  - clopen-non-mf-cylinder
artifacts:
  - research/artifacts/continuum-cylinder-characteristic-kernels-2026-08-30.md
---

Let

```text
pi : E ->> W
```

be the canonical Clifford-witness quotient and put `K=ker(pi)`.  By
`literal-witness-kernel-free`, `K` is a free group of countably infinite rank,
while `pi(w)` is the nontrivial Clifford sign.  In particular, `w` does not
belong to `K`.

R. M. Bryant proved that a free group of countably infinite rank has continuum
many distinct characteristic subgroups.  Choose such a family `(C_i)`.  Since
`K` is normal in `E`, conjugation by every element of `E` restricts to an
automorphism of `K`.  Characteristicity therefore gives

```text
C_i normal E,       C_i <= K,       w notin C_i.                 (CC1)
```

Thus every quotient `E/C_i`, with its marking induced by the eight literal
generators, satisfies all forty-one literal relators and still has `w != 1`.
It lies in the cylinder of `clopen-non-mf-cylinder`, so it is finitely
generated and non-MF.

It remains only to forget the markings without losing cardinality.  Fix a
countable group `Q`.  Every `C_i` for which `E/C_i` is abstractly isomorphic to
`Q` is the kernel of an epimorphism `E ->> Q`.  An epimorphism out of the
eight-generated group `E` is determined by the eight generator images, and
`Q^8` is countable.  Hence each abstract-isomorphism fibre of

```text
C_i |-> isomorphism type of E/C_i
```

is countable.  A continuum-sized set with countable fibres has continuum-sized
image.  Taking one representative from each fibre gives continuum many
pairwise non-isomorphic groups in the literal non-MF cylinder.

The cited source is R. M. Bryant, *Characteristic subgroups of free groups*,
in M. F. Newman (ed.), *Proceedings of the Second International Conference on
the Theory of Groups*, Lecture Notes in Mathematics 372, Springer (1974),
141--149, [doi:10.1007/BFb0065165](https://doi.org/10.1007/BFb0065165).

