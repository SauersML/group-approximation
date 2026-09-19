---
rg: 2
id: stw99-lxxvi-ideal-quotient-permanence-proof
kind: route
title: Restrict the first-factor isomorphism to its support ideal and pass to the Cu quotient
target: stw99-lxxvi-cu-regularity-passes-to-ideals-and-quotients
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Write `F=Cu(iota_A)`.  The inclusion `Cu(I)->Cu(A)` identifies `Cu(I)`
with the corresponding order ideal.  Naturality gives

```text
F(Cu(I)) subset Cu(I tensor Z).                         (1)
```

This restriction is onto.  Indeed, given `y in Cu(I tensor Z)`, choose
`x=[a] in Cu(A)` with `F(x)=y`.  Membership of `[a tensor 1_Z]` in the
order ideal `Cu(I tensor Z)` says that `a tensor 1_Z` belongs to
`I tensor Z` after stabilization.  Applying any slice map
`id tensor omega`, with `omega(1_Z)=1`, shows that `a` belongs to `I` after
stabilization.  Thus `x in Cu(I)`.  Injectivity is inherited from `F`, so
the restriction in (1) is an isomorphism.

Since `Z` is nuclear, tensoring

```text
0 -> I -> A -> A/I -> 0
```

with `Z` is exact and its quotient is canonically
`(A/I) tensor Z`.  Exactness of the Cuntz semigroup functor identifies

```text
Cu(A/I)              ~= Cu(A)/Cu(I),
Cu((A/I) tensor Z)   ~= Cu(A tensor Z)/Cu(I tensor Z).
```

The isomorphism `F` carries the displayed order ideal onto the displayed
order ideal by the first paragraph, hence induces an isomorphism of these
quotients.  Naturality identifies the induced morphism with the
first-factor map for `A/I`.

Finally, a hereditary subalgebra `B subset A` is a full hereditary
subalgebra of `J=Ideal_A(B)`.  The Morita equivalences

```text
Cu(B) ~= Cu(J),                 Cu(B tensor Z) ~= Cu(J tensor Z)
```

intertwine the first-factor maps.  The ideal result for `J` therefore gives
the hereditary result.  Stable-isomorphism invariance is the full-hereditary
special case.
