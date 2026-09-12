---
rg: 2
id: simple-torsion-groups-have-a-macroscopic-mf-dichotomy
kind: claim
title: A finitely generated simple torsion-marked group is either an MF black hole or macroscopically MF
artifacts:
  - notes/EXACT_CORONA_DIMENSION_AND_HILBERT_HOTEL.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED.**  Let `G` be a nontrivial finitely generated simple group
containing an element `a` of finite order.  Exactly one of the following
holds.

1. `Rad_MF(G)=G`, so every homomorphism from `G` to every norm matrix corona
   is trivial.
2. `G` has an operator-norm asymptotic representation `sigma_n:G->U(k_n)`
   which is injective in the norm corona and satisfies
   ```text
   liminf_n ||sigma_n(g)-1||_2 > 0
   ```
   for every `g!=1`.  Moreover the active spectral projection of `a` has
   normalized rank bounded below by a constant determined by finitely many
   normal-generation words for a generating set.

Consequently, for this class of groups the following are equivalent:

```text
G is operator-MF;
G has a faithful operator-norm asymptotic model that is pointwise
  Hilbert--Schmidt separating;
G has a nontrivial norm-corona homomorphism.
```

If `G` is uniformly simple, the middle condition may be strengthened to one
uniform positive Hilbert--Schmidt separation constant on all of `G\{1}`.

This dichotomy applies in particular to simple elementary groups over the
binary Leavitt ring.  Their property-`(T)`-free MF question is therefore a
macroscopic tracial question: microscopic operator-norm separation cannot be
the surviving case.

Equivalently, on every such simple group the MF radical agrees with the
universal operator-to-Hilbert--Schmidt shadow residual.
