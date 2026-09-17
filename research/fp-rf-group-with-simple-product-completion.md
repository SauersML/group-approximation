---
rg: 2
id: fp-rf-group-with-simple-product-completion
kind: claim
title: Some finitely presented residually finite group has an open product of simple groups of unbounded order in its profinite completion
distinct_from:
  fp-rf-group-with-unbounded-prime-torsion: that asks for torsion of infinitely many prime orders; this asks for a profinite shape and says nothing about torsion. The torsion-free Kassabov--Nikolov style candidates belong here, not there.
  kassabov-nikolov-alternating-frames-are-not-fp: that shows the known frames for products of alternating groups are not finitely presented; this asks for a finitely presented group with a product completion, and by fp-groups-have-no-multiplier-product-completions its factors cannot be alternating.
  some-fp-rf-group-acts-on-no-regular-rooted-tree: that is the weaker target; this is one sufficient mechanism for it, through simple-product-completions-block-regular-tree-actions.
---

**OPEN.** There is a finitely presented residually finite group `Γ` such that
some open subgroup of `Γ^` is isomorphic to `prod_(i in I) S_i`, where:
- every `S_i` is a nonabelian finite simple group;
- for every `m`, only finitely many `i` satisfy `|S_i| <= m`.

If established, `simple-product-completions-block-regular-tree-actions` shows
that `Γ` acts faithfully on no regular rooted tree. Route
`fp-rf-tree-obstruction-via-simple-product-completion` then establishes
`some-fp-rf-group-acts-on-no-regular-rooted-tree` and refutes
`every-fp-rf-group-embeds-in-fp-self-similar-group`.

## Necessary conditions

- **(SPC1) Multipliers.** For every prime `p`, only finitely many `S_i` have `p`
  dividing `|H_2(S_i; Z)|`. This is forced by
  `fp-groups-have-no-multiplier-product-completions`, since for perfect `S_i`,
  `H^2(S_i; F_p) = Hom(H_2(S_i; Z), F_p)`. It excludes products of alternating
  groups and every family of `PSL_2(q)` with `q` odd.
- **(SPC2) Not through congruence completions.** Suppose `Γ` is an arithmetic
  group with the congruence subgroup property. Then `Γ^` is virtually a product
  of open compact subgroups of `G(Q_l)`, and those are virtually pro-`l`. Pro-`l`
  groups have no nonabelian simple quotients, so no open subgroup is a product
  of this kind. This remark is not claimed as established; it only steers the
  search.
- **(SPC3) Candidates.** The survivors of (SPC1) are families of groups of Lie
  type with multipliers coprime to each fixed prime from some point on, such as
  `SL_2(2^k)` or `SL_3(q)` with `3` not dividing `q - 1`.
  - A candidate must be a finitely presented group whose finite quotients are,
    virtually, exactly the finite products of such groups.
  - Kassabov--Nikolov style frames for such products would contain the
    restricted product. `products-of-finite-groups-with-schur-factors-not-fp`
    does not exclude them when the multipliers are trivial. Whether any such
    frame is finitely presented is not settled here.
- **(SPC4) Profinite presentability is necessary.** `prod S_i` must be finitely
  presented as a profinite group. By Lubotzky's criterion (*Pro-finite
  presentations*, J. Algebra 242 (2001)), this bounds `dim H^2(S_i; M)` linearly
  in `dim M` over irreducible modules `M`. The criterion is not imported here,
  and it is not sufficient for a discrete finitely presented group to exist.

## Attempts

1. **Alternating and odd `PSL_2` factors (2026-09-17). DEAD.** Excluded for
   every finitely presented group by
   `fp-groups-have-no-multiplier-product-completions`, not only for frames that
   contain the restricted product.
