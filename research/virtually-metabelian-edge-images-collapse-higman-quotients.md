---
rg: 2
id: virtually-metabelian-edge-images-collapse-higman-quotients
kind: claim
title: In a nontrivial quotient of Higman's group neither opposite pair generates a virtually metabelian group, of any rank, so tree splittings over virtually metabelian edge groups are impossible
distinct_from:
  nilpotent-edge-images-collapse-higman-quotients: that kills images of finite Hirsch length (virtually nilpotent, virtually polycyclic, BS(1,n)); this kills every virtually metabelian image, including infinite-rank ones such as Z wr Z and the free metabelian group, by proving they would have finite Hirsch length.
  nontrivial-higman-quotients-are-not-locally-elementary-amenable: that forbids homomorphisms from a quotient to elementary amenable targets; this constrains a subgroup of the quotient, which receives no homomorphism from the quotient.
  almost-commuting-opposite-higman-generators-force-collapse: that is the abelian case; this is the metabelian case.
---

**ESTABLISHED** by `higman-metabelian-edge-collapse-proof`.

**Statement.** Let `Q` be a quotient of
`H4 = < a, b, c, d | b^a = b^2, c^b = c^2, d^c = d^2, a^d = a^2 >` (`x^y = y^-1 x y`).

1. **Metabelian powers collapse.** If for some `m >= 1` the subgroup `<a^m, c^m>` of `Q` is
   metabelian, then `Q = 1`. The same holds for `<b^m, d^m>`.
2. **Virtually metabelian images collapse.** If the image of `<a,c>` or of `<b,d>` in `Q` is virtually
   metabelian, then `Q = 1`.
3. **Trees.** Suppose `Q != 1` acts on a tree without inversions, and each edge stabilizer is virtually
   metabelian or virtually solvable of finite Hirsch length. Then `Q` fixes a vertex. So a nontrivial
   quotient of `H4` never splits as an amalgam or HNN extension over such a subgroup.

**Mechanism.** Put `alpha = a^m`, `gamma = c^m`, `P = 2^m` and `z = [gamma, alpha]`. Two one-sided
facts combine.
- **The `b` side.** Conjugation by `b^P` maps `<gamma, gamma^alpha>` into itself, with
  `gamma -> gamma^(2^P)` and `gamma^alpha -> (gamma^alpha)^2`. It sends `z` to `gamma^(2-2^P)` times an
  element of the abelian group `W` spanned by the `gamma`-conjugates of `z`. The image of `W` is abelian,
  so all but one rank of it is centralized by `gamma^(2-2^P)`. That bounds `rank W` by the rank of the
  fixed points of `gamma^(2-2^P)` on a cyclic `Z[T^±1]`-module, which is finite. So `z` is killed by a
  polynomial in conjugation by `gamma` on `A_1' ⊗ Q`, where `A_1 = <alpha, gamma>`.
- **The `d` side.** The relations `d^c = d^2`, `a^d = a^2` give the same with `alpha` and `gamma`
  swapped. So `z` is also killed by a polynomial in conjugation by `alpha`.
- **Together.** `A_1' ⊗ Q` is a cyclic module over `Q[X^±1, Y^±1]` killed by `p(Y)` and `q(X)`. So it is
  finite-dimensional, `A_1` has finite Hirsch length, and `nilpotent-edge-images-collapse-higman-quotients`
  (distinct-eigenvalue count) forces `Q = 1`.

**Calibration.** Each side alone is consistent. The group `G_1 = < a, b, c | b^a = b^2, c^b = c^2 >` has
the solvable quotient `N ⋊ BS(1,2)`, with `N` induced from `Z[1/2]` on `<b>`. There `c` and `b` have
infinite order and `<a,c> ≅ Z wr Z`. The `b`-side bound holds, since the `c`-span of `z` is
one-dimensional. The `d`-side bound fails, since the `a`-span is infinite-dimensional. It is the second
Baumslag--Solitar pair that is missing. For exponent 1 in place of 2 (the RAAG-like variation with
quotient `Z^4`) `2 - 2^P` becomes `0` and the argument is silent, as it must be.

**What it kills.** Attempt 5 of `higman-group-is-sofic` glues a sofic quotient `G_1'` of `<a,b,c>` to its
relabelled copy over the amenable image `A` of `F_ac`. The glued group is a nontrivial quotient of `H4`
containing `A` as the image of `<a,c>`. By item 2 the construction collapses whenever `A` is virtually
metabelian. This includes `Z wr Z` and the free metabelian group, the infinite-rank edge groups that
`nilpotent-edge-images-collapse-higman-quotients` left open. By item 3 the same holds for any
tree-of-groups construction over such edge groups. What survives are amenable edge images that are
not virtually metabelian and have infinite Hirsch length, for example derived length at least 3.
Non-elementary-amenable images also survive.
