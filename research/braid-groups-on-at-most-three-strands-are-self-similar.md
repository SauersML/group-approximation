---
rg: 2
id: braid-groups-on-at-most-three-strands-are-self-similar
kind: claim
title: The braid groups B_1, B_2 and B_3 admit faithful self-similar actions on regular rooted trees, transitive on the first level
distinct_from:
  principal-ideal-affine-groups-are-self-similar: that is the affine criterion for R^n x| Gamma over rings with a finite-index principal ideal; this is a single non-affine group, the central extension B_3 of PSL_2(Z), made self-similar through a commensurator element of PSL_2(Z) combined with halving on the center.
  baumslag-char-zero-metabelian-group-is-not-self-similar: that obstructs every state-closed action of one metabelian group; this constructs a faithful transitive state-closed action of the three-strand braid group.
---

**ESTABLISHED.** Review PASS by z-verify-groups at 822b3ac5f2
(`research/artifacts/zp-review-groups-2026-09-13-part2.md` §10, landed d228d90964).
A novelty check is pending.

Call a group `G` *self-similar* when it has a
faithful action on the rooted `d`-regular tree `T_d`, for some `d >= 2`, whose
image is state-closed: every section of every element lies in the image
(Zaremsky's definition, arXiv:2405.09722; Nekrashevych, *Self-similar groups*,
2005, for the transitive case). Then:

1. `B_1 = 1` and `B_2 = Z` are self-similar. For `Z`, the virtual endomorphism
   `2Z -> Z`, `2k -> k` has trivial core, giving the binary adding machine.
2. `B_3` has a faithful self-similar action on `T_12` that is transitive on the
   first level.

The action on `T_12` comes from the virtual endomorphism

```text
H = s(Gamma(2)) x <z^2>  (index 12 in B_3),      F : H -> B_3,
F( s(lambda) z^(2k) ) = F_0(lambda) z^k,
```

where:
- `z = Delta^2` generates the center;
- `pi : B_3 -> PSL_2(Z)` is the quotient by the center;
- `s` is a section of `pi` over the free group `Gamma(2)/{±I}`;
- `F_0` lifts conjugation by `D = diag(2,1)`, which maps `Gamma_0(2)` into
  `SL_2(Z)`.

The core of `F` is trivial for two reasons. Iterating conjugation by `D` forces
the image in `PSL_2(Z)` of an invariant normal subgroup into the upper
unitriangular matrices, where no nontrivial normal subgroup of `PSL_2(Z)` lives.
And on the center, `F` halves exponents. Full derivation:
`braid-groups-three-strands-self-similar-proof`.

This answers the three-strand case of Zaremsky Problem 3.9 positively. For
`n >= 4` see `braid-groups-on-four-or-more-strands-are-not-self-similar`, where
the mapping-class rigidity of `B_n / Z(B_n)` blocks the same trick.

## Attempts

- 2026-09-13 (z3-09 lane): construction above. Novelty was checked only in a
  bounded way. arXiv searches for "self-similar braid group" and "self-similar
  mapping class group" found no treatment, and Zaremsky's list (July 12, 2026)
  still records Problem 3.9 as open. Kapovich (arXiv:0809.0323) proves that an
  irreducible lattice in a semisimple algebraic group admits a faithful
  self-similar action iff it is virtually isomorphic to an arithmetic lattice.
  The `B_3` construction is the central-extension analogue of the arithmetic
  commensurator mechanism for `PSL_2(Z)`.
