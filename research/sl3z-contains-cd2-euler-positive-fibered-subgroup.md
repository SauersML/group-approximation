---
rg: 2
id: sl3z-contains-cd2-euler-positive-fibered-subgroup
kind: claim
title: SL_3(Z) contains a two-dimensional subgroup with nonzero Euler characteristic fibring over Z with finitely generated kernel
---

There is a subgroup `G <= SL_3(Z)` of type FP with `cd G = 2`,
`chi(G) = sum_k (-1)^k dim_Q H_k(G; Q) != 0`, and an epimorphism
`phi: G -> Z` whose kernel is finitely generated.

By `sl3z-incoherent-via-euler-fibered-subgroup` its kernel is then finitely
generated and not finitely presented.

**Necessary conditions on any such `G`** (from the established region):

- `ker phi` is a finitely generated, not finitely presented subgroup, so it is
  Zariski dense (`sl3z-non-zariski-dense-fg-subgroups-are-fp`). Hence `G` is
  Zariski dense.
- `G` has infinite index. Finite-index subgroups of `SL_3(Z)` have property
  (T) (Kazhdan), so they have finite abelianization and no epimorphism onto
  `Z`.
- `G` contains no `Z x F_2` (`sl3z-products-of-infinite-subgroups-are-polycyclic`).
- `G` has no infinite normal solvable subgroup. Its Zariski closure would be
  a normal solvable subgroup of `SL_3`, hence finite.
- The centralizer of the Zariski-dense kernel `N` is central in `SL_3`, so it
  is trivial in `SL_3(Z)`. So `G` acts faithfully on `N` by conjugation,
  `G/N` embeds in `Out(N)`, and the monodromy has infinite order in `Out(N)`.

## Attempts

- 2026-09-13 (z3-04-sl3z-incoherent): free-by-free thin subgroups
  `F_n x| F_m` with `n, m >= 2` have `cd = 2` and `chi = (n-1)(m-1) > 0`.
  - They need a character nonzero on the fibre with finitely generated
    kernel. Kropholler–Walsh study such fibrations of free-by-free groups; the
    exact statements were not re-verified.
  - Inside `SL_3(Z)` the normal `F_n` must be Zariski dense, and `F_m` must
    embed in the stabilizer in `Out(F_n)` of the conjugacy class of the
    inclusion `F_n -> SL_3(C)`. That forces the inclusion out of every region
    of the character variety where `Out(F_n)` acts properly. Lead to test:
    properness of the `Out(F_n)` action on projective Anosov representations,
    not re-verified.
- No candidate is known to exist; no obstruction to existence is known.
