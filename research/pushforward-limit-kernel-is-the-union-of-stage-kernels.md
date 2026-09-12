---
rg: 2
id: pushforward-limit-kernel-is-the-union-of-stage-kernels
kind: claim
title: The limit kernel of a lamp pushforward tower is the supremum of the stage kernels
distinct_from:
  compression-wreath-five-radicals-coincide: that identifies five radicals of a specific compression wreath group; this is the algebraic union step of the telescope, stated for an arbitrary tower of site maps and an arbitrary abelian lamp, with no radical in it.
  simple-lamp-radical-one-relation: that measures the presentation-theoretic size of a lamp kernel inside one group; this compares the kernels of a tower of pushforwards against their limit.
artifacts:
  - research/artifacts/multi-mover-hnn-dossier-2026-08-15.md
  - GroupApproximation/Algebra/AbelianLampPushforward.lean
  - GroupApproximation/Algebra/AbelianLampTelescopeKernel.lean
---

Let `A` be an abelian lamp value group, `X` a site set, `q_n : X -> Y_n` a tower
of site maps and `q_inf : X -> Z` a limit map, each `q_inf` factoring through
`q_n`.  Suppose every **finite** set of sites is separated at some finite stage
exactly as it is at the limit:

    for every finite S ⊆ X there is n with
      (q_inf x = q_inf y  =>  q_n x = q_n y)  for all x, y in S.

Then, for the pushforward of finitely supported lamp configurations along a site
map,

    ker (push q_inf) = ⨆_n ker (push q_n).

Two supporting facts come with it: pushforward is functorial (`push (r ∘ q) =
push r ∘ push q`), from which the stage kernels **increase**; and pushforward
along an *equivariant* map of site sets commutes with the coordinate
permutations, which is what lets the whole tower be a tower of maps of wreath
products rather than merely of lamp groups.

This is Theorem 37.5 of the dossier, together with the 37.1 pushforward it runs
on.

## Where the hypothesis comes from, and why it holds

In the application the sites are cosets `G/Gamma_0`, the stages are
`G/Gamma_n`, and the limit is `G/N` with `N` the union of the `Gamma_n`.  The
separation hypothesis holds because a finitely supported configuration has
finitely many support sites, so the finitely many coincidences
`g_i^{-1} g_j ∈ N` all occur inside a single `Gamma_n`.  That is the whole
reason a *union* appears in the conclusion: the tower is exhaustive on finite
data, and a `Finsupp` is finite data.

## The two halves are not symmetric

`⊇` is monotonicity plus the factorization.  `⊆` is the content: a
configuration invisible at the limit must already be invisible at some stage.
It is a fibre computation — the value of a pushforward at a target site is the
sum of the source values over the part of the fibre that meets the support, and
under the separation hypothesis the stage-`n` fibre and the limit fibre cut the
support in the same set.

Written additively the whole construction is `Finsupp.mapDomain`, so the
group-theoretic layer costs almost nothing.  Past the first telescope stage the
lamp group is abelian, which is why the abelian model suffices here even though
the repository also carries the general, possibly nonabelian, `Lamp K X`
pushforward; the limit-kernel arithmetic needs nothing about wreath products.
