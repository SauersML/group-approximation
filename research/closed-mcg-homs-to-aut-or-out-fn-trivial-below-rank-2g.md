---
rg: 2
id: closed-mcg-homs-to-aut-or-out-fn-trivial-below-rank-2g
kind: claim
title: Every homomorphism from the closed genus-g mapping class group to Aut(F_n) or Out(F_n) with n at most 2g minus 1 is trivial for g at least three, so a host of an embedding needs n at least 2g
distinct_from:
  rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg: that bounds the rank of a host of an embedding through dimension and gives n at least 2g minus 1; this makes every homomorphism in rank at most 2g minus 1 trivial or finite, and gives n at least 2g for a host.
  closed-mcg-twists-map-to-polynomially-growing-outer-autos: that constrains the image of each Dehn twist under a homomorphism in every rank; this kills the homomorphism outright in low rank.
---

**ESTABLISHED** by citation, `korkmaz-closed-mcg-free-group-hosts-citation`. No
novelty is claimed.

`MCG(S_g)` is the orientation-preserving mapping class group of the closed
orientable surface of genus `g`, and `H` is `Aut(F_n)` or `Out(F_n)`.

1. If `g ≥ 3` and `n ≤ 2g − 1`, every homomorphism `MCG(S_g) → H` is trivial.
2. If `g = 2` and `n ≤ 3`, every homomorphism `MCG(S_2) → H` has image a quotient
   of `Z/10`.
3. If `g ≥ 2` and `MCG(S_g)` embeds in `Aut(F_n)` or in `Out(F_n)`, then `n ≥ 2g`.

Item 3 improves item 2 of `rank-lower-bounds-for-free-group-hosts-of-out-fm-and-mcg`
by one. For `some-closed-surface-mcg-embeds-in-no-out-free-group` it is only a
constraint on the rank of a host, since the constructions of
`low-genus-closed-mcgs-embed-in-aut-free-groups` and
`aut-free-embeddability-passes-to-finite-index-overgroups` go through large ranks.
Whether the closed group maps nontrivially to `Aut(F_{2g})` or `Out(F_{2g})` is not
recorded in this graph; the bordered group `MCG(S_{g,1})` embeds in `Aut(F_{2g})` by
Dehn--Nielsen--Baer.
