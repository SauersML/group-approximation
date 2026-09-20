---
rg: 2
id: poly-z-subgroups-bound-cantor-crossed-host-dimension
kind: claim
title: "If k[G] embeds unitally in a matrix ring over LC(X, k) ⋊ P, then cd_k P is at least the Hirsch length of every poly-Z subgroup of G; so Thompson's group F forces cd_k P = ∞"
distinct_from:
  finite-field-polynomial-growth-hosts-bound-commuting-rank: that bounds commuting rank in gauge-homogeneous, bounded-propagation pieces over finite fields by dimension counting. This bounds the acting group's cohomological dimension, for every unital embedding over every field, by the Hirsch length of non-abelian poly-Z subgroups, which exceeds every commuting rank (Heisenberg group 3 against 2).
  finite-cd-line-groups-bound-disjointly-supported-families: that bounds disjointly supported families in a finite-cd group acting on the line. This bounds the acting group of a Cantor crossed product from below by the subgroups of a group whose group algebra it contains.
  decidable-group-algebras-have-fp-cantor-crossed-hosts: that is the existence claim. This is a necessary condition on its witnesses, and it does not refute it.
invalidates:
  - cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts
---

**ESTABLISHED** by `poly-z-host-bound-via-ore-localized-hochschild-homology` (unreviewed).

Let `k` be a field and `P` a group acting by homeomorphisms on a compact Hausdorff totally disconnected
space `X`, and put `B = LC(X, k) ⋊ P`, the algebraic crossed product. Let `G` be a group and suppose
`k[G] -> M_r(B)` is a unital injective algebra map for some `r >= 1`. No finite presentation, simplicity,
minimality or freeness is assumed.

1. **Ore subgroups.** Let `H <= G` be a subgroup such that `kH` is an Ore domain (both sides), with
   `n = cd_k H < ∞` and `H_n(H; k) ≠ 0`. Then `cd_k P >= n`.
2. **Poly-Z subgroups.** If `H <= G` is poly-`Z` of Hirsch length `h`, then `cd_k P >= h`.
3. **Unbounded rank.** If `G` has poly-`Z` subgroups of unbounded Hirsch length, for example free abelian
   subgroups of every rank, then `cd_k P = ∞`.

**Instances.**
- `G = Z^m`: `cd_k P >= m`. Sharp at `P = Z^m`, `X` a point.
- The Heisenberg group `UT_3(Z)`: `cd_k P >= 3`, while its abelian subgroups have rank at most `2`. More
  generally `UT_n(Z)` gives `n(n-1)/2`, against a largest abelian rank of `⌊n^2/4⌋`.
- `SL_n(Z)`, `n >= 3` (finitely presented, decidable, containing `UT_n(Z)`): `cd_k P >= n(n-1)/2`, which is its
  virtual cohomological dimension.
- **Thompson's group `F`** (finitely presented, torsion-free, solvable word problem, containing `Z^m` for every
  `m` through elements with disjoint supports): every host has `cd_k P = ∞`. The same holds for every `G`
  containing `Z ≀ Z`.

**Consequences for the Boone–Higman chain.**
- *Finite-dimensional acting groups are dead for* `decidable-group-algebras-have-fp-cantor-crossed-hosts`,
  already at the single input `G = F`. That kills every `P` of finite `cd_(F_2)`: `Z^2`, `Z^2 × F_d`, every
  hyperbolic group, every finite-dimensional CAT(0) group, every torsion-free lattice, the congruence subgroups
  of `PSL_2(Z[1/p])` of Attempt 12 of that claim, right-angled Artin groups, and solvable groups of finite
  Hirsch length.
- Boundary products `(P, X) ↦ (P × F_d, X × ∂F_d)` raise `cd` by at most one. So no tower of them over a
  finite-dimensional seed reaches `G = F`. Hence `cantor-crossed-hosts-via-boundary-products-of-z2-sft-hosts`
  cannot close; its prerequisite (E) fails at `G = F` and at `G = Z^4`.
- A witness at `G = F` must be a finitely presented torsion-free Farrell–Jones group of infinite `cd_(F_2)`.
  Such groups exist: Baumslag's finitely presented metabelian group, which contains `Z ≀ Z`, is torsion-free
  and solvable, hence Farrell–Jones by Wegner (recalled). Among the classes with a recalled Farrell–Jones
  theorem, the only finitely presented members of infinite dimension come from solvable groups of infinite
  Hirsch length and from subgroups of products involving them. Amenable ones are gated by linear soficity (that
  claim's Attempt 3). This census is heuristic, not a theorem.

**Where it does not reach.**
- The units-only weakening `decidable-groups-embed-in-cantor-crossed-leavitt-tensor-units`. `L_2` contains
  Thompson's `V ⊇ Z^m` in its unit group while `k[Z^2]` does not embed in it, so unit embeddings carry no such
  bound.
- Non-unital embeddings. For polynomial rings they reduce to the unital case; for group algebras the corner
  `eM_r(B)e` is not controlled here.
- Groups without poly-`Z` (or Ore) subgroups of large Hirsch length, for example `F_2` or `BS(1,2)`, where
  `H_2(BS(1,2); F_2) = 0`.
