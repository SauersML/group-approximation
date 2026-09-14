---
rg: 2
id: product-variety-free-groups-satisfy-permutational-boone-higman
kind: claim
title: If F/N lies in the permutational Boone--Higman class then so does F/[N,N]N^m for every m >= 0, and every finite-rank free group of a product of abelian varieties lies in it
distinct_from:
  free-solvable-groups-satisfy-permutational-boone-higman: that is the torsion-free case m = 0 at every step, through the integral Magnus embedding; this allows any exponent at each step, which reaches the free groups of all products of abelian varieties, including quotients of free solvable groups that the subgroup-closed class does not inherit.
  quasi-linear-groups-satisfy-permutational-boone-higman: that is finitely generated groups linear over finite products of fields; this climbs the derived series through wreath products and uses no linearity beyond finite abelian groups and Z^r.
  magnus-embedding-mod-m-into-wreath-product: that is the embedding F/[N,N]N^m into (Z/m)^r wr F/N; this is the Boone--Higman consequence and its iteration over product varieties.
---

**ESTABLISHED** by `product-variety-pbh-via-mod-m-magnus-and-wreath-closure`. Not
independently reviewed.

## Statement

Let `F` be free of finite rank `r >= 1`. Let `B_A` be the class of groups that embed
in a group admitting an action of type (A)
(`boone-higman-type-a-class-closed-under-finite-extensions`).

- **(a)** If `N` is normal in `F` and `F/N ∈ B_A`, then `F/[N,N]N^m ∈ B_A` for every
  integer `m >= 0`.
- **(b)** For every finite sequence `m_1, ..., m_d` of integers `>= 0`, put `N_0 = F`
  and `N_k = [N_(k-1), N_(k-1)] N_(k-1)^(m_k)`. Then `F/N_d ∈ B_A`.
- **(c)** `F/N_d` is the free group of rank `r` of the product variety
  `A_(m_d) A_(m_(d-1)) ... A_(m_1)`. Here `A_m` is the variety of abelian groups of
  exponent dividing `m`, `A_0` is the variety of all abelian groups, and `UV` is the
  class of extensions of a group in `U` by a group in `V`.

So every finite-rank relatively free group of a product of abelian varieties, and
every subgroup of one, embeds in a finitely presented simple group. Its finitely
generated subgroups have solvable word problem.

## Examples

- All `m_i = 0`: the free solvable groups `S_(r,d)`, already on main.
- `(m_1, m_2, m_3) = (0, 2, 0)`: `F/[F''F'^2, F''F'^2]`, of derived length 3. It is a
  proper quotient of `S_(r,3)`, so `free-solvable-groups-satisfy-permutational-boone-higman`
  does not give it: `B_A` is closed under subgroups, not quotients.
- `A_p A A_p A` (`m = (0, p, 0, p)`). The node
  `kms-hard-fp-rf-groups-lie-in-apapa-variety` places hard finitely presented residually
  finite groups in a variety of this shape; see the artifact for how it compares. The
  relatively free group is in `B_A`. Its quotients, and so those groups, are **not**
  covered here.

## Not claimed

- Arbitrary finitely generated groups in these varieties. `B_A` is closed under
  subgroups, not quotients, and relatively free groups do not contain all
  finitely generated members as subgroups.
- Centre-by-metabelian groups (`free-centre-by-metabelian-groups-satisfy-boone-higman`).

_Orphan sweep (2026-09-14): this node cited `research/artifacts/bh-solvable-general-2026-09-13.md`, which its lane never wrote to the repository and which could not be recovered from the lane transcript._
