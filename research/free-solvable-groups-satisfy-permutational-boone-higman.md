---
rg: 2
id: free-solvable-groups-satisfy-permutational-boone-higman
kind: claim
title: Every free solvable group, and every F/N^(d) with F/N in the permutational class, lies in the permutational Boone--Higman class
distinct_from:
  fp-metabelian-groups-satisfy-boone-higman: that is the finitely presented metabelian class, reached through quasi-linear groups; this reaches free solvable groups of every derived length, for which no linear route is recorded on main.
  quasi-linear-groups-satisfy-permutational-boone-higman: that is groups of matrices over finite products of fields; this passes from F/N to F/[N,N] through the Magnus embedding and uses no linearity beyond Z^r.
  permutational-boone-higman-closed-under-wreath-products: that is the general permanence under restricted wreath products; this applies it along the Magnus embedding to presentations.
artifacts:
  - research/artifacts/solve-bh-free-solvable-2026-09-13.md
---

**ESTABLISHED** by `free-solvable-pbh-via-magnus-and-wreath-closure`. Not
independently reviewed.

## Statement

Let `F` be a free group of finite rank `r >= 1`, and let `B_A` be the class of groups
that embed in a group admitting an action of type (A).

- **(a)** If `N` is normal in `F` and `F/N ∈ B_A`, then `F/[N, N] ∈ B_A`.
- **(b)** If `F/N ∈ B_A`, then `F/N^(d) ∈ B_A` for every `d >= 0`. Here
  `N^(0) = N` and `N^(d) = [N^(d-1), N^(d-1)]`.
- **(c)** For all `r >= 1` and `d >= 1`, the free solvable group
  `S_(r,d) = F/F^(d)` lies in `B_A`.

So every free solvable group, and every subgroup of one, embeds in a finitely
presented simple group.

## Context

- **Solvable groups of class three are not a Boone--Higman class wholesale.**
  Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3, footnote 9 (extracted text on
  MSI, l.907--911): "By a theorem of Baumslag and Remeslennikov, every finitely
  generated metabelian group embeds into a finitely presented one [4, 94]. Such
  groups have solvable word problem [5], though the same does not hold for solvable
  groups of derived length three [69]." Free solvable groups do have solvable word
  problem. Magnus's embedding reduces it to that of `F/N` (arXiv:0807.1032,
  l.310--327), and it also follows from (c).
- **Beyond metabelian.** `fp-metabelian-groups-satisfy-boone-higman` settles item (7)
  of BBMZ Problem 5.3 through quasi-linear groups. For `d >= 3` no linear or
  quasi-linear embedding of `S_(r,d)` is recorded on main or was found. Mal'cev's
  theorem makes a non-linearity proof expected, since solvable quasi-linear groups
  are virtually nilpotent-by-abelian. That proof is not written here.
- **Examples of (b).** `F/N^(d)` for every finitely generated characteristic-zero
  linear quotient `F/N` of `F`. For instance `N` can be the kernel of a surjection
  `F_2 -> SL_2(Z)`.
- **Novelty.** Bounded search in the artifact. Boone--Higman for free solvable
  groups of class at least three was not found in:
  - the BBMZ survey;
  - BFFHZ arXiv:2503.21882v2;
  - Fournier-Facio--Wu--Zaremsky arXiv:2603.24687;
  - arXiv:2609.01868;
  - two web searches.

  No priority is claimed beyond that.

## Not claimed

- Boone--Higman for finitely generated solvable groups with solvable word problem in
  general.
- Relatively free groups not of the form `F/[N, N]`, such as free
  centre-by-metabelian groups `F/[F'', F]`.
