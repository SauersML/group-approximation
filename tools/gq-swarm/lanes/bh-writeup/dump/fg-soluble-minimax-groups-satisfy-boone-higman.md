---
rg: 2
id: fg-soluble-minimax-groups-satisfy-boone-higman
kind: claim
title: Every finitely generated soluble minimax group (equivalently, of finite Prüfer rank) embeds in a finitely presented simple group
distinct_from:
  rf-soluble-minimax-groups-satisfy-permutational-bh: that is the residually finite part, which is ESTABLISHED through linearity; this includes the groups with infinite radicable torsion radical, which are not residually finite and not linear.
  abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center: that is a soficity calibration for a quotient of Abels' group by a finite central subgroup; this is Boone--Higman for the whole finite-rank soluble class, whose hard cases are quotients by infinite central subgroups.
artifacts:
  - research/artifacts/gq-bh-bh-solvable-status.md
---

**OPEN.** Let `G` be a finitely generated soluble group of finite Prüfer rank
(equivalently minimax, by the facts recalled in Pyber--Segal, arXiv:0711.0687, §3).
Then `G` embeds in a finitely presented simple group.

## What is known

- **Residually finite case: ESTABLISHED.**
  `rf-soluble-minimax-groups-satisfy-permutational-bh`
  puts every such `G` with `τ(G)` finite in `B_A`. Here `τ(G)` is the maximal
  periodic normal subgroup.
- **Word problem.** Cannonito and Robinson, "The word problem for finitely generated
  soluble groups of finite rank", Bull. London Math. Soc. 16 (1984), is the expected
  source that every such `G` has solvable word problem. Only the title and journal
  were checked (Crossref, doi:10.1112/blms/16.1.43); the paper was not read. So this
  node is stated as an embedding claim, and it is a Boone--Higman instance only once
  that input is confirmed.

## The remaining case

Suppose `τ(G)` is infinite. For minimax `G` this is the non-residually-finite case
(Pyber--Segal §3 list). Such `G` contains a quasi-cyclic group `C_(p^∞)`, since an infinite periodic soluble minimax group is Chernikov (standard; not re-read here).

**Calibration example (lane computation, elementary).** Let `A_p` be Abels' group of
upper triangular `4×4` matrices over `Z[1/p]` with diagonal `(1, p^a, p^b, 1)`, and
let `C = {e_14(n) : n ∈ Z}`, a cyclic subgroup of the center `e_14(Z[1/p])`. Then
`A_p/C` is finitely generated soluble minimax, not residually finite, and its word
problem is solvable: reduce a word to its matrix in `A_p` and test whether it equals
`e_14(n)` with `n ∈ Z`.
- `A_p/C` is the unit group, restricted to diagonal `(1, p^a, p^b, 1)`, of the
  generalized triangular ring `T` with diagonal corners `Z, Z[1/p], Z[1/p], Z`,
  off-diagonal entries `Z[1/p]` except the `(1,4)` corner, which is the
  `(Z,Z)`-bimodule `Z[1/p]/Z`. Products into the corner are
  `Z[1/p] ⊗_(Z[1/p]) Z[1/p] → Z[1/p] → Z[1/p]/Z`; they are balanced over the middle
  corners. The `(1,4)` entry of a product in `A_p` is `h_14 + g_12h_24 + g_13h_34 + g_14`,
  so reduction mod `Z` is a homomorphism with kernel `C`.
- So these groups are "linear over a ring" with a divisible torsion corner. Every
  `B_A` producer on main is residually finite (self-similar affine groups over
  polynomial rings, `S`-integer hosts), so none applies.

## What a proof needs

Either:
- (a) a host that is not residually finite and admits finitely presented simple
  envelopes, and contains `A_p/C`-type central quotients; or
- (b) a permanence theorem that `B_A`, or embeddability in finitely presented simple
  groups, passes from `H` to `H/Z` for a central subgroup `Z` with `H/Z` of solvable
  word problem. That is a quotient statement, and quotients are not known to preserve
  either class.

## Attempts

1. Lane `bh-solvable`, 2026-09-18. Central-product tricks `H ×_Z U` recover `H/C` only
   when `U` is `H/C`'s own center, so they give nothing. No non-residually-finite host
   was built. Stopped under the stall rule.
