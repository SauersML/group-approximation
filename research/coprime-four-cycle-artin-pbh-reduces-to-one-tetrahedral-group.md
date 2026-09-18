---
rg: 2
id: coprime-four-cycle-artin-pbh-reduces-to-one-tetrahedral-group
kind: claim
title: The four-cycle Artin group with labels 3,3,3,2 lies in the permutational Boone--Higman class if the complete Artin group on four vertices with five labels 3 and one label 2 does
distinct_from:
  artin-hub-cones-reduce-pbh-to-coned-cliques: that needs one hub whose labels divide all incident labels, impossible here because two vertices meet the coprime labels 2 and 3; this uses two hubs with different labels, found by solving the folding constraints edge by edge.
  artin-pbh-reduces-to-free-of-infinity-artin-groups: that reduces every Artin group to six-vertex complete pieces for this graph (one clone per vertex); this reduces it with two hubs to four-vertex pieces, three of which are known and one of which is a single explicit hyperbolic-type group.
  triangle-free-all-3-artin-groups-satisfy-pbh: that settles the all-3 four-cycle; this is the four-cycle with one label changed to 2, the first coprime case.
---

**ESTABLISHED** (lane proof, in the body below; not independently reviewed). It inherits the status of `artin-pbh-reduces-along-folding-separators` (lane proof, not reviewed). No priority is claimed.

## Statement

Let `Θ` be the four-cycle `a -3- b -3- c -3- d -2- a` (so `ad = da`), with `a, c` and `b, d` not adjacent. Let `P` be the complete labelled graph on four vertices with one label 2 and five labels 3 (Coxeter diagram: `K_4` minus an edge). If `A_P ∈ B_A`, then `A_Θ ∈ B_A`, and so `A_Θ` embeds in a finitely presented simple group.

`A_Θ` is not reached by any earlier node here: `Θ` is 2-connected with a single odd component, has no foldable separator, and admits no hub labelling (`a` and `d` meet the coprime labels 2 and 3).

## Proof

Add hubs `e, f`. Labels, with `a–c` and `b–d` the only non-edges:

| | a | b | c | d | e | f |
|---|---|---|---|---|---|---|
| e | 3 | 2 | 3 | 3 | – | 3 |
| f | 2 | 3 | 3 | 2 | 3 | – |

Call the graph `Γ'`. `A_Θ` is its standard parabolic subgroup on `{a,b,c,d}` (van der Lek; Paris, arXiv:1211.7339, Theorem 5.4). Apply Part 1 of `artin-pbh-reduces-along-folding-separators` three times; each folding is checked edge by edge against cases (a)–(c) of `artin-ordinary-foldings-are-retractions`.

1. **Split `b | d`**, `Λ = {a, c, e, f}`.
   - `b ↦ e`: `ba → (e,a)`, `m_ea = 3 | 3`; `bc → (e,c)`, `3 | 3`; `bf → (e,f)`, `m_ef = 3 | m_bf = 3`; `be → (e,e)`.
   - `d ↦ f`: `da → (f,a)`, `2 | 2`; `dc → (f,c)`, `3 | 3`; `de → (f,e)`, `m_fe = 3 | m_de = 3`; `df → (f,f)`.
2. **Split `{a,b,c,e,f}` along `a | c`**, `Λ = {b, e, f}`.
   - `a ↦ f`: `ab → (f,b)`, `3 | 3`; `ae → (f,e)`, `3 | 3`; `af → (f,f)`.
   - `c ↦ f`: `cb → (f,b)`, `3 | 3`; `ce → (f,e)`, `3 | 3`; `cf → (f,f)`.
   - Pieces: `{a, b, e, f}`, whose Coxeter diagram is the four-cycle `a-b-f-e-a` with `af`, `be` commuting, type Ã_3; and `{b, c, e, f}`, of type `P` (the pair `b, e` commutes).
3. **Split `{a,c,d,e,f}` along `a | c`**, `Λ = {d, e, f}`.
   - `a ↦ f`: `ad → (f,d)`, `2 | 2`; `ae → (f,e)`, `3 | 3`; `af → (f,f)`.
   - `c ↦ e`: `cd → (e,d)`, `3 | 3`; `cf → (e,f)`, `3 | 3`; `ce → (e,e)`.
   - Pieces: `{a, d, e, f}`, whose Coxeter diagram is the star with centre `e` and leaves `a, d, f`, type D_4 (spherical); and `{c, d, e, f}`, of type `P` (the pair `d, f` commutes).

`A(Ã_3) ∈ B_A` (BFFHZ Corollary B, types Ã_n, in `aut-free-groups-satisfy-permutational-boone-higman`) and `A(D_4) ∈ B_A` (`spherical-artin-groups-satisfy-permutational-boone-higman`). So `A_(Γ') ∈ B_A` iff `A_P ∈ B_A`, and then `A_Θ ≤ A_(Γ')` lies in `B_A` (closure under subgroups, `boone-higman-type-a-class-closed-under-finite-extensions`). ∎

## Where the labels come from

Every label in the table is forced by the folding constraints once the first split is along `b | d` and `m_ef = 3`: the fold of `d` needs a vertex joined to `a` by 2 and to `c` by 3 (`f`); the fold of `b` needs one joined to `a` and `c` by 3 (`e`); `m_ef = 3` is the only choice making `Γ'[{a,c,e,f}]` split (as `A_3 *_(A_2) Ã_2`); and the second-level folds force `m_bf = m_de = 3`, `m_df = 2`, while `m_be = 2` makes `{a,b,e,f}` Euclidean. The piece `P` is the price: a complete group, so no folding separation can split it. Its Coxeter group is a non-compact hyperbolic tetrahedral group (two rank-3 subdiagrams of type Ã_2).
