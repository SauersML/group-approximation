---
rg: 2
id: raags-are-undistorted-in-brin-thompson-group-2v
kind: claim
title: Every finitely generated right-angled Artin group is undistorted in the Brin-Thompson group 2V (Salo's conveyor-belt embedding is a quasi-isometric embedding)
distinct_from:
  every-raag-embeds-in-brin-thompson-group-2v: that is Salo's embedding A_Γ -> [[{0,1}^Z]] -> 2V as an abstract embedding; this proves that the same embedding is a quasi-isometric embedding of word metrics, with the explicit bound |g| <= (ω/2)(M(g)+1).
  brin-thompson-mv-contains-a-distortion-element: that shows 2V has distorted cyclic subgroups, so undistortion in 2V is not automatic; this shows the right-angled Artin subgroups of Salo's embedding are not distorted.
  hyperbolic-groups-undistortedly-embed-in-fp-simple-groups: that uses the BBMZ host SV_Γ, which is finitely presented but not known to be F_infinity; this puts right-angled Artin groups undistortedly in 2V, which is F_infinity.
---

**ESTABLISHED** by `raag-undistortion-in-2v-via-heaviest-belt-chain-proof` (lane proof, elementary, not
independently reviewed; no priority claimed, bounded search: arXiv and web search on 09-18 found no
statement that right-angled Artin groups are undistorted in some `nV`).

## Statement

Let `Γ` be a finite simple graph with clique number `ω = ω(Γ)`, and `A_Γ` its right-angled Artin group
with word length `|·|` in the standard generators `t_u`. Let `Ψ : A_Γ -> [[Σ^Z]]` be Salo's conveyor-belt
embedding (`every-raag-embeds-in-full-shift-topological-full-group`; artifact
`raags-in-2v-via-full-shift-full-group-2026-09-16`, Part B), and `Ψ̂ : A_Γ -> 2V` its composite with the
binary recoding (Part B.5) and the baker's-map conjugation (Part A,
`full-shift-topological-full-group-embeds-in-2v`). For `f ∈ [[Σ^Z]]` put `M(f) = max_x |c_f(x)|`, the
largest head move of `f`.

1. For every `g ∈ A_Γ`: `|g| <= (ω/2) (M(Ψ(g)) + 1)`.
2. `A_Γ` is undistorted in every finitely generated group `K` with `Ψ(A_Γ) <= K <= [[Σ^Z]]`, or with
   `Ψ̂(A_Γ) <= K <= 2V`. In particular `Ψ̂ : A_Γ -> 2V` is a quasi-isometric embedding.

`2V` is a simple group of type F_∞: Brin proved it is simple, and Kochloukova, Martínez-Pérez and Nucinkis
proved it is of type F_∞. Both are recalled in Belk–Zaremsky, arXiv:2001.04579, TeX l.151 and l.185. So
every finitely generated right-angled Artin group quasi-isometrically embeds in one simple group of type
F_∞.

## Why it is not automatic

`2V` contains distorted cyclic subgroups (`brin-thompson-mv-contains-a-distortion-element`,
Callard–Salo). So undistortion depends on the embedding. The proof uses two facts.
- **A subadditive length on 2V.** Take the ℓ¹ norm of the local scaling exponents.
- **A lower bound from the belts.** A reduced word is covered by at most `ω` chains of pairwise
  non-commuting syllables. After reordering the word, Salo's faithfulness configuration follows the
  heaviest chain, so the head moves by about twice that chain's exponent sum.
