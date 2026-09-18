---
rg: 2
id: houghton-six-rays-polynomial-dehn-via-path-words
kind: route
title: Sort, write every transposition as a path word of routed edge transpositions, and eliminate points with edge relations of area R^2 log R
target: houghton-groups-with-six-or-more-rays-have-polynomial-dehn
requires:
  - houghton-dehn-polynomially-equivalent-to-commutation-area
  - houghton-far-commutation-has-quadratic-log-area-for-six-rays
artifacts:
  - research/artifacts/zp-houghton-pours-2026-09-17.md
---

Complete proof in `research/artifacts/zp-houghton-pours-2026-09-17.md`, §§4–6.
It uses Lemma 1 (depth), Lemma 3 (sorting) and Step 2 (carry-and-merge elimination)
of `research/artifacts/zp-houghton-dehn-2026-09-13-part1.md`, from
`houghton-dehn-polynomially-equivalent-to-commutation-area`. It also uses the pour,
reroute and far-commutation bounds `W, R, F ≼ k^2 log k` of
`houghton-far-commutation-has-quadratic-log-area-for-six-rays`.

1. *Edge words.* Let `Γ` be `K_n` on the top points `(x,1)`, with the rays as
   pendant paths. Each edge is a transposition, written as a routed word:
   - `D^(c(x))_x(j-1)` for the ray edge `t_x(j)`;
   - `λ_yx τ_x λ_xy` for the top edge `σ_{x,y}`.

   Every edge relation at depth `<= R` has area `≼ R^2 log R`: squares, commutation
   of disjoint edges, braids, and star or triangle relations at a top vertex.
   Commuting two edges on one ray is a far commutation. Commuting edges on
   different rays is two reroutes and a letterwise commutation.
2. *Letters on edges.* Conjugating an edge word by `λ_zw` gives an edge word at
   cost `≼ R^2 log R`. The one exception is `σ_{w,y}` with `y != z`, which gives
   `t_w(1) σ_{w,y} t_w(1)`.
3. *Path words.* Let `Can((p q))` be `e_1 ⋯ e_r ⋯ e_1` along the geodesic of `Γ`.
   Reversal, shortcut of a top detour, and refinement cost `O(R^2)` edge
   relations. Hence:
   - `e Can(ρ) e -> Can(ρ^e)` costs `≼ R^4 log R`, by cases on how `e` meets the
     geodesic;
   - `s^(-1) Can(ρ) s -> Can(ρ^s)` costs `≼ R^4 log R` for each letter `s`.
4. *Reduction.*
   - Sort, at cost `O(L^2)`, into `M = O(L^2)` conjugates of `α` by words of length
     `O(L)`.
   - Normalize each to a path word, letter by letter, at cost `O(L^7 log L)` in
     total.
   - Eliminate the `O(L)` points by carry-and-merge. Each `(ρσρ)` move is `2r-1`
     edge conjugations along the palindrome `Can(ρ)`, at cost `≼ R^5 log R`.

   The total is `δ(L) ≼ L^8 log L`.
