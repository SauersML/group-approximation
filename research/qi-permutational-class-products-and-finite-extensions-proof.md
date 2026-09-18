---
rg: 2
id: qi-permutational-class-products-and-finite-extensions-proof
kind: route
title: Undistortion survives products of actors on disjoint unions and finite wreaths on imprimitive sets, and the acting group is undistorted in its twisted Brin-Thompson group
target: products-of-hyperbolic-groups-qi-embed-in-fp-simple-groups
requires:
  - type-a-actions-closed-under-products-and-finite-wreaths
  - type-a-action-gives-boone-higman-for-subgroups
  - twisted-brin-thompson-groups-quasi-retract-onto-acting-group
  - hyperbolic-groups-undistortedly-embed-in-fp-simple-groups
  - hyperbolic-groups-lie-in-the-permutational-class
  - aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups
---

Lane proof, not independently reviewed. Word lengths in products use the union of the factors'
generating sets, so `|(g_1, …, g_k)| = Σ |g_i|`.

**Item 1.** Let `G <= Δ` be undistorted, with `Δ` acting on `S` of type (A).
- **Finiteness.** `SV_Δ` is finitely presented and simple (`type-a-action-gives-boone-higman-for-subgroups`,
  Zaremsky arXiv:2405.18354; simplicity is Belk–Zaremsky `thrm:simple`). It is finitely generated, since
  `Δ` is and type (A) gives finitely many orbits.
- **Undistortion.** By `twisted-brin-thompson-groups-quasi-retract-onto-acting-group`, `Δ` is undistorted
  in `SV_Δ`. Composing, `G` is undistorted in `SV_Δ`.

**Item 2.**
- **Subgroups.** A composite of undistorted inclusions is undistorted.
- **Products.** If `G_i <= Δ_i` are undistorted, then `G_1 × G_2 <= Δ_1 × Δ_2` is undistorted, since
  lengths add coordinatewise. `Δ_1 × Δ_2` acting on `S_1 ⊔ S_2` is of type (A)
  (`type-a-actions-closed-under-products-and-finite-wreaths` (a)).
- **Finite-index overgroups.** Let `H <= G` have finite index, with `H <= Δ` undistorted.
  - **Setup.** Let `N` be the normal core of `H`, of index `k` in `G`. `N` has finite index in `H`, so it
    is undistorted in `Δ`. Choose coset representatives `t_1 = 1, t_2, …, t_k` of `N`.
  - **Wreath embedding.** The Kaloujnine–Krasner embedding `G -> N ≀ S_k` sends `n ∈ N` to
    `(t_1^{-1} n t_1, …, t_k^{-1} n t_k; id)`. Its first coordinate is `n`, so
    `|n|_N <= |ι(n)|_{N^k} <= C |ι(n)|_{N ≀ S_k} + D`, since `N^k` has finite index.
  - **Back to `G`.** `N` has finite index in `G`, so `G` is undistorted in `N ≀ S_k`. Write `g = n r` with
    `r` in a finite set of coset representatives. Then `|g|_G <= c|n|_N + c'` and
    `|ι(n)| <= |ι(g)| + c''`.
  - **Into the actor.** `N^k <= Δ^k` is undistorted coordinatewise, and both are of finite index. So
    `N ≀ S_k <= Δ ≀ S_k` is undistorted, and `Δ ≀ S_k` is of type (A) (same node, part (b)).

**Item 3.**
- **Hyperbolic groups.**
  - Undistortion: steps 1–2 of `hyperbolic-undistorted-fp-simple-embedding-proof` give `G <= Γ`
    undistorted for `Γ = [[G*Z | ∂_h(G*Z)]]`.
  - Type (A): `Γ` is a full contracting RSG, so its action on a rational orbit is of type (A)
    (`hyperbolic-groups-lie-in-the-permutational-class`, item 1).
- **`Aut(F_n)`.** It is a retract of `Γ = Aut_V(V * F_n)` (`aut-free-groups-quasi-isometrically-embed-in-fp-simple-groups`,
  part 2), and a retract is undistorted. The BFFHZ twisted Brin–Thompson group `SV_Γ` is finitely presented.
  By BFFHZ's l.185, quoting Zaremsky's criterion, that means the action of `Γ` on `S` is of type (A).

**Item 4.** This follows from items 1–3. ∎
