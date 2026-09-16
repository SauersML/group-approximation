---
rg: 2
id: subcomplex-pi1-kernels-hyperlinear-quotients-proof
kind: route
title: Normalize the enlargement rel K, push the killing system along ρ, and apply Nitsche--Thom Theorem 1.2 over the hyperlinear target
target: subcomplex-pi1-kernels-vanish-in-hyperlinear-quotients
requires:
  - kervaire-laudenbach-holds-for-hyperlinear
artifacts:
  - research/artifacts/eilenberg-ganea-frontier-2026-09-16.md
---

Let `Y`, `K ⊆ Z ⊆ Y`, `N` and `ρ: π_1(K) → Q` be as in the target, with `Q` hyperlinear.

**Step 1: relative H_2 vanishes.**
- `C_2(Z) ⊆ C_2(Y)` with the same boundary map, and neither complex has 3-cells. So
  `H_2(Z) = Z_2(Z) ⊆ Z_2(Y) = H_2(Y) = 0`.
- The pair sequence `0 = H_2(Z) → H_2(Z, K) → H_1(K) → H_1(Z)` gives
  `H_2(Z, K) ≅ ker(H_1(K) → H_1(Z)) = 0`.

**Step 2: normal form.**
- Choose a forest `T` of edges of `Z` not in `K` that contains every vertex of `Z` outside `K`, each
  component meeting `K` in exactly one vertex. It exists because `Z` is connected: take a spanning
  tree of the graph `Z^1` with the vertex set of `K` identified to a point.
- Collapsing each component to its vertex in `K` is a homotopy equivalence rel `K`, as in Step 3 of
  `acyclic-subcomplex-pi1-nonhyperlinear-proof`. The result is
  `Z'' = K ∪ (a 1-cells) ∪ (b 2-cells)`, with the new 1-cells attached at vertices of `K`.
- So `H_2(Z'', K) = 0`, and `N = ker(i: π_1(K) → π_1(Z''))`.
- With a basepoint and paths in `K`, van Kampen gives
  `π_1(Z'') = (π_1(K) * F_a) / <<w_1, ..., w_b>>`, with `i` induced by the first factor.

**Step 3: the exponent-sum matrix is injective.**
- The relative cellular complex of `(Z'', K)` is `Z^b → Z^a → 0`. Its first map is the exponent-sum
  matrix `E` of `ε(w_1), ..., ε(w_b)`, where `ε: π_1(K) * F_a → F_a` kills `π_1(K)`.
- Hence `ker E = H_2(Z'', K) = 0`.
- The one-vertex presentation complex `P` of `<x_1, ..., x_a | ε(w_1), ..., ε(w_b)>` has cellular
  complex `Z^b → Z^a → Z` (maps `E` and `0`). So `H_2(P) = ker E = 0`.

**Step 4: push along ρ.**
- Put `w'_j = (ρ * id)(w_j) ∈ Q * F_a`. The augmentation killing `Q` sends `w'_j` to `ε(w_j)`, so
  the pushed system has the same presentation complex `P`.
- By `kervaire-laudenbach-holds-for-hyperlinear` (Nitsche--Thom, Theorem 1.2, applied with
  `G := Q`), the system `w'_1, ..., w'_b` is solvable in a group `H` containing `Q`: there is
  `h ∈ H^a` with `w'_j(h) = 1` for all `j`. Let `ι: Q → H` be the inclusion.
- Define `Φ: π_1(K) * F_a → H` by `ι ∘ ρ` on `π_1(K)` and `x_i ↦ h_i`. Then `Φ(w_j) = w'_j(h) = 1`,
  so `Φ` induces `Φ̄: π_1(Z'') → H` with `Φ̄ ∘ i = ι ∘ ρ`.
- For `n ∈ N`: `ι(ρ(n)) = Φ̄(i(n)) = 1`, and `ι` is injective. So `ρ(n) = 1`.
- *Degenerate cases.* If `b = 0`, then `i` is injective and `N = 1`. If `a = 0`, then `ker E = Z^b`,
  which forces `b = 0`. This proves (a).

**Step 5: the acyclic case (b).**
- `π_1(K)` is finitely generated. The null-homotopies in `Y` of finitely many generator loops are
  compact, meet `K`, and lie in a finite subcomplex. Their union with `K` gives a finite connected
  `Z ⊇ K` with `π_1(K) → π_1(Z)` trivial, as in Step 1 of `acyclic-subcomplex-pi1-nonhyperlinear-proof`.
- If `H_1(K) = 0`, the injectivity hypothesis holds, and `N = π_1(K)`. So `ρ = 1` by (a).
- Finite groups are hyperlinear. The left regular representation embeds a finite group in
  `U(|G|)`, as recorded in the cited proof. So `π_1(K)` has no nontrivial finite quotient.

**Trust surface.** The only import is Nitsche--Thom Theorem 1.2, as quoted in
`kervaire-laudenbach-holds-for-hyperlinear`. Steps 1--5 are elementary and complete here.
