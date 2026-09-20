---
rg: 2
id: sl4z-involution-centralizers-rational-h2-proof
kind: route
title: Proof that the block-swap involution centralizer of SL_4(Z) has H^2 = Q with a detecting torus
target: sl4z-involution-centralizers-have-rational-h2
requires: []
---

Lane proof, elementary. Standard inputs, used without citation:
- (S1) if `N ⊴ Δ` has finite index, then restriction gives `H^*(Δ; Q) ≅ H^*(N; Q)^{Δ/N}`
  (transfer), and inner automorphisms act trivially on cohomology;
- (S2) the Künneth formula over `Q`;
- (S3) `H^k(Γ; Q) = 0` for `k ≥ 2` when `Γ` is virtually free.

**Step 1 (centralizer).**
- In 2x2 blocks, `M = [[P, Q], [R, S]]` commutes with `g = [[0, I], [I, 0]]` iff
  `[[Q, P], [S, R]] = [[R, S], [P, Q]]`, i.e. `R = Q` and `S = P`. So `M = [[A, B], [B, A]]`.
- Put `f_i = e_i + e_{i+2}` and `f'_i = e_i − e_{i+2}` for `i = 1, 2`. Then `M f = (A+B) f`
  on `L_+ = span_Z(f_1, f_2)` and `M f' = (A−B) f'` on `L_− = span_Z(f'_1, f'_2)`, in these
  bases. So `M` is conjugate over `Q` to `diag(X, Y)` with `X = A+B`, `Y = A−B`, and
  `det M = det X · det Y`.
- `M ∈ GL_4(Z)` commuting with `g` preserves `L_± = Z^4 ∩ ker(g ∓ 1)`, and so does
  `M^{-1}`. So `X, Y ∈ GL_2(Z)`.
- Conversely, `(X, Y) ∈ GL_2(Z)^2` gives an integral `M` iff `A = (X+Y)/2` and `B = (X−Y)/2`
  are integral, i.e. `X ≡ Y mod 2`. Then `M^{-1}` comes from `(X^{-1}, Y^{-1})` and is
  integral too.
- `det M = 1` iff `det X · det Y = 1` iff `det X = det Y`. So `Z_{SL_4(Z)}(g) ≅ Δ`, and the
  map `M ↦ (X, Y)` is multiplicative, because `M` acts on `L_+ ⊕ L_−` by `X ⊕ Y`.
- `g`: `A = 0`, `B = I`, so `g = (I, −I)`. `c = −I_4` gives `(−I, −I)`. Both are scalar in
  each coordinate, hence central in `Δ`.

**Step 2 (a finite-index normal subgroup).**
- Let `Γ(2) = ker(SL_2(Z) → SL_2(Z/2))`. It contains `−I`, and `Γ(2)/{±I}` is free on
  `a = [[1,2],[0,1]]` and `b = [[1,0],[2,1]]` (Sanov; standard). So `Γ(2)` is virtually free
  and `H_1(Γ(2); Q) = Q[a] ⊕ Q[b]`.
- Let `N = Γ(2) × Γ(2) ⊂ Δ`. Define `Δ → GL_2(Z/2) × {±1}`, `(X, Y) ↦ (X mod 2, det X)`.
  This is a homomorphism, because `X ≡ Y mod 2` and `det X = det Y` on `Δ`. Its kernel is
  `{X ≡ Y ≡ I mod 2, det X = det Y = 1} = N`. It is onto: `(X, X)` for `X ∈ SL_2(Z)`
  reaches every element of `GL_2(Z/2) = SL_2(Z/2)`, and `(d, d)` with `d = diag(1, −1)`
  reaches `(I, −1)`. So `N ⊴ Δ` and `Δ/N ≅ S_3 × Z/2`.

**Step 3 (the action on `H_1(Γ(2); Q)`).**
- Conjugation gives `ρ : GL_2(Z) → GL(H_1(Γ(2); Q))`. By (S1) `ρ` is trivial on `Γ(2)`, so
  its image is a quotient of `GL_2(Z)/Γ(2)`, which has order 12. In particular the image is finite.
- For `(X, Y) ∈ Δ`, `X^{-1}Y ≡ I mod 2` and `det(X^{-1}Y) = 1`, so `X^{-1}Y ∈ Γ(2)`. Hence
  `ρ(Y) = ρ(X)`. Conjugation by `(X, Y)` acts on `N` coordinatewise, so it acts on
  `H_1(Γ(2); Q) ⊗ H_1(Γ(2); Q) ⊂ H_2(N; Q)` by `ρ(X) ⊗ ρ(X)`.
- With `U = [[1,1],[0,1]]` and `S = [[0,−1],[1,0]]`:
  - `U a U^{-1} = a`;
  - `U b U^{-1} = [[3,−2],[2,−1]] = −a b^{-1}`;
  - `S a S^{-1} = [[1,0],[−2,1]] = b^{-1}`;
  - `S b S^{-1} = [[1,−2],[0,1]] = a^{-1}`.

  So in the basis `([a], [b])`, `ρ(U)(p, q) = (p + q, −q)` and `ρ(S)(p, q) = (−q, −p)`.
- The eigenlines of `ρ(S)` are spanned by `(1, −1)` and `(1, 1)`. `ρ(U)` sends them to
  `(0, 1)` and `(2, −1)`, which are not on the same lines. So `ρ(SL_2(Z))` has no invariant
  line over `C`. So `H_1(Γ(2); C)` is irreducible, and by Schur its commutant is `C`.

**Step 4 (`H^1` and `H^2` of `Δ`).**
- By (S2) and (S3), `H^1(N; Q) = H^1 ⊕ H^1` and `H^2(N; Q) = H^1 ⊗ H^1`, where
  `H^1 := H^1(Γ(2); Q)`. The second group is the space of bilinear forms on `H_1(Γ(2); Q)`,
  via cross products.
- By (S1) and Step 3, `H^1(Δ; Q)` is the `ρ(GL_2(Z))`-invariants in `H^1 ⊕ H^1`, which are
  `0` because the representation is irreducible and nontrivial.
- Likewise `H^2(Δ; Q)` is the space of bilinear forms `B` with `B(ρ(X)u, ρ(X)v) = B(u, v)`
  for all `X ∈ GL_2(Z)`. Every `X` occurs, as the first coordinate of `(X, X) ∈ Δ`.
  - Averaging an inner product over the finite group `ρ(GL_2(Z))` gives a positive
    definite invariant form `B_0`.
  - For any invariant `B`, `B_0^{-1}B` commutes with `ρ(GL_2(Z))`. By Step 3 it is a scalar.
  - So `H^2(Δ; Q) = Q·B_0`, and `B_0` is symmetric.

**Step 5 (detecting torus).**
- `x = a ∈ Γ(2)`. So `M_1 = (x, 1)` and `M_2 = (1, x)` lie in `N`, commute, and have infinite
  order.
- Their block forms follow from `A = (X+Y)/2` and `B = (X−Y)/2`:
  - `M_1`: `A = [[1,1],[0,1]]`, `B = [[0,1],[0,0]]`;
  - `M_2`: the same `A`, and `−B`.
- Let `ι : Z^2 → N`, `(m, n) ↦ (x^m, x^n)`. Then `ι_*[T^2] = [a] × [a]`. Pairing it with the
  class `B_0` gives `±B_0([a], [a]) ≠ 0`, because `[a] ≠ 0` and `B_0` is positive definite.
- So the restriction `H^2(Δ; Q) → H^2(Z^2; Q)` is nonzero. Both groups are `Q`, so it is an
  isomorphism.

**Step 6 (Weyl swap; the class is odd).**
- With `h = diag(I, −I)`, `h [[P, Q], [R, S]] h^{-1} = [[P, −Q], [−R, S]]`. So `h g h^{-1} = −g`
  and `h [[A, B], [B, A]] h^{-1} = [[A, −B], [−B, A]]`. In coordinates this is
  `(X, Y) ↦ (Y, X)`. In particular `h M_1 h^{-1} = M_2`, `h M_2 h^{-1} = M_1`, and `det h = 1`.
- `h` normalizes `Δ` and `N` and acts on `N = Γ(2) × Γ(2)` by the factor swap `τ`. On cross
  products of degree-one classes, `τ^*(α × β) = −β × α`. So on bilinear forms `τ^*B = −B^T`, and
  `τ^*B_0 = −B_0`. Hence `h` acts on `H^2(Δ; Q)` by `−1`.
- **PSL.** `{M ∈ SL_4(Z) : MgM^{-1} = ±g} = Δ ⊔ hΔ`. If `MgM^{-1} = −g`, then `h^{-1}M` centralizes
  `g`. So `C_{PSL_4(Z)}(ḡ) = (Δ ⊔ hΔ)/{±I}`.
  - `Δ → Δ/{±I}` has finite central kernel, so it induces an isomorphism on rational
    cohomology. This is (S1) applied to the Lyndon–Hochschild–Serre spectral sequence with
    finite kernel.
  - By (S1) again, `H^2(C_{PSL_4(Z)}(ḡ); Q) = H^2(Δ; Q)^{h} = 0`.

**Step 7 (second involution `g_1`).** One extra standard input:
- (S5) `Γ_0(2)/{±I}` is a free product `Z * Z/2`, with the `Z` generated by `T = [[1,1],[0,1]]`.
  It has index 3 in `PSL_2(Z)`, genus 0, two cusps and one elliptic point of order 2.
  This is recalled, not re-derived.

The argument:
- Put `f = e_3 + e_4` and `f' = e_3 − e_4`. The eigenlattices of `g_1` are
  `L_+ = span(e_1, f)` and `L_− = span(e_2, f')`. As in Step 1, a centralizing `M` is `X ⊕ Y`
  with `X, Y ∈ GL_2(Z)` in these bases.
- `Z^4 = L_+ ⊕ L_− + Z e_3` with `e_3 = (f + f')/2`, and `X ⊕ Y` preserves `Z^4` iff
  `(Xf + Yf')/2 ∈ Z^4`.
  - Write `Xf = β e_1 + δ f` and `Yf' = β' e_2 + δ' f'`. The condition is that `β` and `β'` are
    even and `δ ≡ δ' mod 2`.
  - When `β` is even and `det X = ±1`, `δ` is odd. So the condition is `β, β' ∈ 2Z`.
- So `Z(g_1) ≅ C_1 = {(X, Y) ∈ Γ^0_±(2)^2 : det X · det Y = 1}`, where
  `Γ^0_±(2) = {X ∈ GL_2(Z) : X_{12} ∈ 2Z}`.
- `N_1 = Γ^0(2) × Γ^0(2)` (determinant one) has index 2, with the other coset `(d, d)N_1`.
- `S T S^{-1} = T'^{-1}` with `T' = [[1,0],[1,1]]`. So by (S5), `Γ^0(2) = S Γ_0(2) S^{-1}` is
  virtually free with `H_1(Γ^0(2); Q) = Q[T']`.
- `d T' d^{-1} = T'^{-1}`, so `d` acts by `−1` on `H^1`, and `(d, d)` acts by `+1` on
  `H^1 ⊗ H^1 = Q`. So `H^2(C_1; Q) = Q`. The torus `(T', 1), (1, T')` pairs to `±1`.
- `k` sends `(e_1, f) ↦ (e_2, f')` and `(e_2, f') ↦ (e_1, f)`, so `k(X ⊕ Y)k^{-1} = Y ⊕ X` in
  these bases. `k g_1 k^{-1} = −g_1` by direct evaluation on `e_1, …, e_4`, and `det k = (−1)(−1) = 1`.
