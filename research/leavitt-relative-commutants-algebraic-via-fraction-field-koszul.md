---
rg: 2
id: leavitt-relative-commutants-algebraic-via-fraction-field-koszul
kind: route
title: A transcendental element commuting with a copy of L makes L ⊗ k[t] a subalgebra of L; the fraction-field Koszul complex then forces weak dimension two on the hereditary algebra L_K(1,2)
target: leavitt-relative-commutants-are-algebraic-over-every-field
requires: []
---

All unmarked tensor products are over the field `k`. `L = L_k(1,2)`. For an extension field `K ⊇ k`,
`L ⊗ K ≅ L_K(1,2)`, since the defining presentation has coefficients in the prime field.

## 1. Koszul lower bound (field-independent)

**Lemma 1.** Let `A` be a unital `k`-algebra, and let `a_1, ..., a_n ∈ A` commute pairwise with
`P(a_1, ..., a_n) ≠ 0` for every nonzero `P ∈ k[x_1..x_n]`. Put `K = k(y_1..y_n)`. Then
`w.gl.dim(A ⊗ K) >= n`.

*Proof.* Put `C = k[a_1..a_n] ⊆ A`, which is a polynomial ring, `R = A ⊗ K` and `S = C ⊗ K = K[a_1..a_n] ⊆ R`. The
inclusion holds because tensoring over a field is exact.
1. Put `z_i = a_i ⊗ 1 - 1 ⊗ y_i ∈ S`. These form a regular sequence in the commutative polynomial ring `S`
   (a change of variables). Let `I = (z_1..z_n)`. The Koszul complex `K_•(z; S)` is a free `S`-resolution of
   `S/I` of length `n`. As a `C`-module, `S/I ≅ K`, with `a_i` acting as `y_i`. This is `Frac(C)`, with
   `C -> Frac(C)` the inclusion.
2. *Flat base change.* `R = A ⊗_C S`, and `S = C ⊗ K` is free over `C`. Take a projective resolution `P -> A`
   of right `C`-modules. Then `P ⊗_C S -> R` is a projective resolution over `S`, and
   `(P ⊗_C S) ⊗_S M = P ⊗_C M`. So `Tor^S_i(R, M) = Tor^C_i(A, M)` for every `S`-module `M`. For `M = S/I = Frac(C)`,
   which is flat over `C`, these vanish for `i > 0`.
3. So `F_• = R ⊗_S K_•(z; S)` is a free left `R`-resolution of `Q' = R ⊗_S S/I = R / R I`, of length `n`. Its
   differentials are right multiplications by the `z_i`, which are left `R`-linear.
4. Let `Q = S/I ⊗_S R = R / I R`, a right `R`-module. Then
   `Tor^R_n(Q, Q') = H_n(Q ⊗_R F_•) = H_n(K_•(z; Q)) = { q ∈ Q : q z_i = 0 for all i }`.
5. The class `q = 1 + IR` satisfies `q z_i = z_i + IR = 0`. It is nonzero: `Q ≅ Frac(C) ⊗_C A`, which contains
   `Frac(C) ⊗_C C = Frac(C)` because `Frac(C)` is flat over `C` and `C ⊆ A`. Under this identification `q` is `1 ⊗ 1`.
   So `Tor^R_n(Q, Q') ≠ 0`. ∎

## 2. Upper bound

**Lemma 2.** For every field `K`, `L_K(1,2)` is hereditary, so `w.gl.dim(L_K(1,2)) <= 1`.

This is Ara--Moreno--Pardo, *Nonstable K-theory for graph algebras*, Algebr. Represent. Theory 10 (2007): the
Leavitt path algebra of a row-finite graph over a field is hereditary. The theorem number was not re-checked
here. The same bound holds for every row-finite graph `E`, and `L_k(E) ⊗ K ≅ L_K(E)`.

## 3. Part 1: no polynomial ring in two variables

Suppose `a, b ∈ L` commute and are algebraically independent (constants evaluated at `1_L`). Lemma 1 with `A = L`
and `n = 2` gives `w.gl.dim(L_K(1,2)) >= 2` for `K = k(y_1, y_2)`, which contradicts Lemma 2.

*The non-unital form.* Let `f : k[x, y] -> L` be injective with `e = f(1) ≠ 1`. Then `e` is a nonzero idempotent,
and `eLe ≅ L`. This is the Ara--Cortiñas remark after Question 5.7 (arXiv:1108.0352v3, p. 8, quoted in
`no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2`). So `f` is a unital embedding into a copy of `L`,
which is excluded.

## 4. Part 2: relative commutants

Let `rho` be a unital endomorphism of `L`, and let `z ∈ C = C_L(rho(L))` be transcendental over `k`.
1. `rho` is injective, because `L` is simple (`leavitt-algebras-l-k-1-n-are-simple`) and `ker rho` is a proper
   ideal.
2. `mu : L ⊗ k[t] -> L`, given by `r ⊗ p -> rho(r) p(z)`, is a unital homomorphism, because `z` commutes with
   `rho(L)`.
3. `L` is central simple over `k`: its centre is `k`, as used in `tensor-square-nonembedding-from-algebraic-dependence`,
   step 1. So every ideal of `L ⊗ B` has the form `L ⊗ J` for an ideal `J` of `B`. This is the standard theorem on
   tensor products with a central simple algebra, which holds without finite dimension.
   - So `ker mu = L ⊗ J` with `J = { p : 1 ⊗ p ∈ ker mu } = { p : p(z) = 0 } = 0`, and `mu` is injective.
   - The same argument applied to `L ⊗ C -> L`, `r ⊗ c -> rho(r) c`, shows that it is injective. Its restriction
     to `1 ⊗ C` is the inclusion. This gives the second sentence of Part 2.
4. `s_0` is transcendental over `k`: its powers `s_0^m` are the distinct paths `0^m`, which are linearly independent
   in the path basis. So `k[s_0] ⊗ k[t]` is a polynomial ring in two variables inside `L ⊗ k[t]`.
5. Its image under `mu` is `k[rho(s_0), z]`, a polynomial ring in two commuting variables inside `L`. That
   contradicts Part 1.

So every element of `C` is algebraic over `k`.

## 5. Part 3: finite fields

If `k` is finite and `z ∈ C` is a unit, then `k[z]` is finite-dimensional by Part 2, hence a finite ring. The powers
of `z` lie in the finite group `k[z]^x`, so `z` has finite order. ∎

## Checks

- *Sanity against known embeddings.* `F_2(t) ⊆ L` (`rational-function-field-embeds-in-binary-leavitt-algebra`, if
  true) and `LC(∂F_d, k) ⋊ F_d ⊆ L` (`boundary-crossed-product-embeds-unitally-in-binary-leavitt`) have commutative
  subalgebras of transcendence degree at most one. `V × V ⊆ V ⊆ L^x` gives commuting units, not independent ones.
  For example, commuting disjointly supported permutation units satisfy `(1 - u)(1 - v) = 0`. None of these
  conflicts with Part 1.
- *The flip.* `rho_w = phi` for the flip `w`, and its commutant `M_2(F_2)` is algebraic, as Part 2 says.
- *Where Lemma 1 needs care.* It needs no flatness of `A` over `C`. Only `Frac(C)` has to be flat over `C`. This
  is why the earlier subfield and flatness-gated attempts stopped, and why this route does not.
