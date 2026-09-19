---
rg: 2
id: positive-characteristic-steinberg-unitary-images-finite-proof
kind: route
title: Level-ideal cycle, exponent bound, congruence factorization, then central K_2 plus determinants on a perfect group
target: positive-characteristic-steinberg-unitary-images-are-finite
requires:
  - semilocal-steinberg-groups-have-central-k2
---

Notation: `A` unital with `m·1 = 0`, `n >= 3`, `rho : St_n(A) -> U(d)`, `[g,h] = g h g^(-1) h^(-1)`. The Steinberg
relations are

```text
(S1) x_ij(a) x_ij(b) = x_ij(a+b)
(S2) [x_ij(a), x_jk(b)] = x_ik(ab)           i, j, k distinct
(S3) [x_ij(a), x_kl(b)] = 1                  j != k, i != l
```

**Step 1 (one level ideal).** Put `K_ij = {a : rho(x_ij(a)) = 1}`. By (S1) it is an additive subgroup. For distinct
`i, j, k`, relation (S2) gives `x_ik(a) = [x_ij(a), x_jk(1)]` and `x_kj(a) = [x_ki(1), x_ij(a)]`. So
`K_ij ⊆ K_ik` and `K_ij ⊆ K_kj`. Since `n >= 3`, these two moves connect any ordered pair `(i,j)` to any other, so
all the `K_ij` are one subgroup `I`. (This is the cycle `K_12 ⊆ K_13 ⊆ K_23 ⊆ K_21 ⊆ K_31 ⊆ K_32 ⊆ K_12` of
`lef-elementary-groups-force-lef-rings-proof`, step 4.) For `a ∈ I` and `b ∈ A`,
`x_13(ab) = [x_12(a), x_23(b)]` and `x_13(ba) = [x_12(b), x_23(a)]` both map to `1`. So `ab, ba ∈ K_13 = I`, and `I`
is a two-sided ideal. This proves (1).

**Step 2 (exponent bound).** By (S1), `a -> rho(x_13(a))` is a homomorphism `(A, +) -> U(d)` with kernel `I`. Its image
`E ≅ A/I` is abelian, and `m·a = 0` gives `rho(x_13(a))^m = 1`. Commuting unitaries are simultaneously
diagonalizable, so `E` embeds in the diagonal group `μ_m^d`. Hence `|A/I| <= m^d`. This proves (2). Put `B = A/I`, a
finite ring.

**Step 3 (congruence factorization).** Define `rho_bar(x_ij(a + I)) = rho(x_ij(a))`. This is well defined: by (S1),
`rho(x_ij(a + c)) = rho(x_ij(a))` for `c ∈ I`. Each relation (S1)–(S3) of `St_n(B)` is the image of the same relation
in `St_n(A)` for any lifts, so it holds among the `rho(x_ij(a))`. By von Dyck's theorem `rho_bar` is a homomorphism
`St_n(B) -> U(d)`, and `rho = rho_bar ∘ (St_n(A) -> St_n(B))`. This proves (3).

**Step 4 (finiteness).** Let `H = rho_bar(St_n(B)) = rho(St_n(A))`.
- `St_n(B)` is perfect, since `x_ij(b) = [x_ik(b), x_kj(1)]` for any `k ∉ {i,j}`. So `H` is perfect.
- `B` is finite, hence semilocal. By `semilocal-steinberg-groups-have-central-k2`, the kernel `K_2(n,B)` of
  `St_n(B) -> GL_n(B)` is central. The image of this map is `E_n(B)`, a finite group. So `N := rho_bar(K_2(n,B))` is
  central in `H`, and `[H : N] <= |E_n(B)|`.
- `U(d)` is completely reducible: `C^d = V_1 ⊕ ... ⊕ V_s`, with each `V_j` an irreducible `H`-module of dimension
  `d_j`. An element `y ∈ N` lies in `H`, so it preserves each `V_j`. It commutes with `H`, so by Schur's lemma it
  acts on `V_j` as a scalar `λ_j(y)`.
- `h -> det(h|V_j)` is a homomorphism from the perfect group `H` to the abelian group `U(1)`, so it is trivial. Hence
  `λ_j(y)^(d_j) = det(y|V_j) = 1`.
- So `y -> (λ_j(y))_j` embeds `N` in `μ_(d_1) × ... × μ_(d_s)`. This gives `|N| <= d_1 ⋯ d_s <= d^d`.

Therefore `|H| <= |E_n(B)| · d^d`. This proves (4).

**Remarks.**
- Step 4 does not use Schur's 1911 theorem on periodic linear groups. The determinant trick on the perfect group
  replaces it.
- The only imported result is centrality of `K_2` for finite rings (`semilocal-steinberg-groups-have-central-k2`:
  Voronetsky, arXiv:2004.08551, l.401–402 and l.113, quoted verbatim in
  `semilocal-steinberg-groups-have-central-k2-citation`).
- For `EL_n(A)`, and for any root-generated quotient of `St_n(A)`, precompose with the surjection from `St_n(A)`.
