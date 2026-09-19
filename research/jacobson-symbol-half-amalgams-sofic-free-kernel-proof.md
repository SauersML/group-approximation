---
rg: 2
id: jacobson-symbol-half-amalgams-sofic-free-kernel-proof
kind: route
title: Check the fibre-split hypotheses for the two Jacobson decompositions, compute the head relators, and apply the lemma
target: jacobson-symbol-half-amalgams-are-sofic-with-free-kernel
requires:
  - fibre-split-amalgam-kernels-are-free-and-centralize-the-fibre
  - jacobson-polynomial-symbol-preimages-are-lef-in-every-rank
  - laurent-finitary-el-is-kazhdan-lef-inside-doubled-jacobson
  - elek-szabo-amalgams-over-amenable-subgroups-are-sofic
---

Notation as in the target. "The lemma" is `fibre-split-amalgam-kernels-are-free-and-centralize-the-fibre`, "LEF-m" is
`jacobson-polynomial-symbol-preimages-are-lef-in-every-rank`, and "(BCk)" refers to
`laurent-finitary-el-is-kazhdan-lef-inside-doubled-jacobson`. Commutators are `[g, h] = g h g^(-1) h^(-1)`.

## Step 0. Two elementary facts

- **(F1) Commutator of transvection sums.** Let `X, Y` be matrices over `J` with `X^2 = Y^2 = YX = 0`. Then
  `(1+X)^(-1) = 1 - X`, `(1+Y)^(-1) = 1 - Y`, and expanding `(1 + X + Y + XY)(1 - X - Y + XY)` gives
  `[1 + X, 1 + Y] = 1 + XY`, because every other term contains `X^2`, `Y^2` or `YX`.
- **(F2) `L_m` is simple.** By LEF-m, `L_m = GL_fin(V)` for `F = F_2`. Every element fixes all but finitely many basis
  vectors and preserves the span of the rest, so `L_m` is the directed union of the groups `GL_N(F_2) = SL_N(F_2)`,
  `N >= 3`. These are simple (Jordan--Dickson), and a directed union of simple groups is simple.
- **(F3) Symbol surjectivity.** `F[z]`, `F[z^(-1)]` and `A` are Euclidean (for `A`, use the span of exponents), so
  `SL_k = EL_k` over each of them.

## Step 1. The hypotheses for (R3)

- `A_0 ∩ L = 1`, and `π` maps `A_0` isomorphically onto `SL_3(F[z])` (LEF-m, point 1). Applying the twist of LEF-m,
  point 4, `B_0 ∩ L = 1`, and `π(B_0) = SL_3(F[z^(-1)])`. So `L A_0 = H_+` and `L B_0 = H_-`.
- `SL_3(F[z]) ∩ SL_3(F[z^(-1)]) = SL_3(F[z] ∩ F[z^(-1)]) = SL_3(F)`. The constants `SL_3(F) = EL_3(F)` lie in `A_0`
  and in `B_0`. If `x in A_0 ∩ B_0`, then `π(x) = π(g)` for some `g in SL_3(F)`, and `x = g` because `π` is injective
  on `A_0`. So `C_0 = SL_3(F)` and (H) holds.
- **Generation.** `<A_0, B_0>` contains `x_ij(S)`, `x_ij(T)` and `x_ij(1)` for all `i != j`. With a third index `k`,
  `[x_ik(a), x_kj(b)] = x_ij(ab)`. So it contains `x_ij(w)` for every monomial `w` in `S, T`, hence `x_ij(r)` for every
  `r in J`, hence `E_3`.

## Step 2. The hypotheses for (R2n)

- **`A_0`.** As in Step 1, `A_0 ∩ L = 1` and `L A_0 = H_+` (LEF-m, point 1, with `m = 2n`).
- **`B_0 ⊆ E`.** `rho(x_ij(a))` has the `2 x 2` block `rho(a)` at `(i, j)`, so it is a product of four commuting
  elementary matrices `x_(i±, j±)(·)`. So `B_0 = rho(EL_n(A)) ⊆ E_(2n)`.
- **`B_0 ∩ L = 1`.** `π rho(a) = diag(a(z), a(z^(-1)))` blockwise (BC3), which is injective on `M_n(A)`. So `π` is
  injective on `B_0`.
- **`L B_0 = rho(H_bi(n))`.** By (F3), `π(B_0) = π rho(SL_n(A)) = Gamma^tw`, and `π^(-1)(Gamma^tw) = rho(H_bi(n))`
  (BC3).
- **(H).** An element of `Gamma^tw` has blocks `diag(a_ij(z), a_ij(z^(-1)))`. It lies in `SL_(2n)(F[z])` exactly when
  every `a_ij` is in `F[z] ∩ F[z^(-1)] = F`. So `π(A_0) ∩ π(B_0) = π rho(SL_n(F))`.
- **`C_0`.** `rho(g) = g ⊗ I_2` for `g in SL_n(F)`. It lies in `B_0`, and in `EL_(2n)(F) ⊆ A_0`. As in Step 1,
  injectivity of `π` on `B_0` gives `A_0 ∩ B_0 = rho(SL_n(F))`. This matches the intersection in (BC4).

## Step 3. The head relators (point 4)

- **(R3).** `X = S e_12` and `Y = T e_23` satisfy (F1), so `[x_12(S), x_23(T)] = x_13(ST)`. In characteristic two,
  `ST + 1 = 1 - ST = Q`, so `Φ(ρ_+) = x_13(Q)`.
- **(R2n).** The block of `rho(x_23(z^(-1)))` at `(2, 3)` is `[[T, 0], [Q, S]]`, with rows `2+, 2-` and columns
  `3+, 3-`. So `rho(x_23(z^(-1))) = 1 + Y` with `Y = T e_(2+,3+) + Q e_(2-,3+) + S e_(2-,3-)`. The three terms have
  pairwise zero products, which gives the factorization into commuting elementary matrices. Put `X = S e_(1+,2+)`.
  - `X^2 = 0`, and `Y^2 = 0` because the columns of `Y` are `3±` and its rows are `2±`.
  - `YX = 0`, because the columns of `Y` are `3±` and the only row of `X` is `1+`.
  - `XY = S T e_(1+,3+)`.

  By (F1), `[x_(1+,2+)(S), rho(x_23(z^(-1)))] = x_(1+,3+)(ST)`, so `Φ(k_Q) = x_(1+,3+)(ST + 1) = x_(1+,3+)(Q)`.
- In both cases the word has letters in `A_0 ∪ B_0`, so it lies in `U`. Its image under `Φ` is in `L`, so
  `λ(h) = 1`, `h in K`, and `ℓ(h)` is the head, which is `!= 1`.

## Step 4. Generation for (R2n) (point 1)

Let `E' = <A_0, B_0> <= E_(2n)`.
- **All `x_pq(Q)`.** `E'` contains `x_(1+,3+)(Q) = Φ(k_Q)` by Step 3. The permutation matrices lie in
  `SL_(2n)(F_2) ⊆ A_0` (determinant `±1 = 1`), and they conjugate `x_pq(r)` to `x_(σp, σq)(r)`. As `Sym(2n)` is
  2-transitive, `E'` contains `x_pq(Q)` for all `p != q`.
- **All `x_pq(T)`.** For `i != j` in `{1..n}`, the factorization of Step 3 gives
  `x_(i+, j+)(T) = rho(x_ij(z^(-1))) · x_(i-, j-)(S)^(-1) · x_(i-, j+)(Q)^(-1)`, with every factor in `E'`. Permutation
  conjugation then gives `x_pq(T)` for all `p != q`.
- **Everything.** `E'` contains `x_pq(S)` and `x_pq(1)` from `A_0`. Since `2n >= 6`, commutators with a third index
  give `x_pq(w)` for every monomial `w`, and additivity gives `x_pq(r)` for every `r in J`. So `E' = E_(2n)`.

## Step 5. Soficity of the amalgam (point 2)

- **`L A_0 = H_+` is sofic** by LEF-m, point 3. For (R3), `L B_0 = H_-` is sofic by LEF-m, point 4.
- **`rho(H_bi(n))` is sofic.** It is LEF by (BC2) and (BC3). LEF passes to subgroups. Let `Y` be a finitely generated
  subgroup, `D ⊂ Y` finite, and `φ : D -> G` an injective partial homomorphism into a finite group. Let `D` act on
  `G` by `σ_d(g) = φ(d) g`. Then `σ_d σ_(d') = σ_(dd')` whenever `d, d', dd' in D`, and `σ_d` has no fixed point
  for `d != 1`. This is an exact sofic approximation on `D`, so `Y` is sofic. By the convention quoted in
  `elek-szabo-amalgams-over-amenable-subgroups-are-sofic`, `rho(H_bi(n))` is sofic.
- **`C = L C_0` is locally finite.** Each element of `L` preserves the span of finitely many basis vectors and fixes
  the others, so every finitely generated subgroup of `L` is finite. `C_0` is finite. If `Y <= C` is finitely
  generated, `Y ∩ L` has finite index in `Y`, so it is finitely generated, hence finite, and `Y` is finite. (This is
  also stated in (BC4).)
- **`C` is amenable.** For a finite `D ⊂ C`, the finite group `Y = <D>` satisfies `d Y = Y` for `d in D`, so it is an
  exact Følner set.
- By Theorem 1 of `elek-szabo-amalgams-over-amenable-subgroups-are-sofic`, `P` is sofic.

## Step 6. Applying the lemma (points 3, 5 and 6)

Steps 1 and 2 are the hypotheses of the lemma, and Steps 1 and 4 give `<A_0, B_0> = E`.
- **Point 3** is the lemma's points 2 and 3.
- **Point 5.** `L` is simple by (F2). The element `r = ℓ(h)^(-1) h` is in `N` by the lemma's point 2, and
  `ℓ(p(r)) = ℓ(h) != 1` by Step 3. The lemma's point 4 gives `N = ker ℓ · <<r>>_P`, `E ≅ U / ker ℓ` and
  `P / ker ℓ ≅ E ×_Λ E`. Here `Λ = E / L = π(E)`, which is `SL_m(A)` by (F3).
- **Point 6** is the lemma's Consequence. `A_0` and `B_0` are isomorphic through `π` to `SL_m(F[z])`,
  `SL_m(F[z^(-1)])` or `SL_n(A)`, which are linear over `F(z)`, and `C_0` is finite.

**The remark on `u ⊕ 1`.** `u ⊕ 1 = diag(u, 1, ..., 1)` has symbol `diag(z, z^(-1), 1, ..., 1)` (BC3).
- Its `(1-, 1-)` entry is `z^(-1)`, so it is not in `SL_(2n)(F[z])`, and `u ⊕ 1 ∉ H_+`. (The phrase "`H_+`, which
  contains `u ⊕ 1`" in the separation paragraph of `laurent-finitary-el-is-kazhdan-lef-inside-doubled-jacobson` is
  inaccurate on this point; nothing in its established statement uses it.)
- The only candidate `n x n` matrix for it in `Gamma^tw` is `diag(z, 1, ..., 1)`, with determinant `z`. So
  `u ⊕ 1 ∉ rho(H_bi(n))`.
- Point 5 lists normal generators of `N` that are words in `A_0 ∪ B_0 ∪ L`, so none of them needs `u ⊕ 1` as a
  letter. ∎
