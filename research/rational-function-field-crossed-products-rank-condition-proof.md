---
rg: 2
id: rational-function-field-crossed-products-rank-condition-proof
kind: route
title: Reducing a rational function field modulo p turns any group action into partial substitutions on F_q^n that are exact off one hypersurface, so a Schwartz–Zippel count bounds every rank defect
target: rational-function-field-crossed-products-have-the-rank-condition
requires: []
---

Notation: `k ∈ {Q, F_p}`, `k_0 = Z` or `F_p`, `R = k_0[x_1, ..., x_n]`, `K = k(x_1..x_n) = Frac(R)`. Every
automorphism fixes `k`. For `c ∈ R∖{0}` put `R_c = R[1/c] ⊂ K`. Every `a ∈ K` lies in some `R_c`.

## 0. Schwartz–Zippel (elementary, proved here)

**Lemma 0.** Let `F` be a field, `S ⊆ F` finite, and `P ∈ F[x_1..x_n]` nonzero of total degree `δ`. Then
`|{s ∈ S^n : P(s) = 0}| <= δ |S|^{n-1}`.

*Proof.* Induct on `n`. For `n = 1`, a nonzero polynomial has at most `δ` roots. For `n > 1`, write
`P = Σ_{j<=e} P_j(x_1..x_{n-1}) x_n^j` with `P_e ≠ 0` of degree `<= δ - e`.
- If `P_e(s') = 0`: at most `(δ-e)|S|^{n-2}` choices of `s'`, times `|S|` choices of `s_n`.
- Otherwise `P(s', ·)` is a nonzero polynomial of degree `e` in `x_n`, so at most `|S|^{n-1} · e` zeros.
The total is at most `δ|S|^{n-1}`. ∎

## 1. The finite model

Fix a prime `p`, with `p = char k` in characteristic `p`. Let `q` be a power of `p`, with `q = p` when `k = Q`.
Put `Ω = Hom_ring(R, F_q)`. Evaluation at `ω ∈ F_q^n` gives `Ω = F_q^n`, so `N := |Ω| = q^n`.

For `φ ∈ Ω` with `φ(c) ≠ 0` there is a unique ring homomorphism `φ_c : R_c -> F_q` extending `φ`. Uniqueness
holds because every element of `R_c` is `r/c^m`.

**Data.** Fix a finite `T ⊂ G` and `c ∈ R∖{0}` with `σ_g(x_i) ∈ R_c` for all `g ∈ T` and all `i`, so that
`σ_g(R) ⊆ R_c` for `g ∈ T`.

**Partial maps.** For `g ∈ T` and `φ(c) ≠ 0`, put `τ_g φ := φ_c ∘ σ_g|_R ∈ Ω`. Here `τ_1 φ = φ`.

**Matrices.** Functions `f: Ω -> F_q^m` form `F_q^{mN}`.
- For a matrix `M` over `R_c`: `(ev(M) f)(φ) = φ_c(M) f(φ)` if `φ(c) ≠ 0`, and `0` otherwise.
- For `g ∈ T`: `(P_g f)(φ) = f(τ_g φ)` if `φ(c) ≠ 0`, and `0` otherwise.
- For `X = Σ_{g∈T} X_g u_g` (a matrix over `K ⋊ G` with every `X_g` over `R_c`): `π(X) := Σ_g ev(X_g) P_g`.
  This is an `F_q`-matrix of size `(rows of X)·N × (columns of X)·N`.

**Lemma 1 (composition off a hypersurface).** Let `g, h, gh ∈ T`. Since `σ_g(c) ∈ R_c∖{0}`, write
`σ_g(c) = c'_g / c^m` with `c'_g ∈ R∖{0}`. Let `φ(c c'_g) ≠ 0`. Then `φ_c` extends to a ring homomorphism
`φ^ : R_{c c'_g} -> F_q`, and:
1. `(τ_g φ)(c) ≠ 0`, and `(τ_g φ)_c = φ^ ∘ σ_g|_{R_c}`;
2. `τ_h τ_g φ = τ_{gh} φ`;
3. `(τ_g φ)_c(b) = φ_c(σ_g b)` for every `b ∈ R_c` with `σ_g(b) ∈ R_c`.

*Proof.*
- `σ_g(R_c) = σ_g(R)[1/σ_g(c)] ⊆ R_c[c^m/c'_g] ⊆ R_{c c'_g}`, so `φ^ ∘ σ_g` is a ring homomorphism `R_c -> F_q`
  extending `τ_g φ`. By uniqueness it equals `(τ_g φ)_c`. Also `(τ_g φ)(c) = φ^(σ_g c) = φ(c'_g)/φ(c)^m ≠ 0`.
  This gives (1) and (3), since `φ^` restricts to `φ_c` on `R_c`.
- (2): `τ_h τ_g φ = (τ_g φ)_c ∘ σ_h|_R = φ^ ∘ σ_g ∘ σ_h|_R = φ^ ∘ σ_{gh}|_R`. Since `σ_{gh}(R) ⊆ R_c` and `φ^`
  extends `φ_c`, this is `τ_{gh} φ`. ∎

## 2. Products are modelled off one hypersurface

**Lemma 2.** Let `A = Σ_{g∈S_A} A_g u_g` (size `d × r`) and `B = Σ_{h∈S_B} B_h u_h` (size `r × m`). Put
`T ⊇ S_A ∪ S_B ∪ S_A S_B`, and choose `c` as in Section 1 so that every entry of `A_g`, `B_h` and `σ_g(B_h)` lies
in `R_c`. Put `D = c · Π_{g∈S_A} c'_g ∈ R∖{0}`. Then at every row `(φ, i)` with `φ(D) ≠ 0`, `π(A)π(B)` and
`π(AB)` agree. Here `AB = Σ_k (Σ_{gh=k} A_g σ_g(B_h)) u_k` has all coefficients over `R_c`, and `k ∈ S_A S_B ⊆ T`.

*Proof.* Fix `f: Ω -> F_q^m` and `φ` with `φ(D) ≠ 0`. By Lemma 1(1), `τ_g φ` has `(τ_g φ)(c) ≠ 0` for `g ∈ S_A`.
Then
`(π(A)π(B)f)(φ) = Σ_g φ_c(A_g) (π(B)f)(τ_g φ) = Σ_{g,h} φ_c(A_g) (τ_g φ)_c(B_h) f(τ_h τ_g φ)`.
By Lemma 1(3) and (2) this is
`Σ_{g,h} φ_c(A_g σ_g(B_h)) f(τ_{gh} φ) = Σ_k φ_c(Σ_{gh=k} A_g σ_g(B_h)) f(τ_k φ) = (π(AB)f)(φ)`. ∎

**Lemma 3.** `π(I_d) = I_{dN}` at every row `(φ, i)` with `φ(c) ≠ 0`.

## 3. Proof of Theorem 1

Let `AB = I_d` with `r < d`. Choose `T`, `c`, `D` as in Lemma 2, and also make `c` a factor of `D`. Let `δ = deg D`.
- **Choice of `p`.** In characteristic 0, `D ∈ Z[x]` is nonzero, so choose `p` not dividing one of its nonzero
  coefficients. Then `D mod p` is nonzero of degree `<= δ`. Every step of Sections 1–2 works over this `p`,
  because the identities used hold in `R_c` and are pushed through `φ_c`.
- **Rank bound.** By Lemmas 2 and 3, `π(A)π(B) - I_{dN}` vanishes outside the rows `(φ, i)` with `φ(D) = 0`.
  By Lemma 0 with `S = F_q`, there are at most `d δ q^{n-1}` such rows. So
  `rank(π(A)π(B)) >= d q^n - d δ q^{n-1}`.
- **Contradiction.** `π(A)π(B)` factors through `F_q^{rN}`, so its rank is at most `r q^n`. Hence
  `(d - r) q <= d δ`, which is false once `q > d δ`. Any `p` in characteristic 0, or any power of `p` in
  characteristic `p`, eventually gives such a `q`. ∎

**Local form.** The proof uses only the finitely many elements in the entries, the maps `σ_g` for `g ∈ T`, and
`σ_g σ_h = σ_{gh}`. All of these live in any `K_0 = k(x_1..x_n) ⊆ K'` with `E ⊆ K_0` and `σ_g(K_0) ⊆ K_0` for
`g ∈ T`. So run the argument with `R = k_0[x_1..x_n]` inside `K_0`.

## 4. Proof of Theorem 2 (faithful σ)

**Lemma 4 (faithful rows are thick).** Let `σ` be faithful and `y = Σ_{g∈T_y} y_g u_g ∈ K ⋊ G` with every `y_g ≠ 0`
and `t = |T_y| >= 1`. Fix data `T ⊇ T_y ∪ T_y^{-1} ∪ {1}` and `c` as in Section 1, with all `y_g ∈ R_c`. There is
`D_y ∈ R∖{0}`, depending only on this data and not on `q`, such that
`rank π(y) >= (q^n - deg(D_y) q^{n-1}) / (2t + 1)` whenever `D_y mod p ≠ 0`.

*Proof.*
- **Choice of `D_y`.** Fix `g_0 ∈ T_y`. For each `g ∈ T_y∖{g_0}` we have `σ_g ≠ σ_{g_0}`, and both fix `k`, so some
  `σ_g(x_{i(g)}) - σ_{g_0}(x_{i(g)})` is nonzero. Let `e_g ∈ R∖{0}` be its numerator over a power of `c`, and let
  `y'` be the numerator of `y_{g_0}`. Let `D_y` be the product of `c`, `y'`, all `e_g`, and `c'_g` for
  `g ∈ T_y ∪ T_y^{-1}`.
- **Good rows.** Call `φ` good if `φ(D_y) ≠ 0`. Then:
  1. `τ_g φ ≠ τ_{g_0} φ` for `g ≠ g_0`, because they differ on `x_{i(g)}`;
  2. row `φ` of `π(y)` is `Σ_g φ_c(y_g) e_{τ_g φ}`, with coefficient `φ_c(y_{g_0}) ≠ 0` at column `τ_{g_0} φ`;
  3. by Lemma 1(2) with `h = g^{-1}`, `τ_{g^{-1}} τ_g φ = φ` for `g ∈ T_y`.
- **Greedy selection.** Choose good `φ_1, φ_2, ...` so that for `i ≠ j`, column `τ_{g_0} φ_j` is not in the row
  support `{τ_g φ_i : g ∈ T_y}`. Selecting `φ_j` forbids:
  - every good `φ` with `τ_{g_0} φ = τ_g φ_j`. By item 3, `φ = τ_{g_0^{-1}} τ_g φ_j`, at most `t` of them;
  - every good `φ` with `τ_g φ = τ_{g_0} φ_j`. Then `φ = τ_{g^{-1}} τ_{g_0} φ_j`, at most `t` of them;
  - `φ_j` itself.
  So the selection continues until at least `|good| / (2t+1)` rows are chosen.
- **Rank.** On the chosen rows and the columns `τ_{g_0} φ_j`, `π(y)` restricts to a diagonal matrix with nonzero
  diagonal, so its rank is at least the number of chosen rows. Lemma 0 gives `|good| >= q^n - deg(D_y) q^{n-1}`.
  ∎

(The inverse formulas in the bullets use item 3 at the good point: `τ_{g_0}φ = ψ` implies
`φ = τ_{g_0^{-1}} ψ`. Here `ψ = τ_g φ_j` has `ψ(c) ≠ 0` by Lemma 1(1), so `τ_{g_0^{-1}} ψ` is defined, and it is
one point. Distinct `g` give at most `t` candidates.)

**Proof of Theorem 2.** Let `A, B ∈ M_d(K ⋊ G)` with `AB = I_d`, and suppose `C := BA - I_d ≠ 0`. Let `y` be a
nonzero entry of `C`. Choose one `T` and `c` serving Lemma 2 for both products `AB` and `BA`, and Lemma 4 for `y`.
Let `D` be the product of the three hypersurface polynomials and `δ = deg D`. Put `X = π(A)`, `Y = π(B)`, and let
`N = q^n`.
- By Lemmas 2 and 3, `E := XY - I` has rank at most `ε := d δ q^{n-1}`.
- `rank Y >= rank(XY) >= dN - ε`, and `(YX - I)Y = YE` has rank at most `ε`. So `YX - I` has rank at most `ε` on
  `im Y`, which has codimension at most `ε`. Hence `rank(YX - I) <= 2ε`.
- `π` is linear. `π(C) - (YX - I) = (π(BA) - YX) - (π(I_d) - I)`, and both terms vanish outside the rows with
  `φ(D) = 0` (Lemmas 2 and 3, `c | D`). So this difference has rank at most `ε`, and `rank π(C) <= 3ε`.
- In characteristic 0, choose `p` with `D mod p ≠ 0`, as in Section 3.
- `π(y)` is a block of `π(C)`, so Lemma 4 gives `(q^n - δ q^{n-1})/(2t+1) <= 3 d δ q^{n-1}`. This fails for large
  `q`. Hence `C = 0`. ∎

## 5. Remarks: where the method stops (not part of the established claim)

- **Cocycles.** With a 2-cocycle `α`, the model would have to send `u_g` to `ev(β_g) P_g` with
  `β_g · (β_h ∘ τ_g) = α(g,h) β_{gh}` at most points. So `α` would have to be a coboundary on the finite models.
  This fails for the ternary route (`n = 0`, `K = F_3`, one point, where `α` would have to be a coboundary
  outright). A twist is therefore the first place a witness can live over finitely generated rational fields.
- **Infinitely generated orbits.** For Bernoulli fields `F_p(x_g : g ∈ G)` with `G` shifting variables, no finite
  set of variables is closed under a finite `T`, so `Ω` has no finite `τ`-stable form. There one needs a sofic
  approximation of `G` instead (`sofic-lamplighter-bernoulli-crossed-products-have-rank-models` is the analogue).
- **Non-rational finitely generated fields.** Replace `R` by a finitely generated `k_0`-algebra `R` with
  `Frac R = K`, and `Ω` by `Hom(R, F_q)`. Lemmas 1–4 are unchanged. Lemma 0 would be replaced by
  `|V(D)(F_q)| = O(q^{n-1})` and `|Spec R(F_q)| >= q^n/2` for suitable `q`, which in characteristic 0 needs a
  good reduction of `R`. That is the Lang–Weil estimate plus spreading out. It is **not imported verbatim here**,
  so this extension (for instance automorphisms of K3 surface function fields) stays unrecorded as established.
- **By-product: soficity.** In characteristic `p` (or modulo a good `p`), Lemma 1(2) and item 1 of Lemma 4 show
  that the partial maps `τ_g` on `F_q^n` form sofic approximations of every group acting faithfully on
  `k(x_1..x_n)`, that is, of every subgroup of the Cremona group `Bir(P^n_k)`, `k` prime. This is probably
  known. Literature novelty of Theorems 1–2 was **not checked** in this lane.
- **Why no invariant measure is needed.** Regime (c) of `field-crossed-product-rank-condition-survival-cases`
  needs a measure on `Emb(K_0, C)` because birational maps do not preserve any measure on complex points. On
  `F_q^n` the maps `τ_g` are bijections off `O(q^{n-1})` points, so counting measure is almost invariant for free.
