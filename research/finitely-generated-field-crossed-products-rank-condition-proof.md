---
rg: 2
id: finitely-generated-field-crossed-products-rank-condition-proof
kind: route
title: Spread a finitely generated field out to a domain, reduce modulo a prime avoiding the minimal primes of one element, and replace Schwartz–Zippel by Lang–Weil in the partial-substitution model
target: finitely-generated-field-crossed-products-have-rank-condition
requires: [lang-weil-point-count]
---

Notation: `k ∈ {Q, F_p}` is the prime field of `K`, and `k_0 = Z` or `F_p` is its prime ring. `K ⋊ G` is the skew
group ring, `(a u_g)(b u_h) = a σ_g(b) u_{gh}`.

## 0. What is reused

Sections 1, 2 and 4 of `rational-function-field-crossed-products-rank-condition-proof` (the finite model `π`,
Lemmas 1–3, and Lemma 4 except its last sentence) use only the following properties of `R` and `K`:

- (R1) `R ⊂ K` is a subring containing `k_0` with `Frac R = K`, generated as a `k_0`-algebra by `x_1..x_n`.
- (R2) Every `a ∈ K` lies in some `R_c = R[1/c]` with `c ∈ R∖{0}`. This follows from (R1): if `a = r/s`, take `c = s`.
- (R3) `σ_g(x_i) ∈ R_c` for all `i` implies `σ_g(R) ⊆ R_c`, because `σ_g` fixes `k_0`.
- (R4) If `σ_g ≠ σ_{g_0}` then `σ_g(x_i) ≠ σ_{g_0}(x_i)` for some `i`. Two ring homomorphisms that agree on `k_0` and on
  the generators agree on `R`, hence on `K = Frac R`.
- (R5) `Ω = Hom_ring(R, F_q)` is a finite set, and each `φ ∈ Ω` with `φ(c) ≠ 0` extends uniquely to `φ_c: R_c -> F_q`.

Nothing in those sections uses that `R` is a polynomial ring. The only uses of Schwartz–Zippel (Lemma 0) are the
point counts in Sections 3 and 4, which Section 3 below replaces. So **Lemmas 1–3 and the rank part of Lemma 4 hold
verbatim** for any finitely generated `k_0`-subalgebra `R ⊂ K` with `Frac R = K`, and for any prime power `q`.

In counting form, write `N = |Ω|` and `b_q(D) = |{φ ∈ Ω : φ(D) = 0}|`. Then:
- Lemma 2 + Lemma 3 give `rank(π(A)π(B) - I_{dN}) <= d · b_q(D)`;
- Lemma 4 gives `rank π(y) >= (N - b_q(D_y)) / (2t + 1)`.

The proof of Lemma 4 bounds the greedy selection only through the good set, whose size is `N - b_q(D_y)`. The
maps are partial injections, and `τ_{g^{-1}} τ_g φ = φ` at good points.

## 1. Commutative algebra (standard imports, with proofs sketched)

**Lemma A (points and dimension).** Let `S = F_p[X_1..X_d] / (P_1..P_m)` and `V = {x ∈ F̄_p^d : P_i(x) = 0 ∀ i}`.
1. `Hom_ring(S, F_q) ≅ V ∩ F_q^d`, via `φ ↦ (φ(X_1), ..., φ(X_d))`.
2. If `S ≠ 0`, then `V ≠ ∅` and `dim V = dim S` (Krull dimension).

*Proof.*
- Item 1: ring homomorphisms `S -> F_q` fix `F_p`, so they are determined by the images of the `X_i`, which must
  satisfy the `P_i`.
- Item 2 uses three facts.
  - Noether normalization gives a finite injective `F_p[t_1..t_e] -> S`, and integral extensions preserve Krull
    dimension (Cohen–Seidenberg), so `e = dim S`.
  - Base change to `F̄_p` is flat, so `F̄_p[t_1..t_e] -> F̄_p ⊗ S` is still finite and injective. Hence
    `dim (F̄_p ⊗ S) = e`, and `F̄_p ⊗ S ≠ 0`.
  - `F̄_p ⊗ S = F̄_p[X]/(P_i)`, whose reduced quotient is the coordinate ring of `V`. Passing to the reduced quotient
    does not change the dimension, and the Nullstellensatz over `F̄_p` makes `V` nonempty with `dim V = e`. ∎

**Lemma B (dimension drop).** Let `S ≠ 0` be a finitely generated algebra over a field, and let `D ∈ S` lie in no
minimal prime of `S`. Then `S/(D) = 0` or `dim S/(D) <= dim S - 1`.

*Proof.* Let `Q ⊇ (D)` be prime. `Q` contains a minimal prime `P`, and `P ≠ Q` because `D ∉ P`. A chain of primes
ascending from `Q` extends downward by `P`, so `dim S/Q + 1 <= dim S/P <= dim S`. Finally
`dim S/(D) = max_Q dim S/Q`. ∎

**Lemma D (choice of p in characteristic 0).** Let `R` be a finitely generated `Z`-algebra that is a domain of
characteristic 0, and let `D ∈ R∖{0}`. There is a prime `p` with `pR ≠ R` such that `D` lies in no minimal prime of
`R` over `pR`. Equivalently, the image of `D` lies in no minimal prime of `R/pR`.

*Proof.*
- **Only finitely many primes are bad.**
  - Let `Q` be minimal over `pR` with `D ∈ Q`. Since `R` is a Noetherian domain and `p ≠ 0`, Krull's principal ideal
    theorem gives `ht Q = 1`.
  - Any prime `P` with `(D) ⊆ P ⊆ Q` is nonzero, because `D ≠ 0`, so `P = Q`. Hence `Q` is one of the finitely many
    minimal primes `Q_1..Q_s` over `(D)`. (If `D` is a unit there are none, and every `p` works.)
  - `p ∈ Q_i` forces `Q_i ∩ Z = pZ`. So the bad primes lie in the finite set `L = {ℓ : Q_i ∩ Z = ℓZ for some i}`.
- **Some good prime exists.**
  - Let `F = ∏_{ℓ ∈ L} ℓ`. Then `R[1/F]` is a nonzero finitely generated `Z`-algebra, since `R` is a domain of
    characteristic 0.
  - Take a maximal ideal `m` of `R[1/F]`. The field `R[1/F]/m` is finitely generated as a ring, hence finite (general
    Nullstellensatz: `Z` is a Jacobson ring).
  - Let `p` be its characteristic. Then `p ∉ L`, because `F` is invertible. Also `p ∈ m ∩ R`, a proper ideal, so
    `pR ≠ R`. ∎

## 2. Choice of the model ring

Let `K` be finitely generated over `k`, and fix finite data: a finite `T ⊂ G` and finitely many elements of `K`.
- Choose field generators `x_1..x_n` of `K` over `k`.
- Put `R = k_0[x_1..x_n] ⊂ K`, a finitely generated `k_0`-algebra and a domain with `Frac R = K`. So (R1)–(R5) hold.
- Choose `c ∈ R∖{0}` as in Section 1 of the rational route: all `σ_g(x_i)` for `g ∈ T`, and all coefficients, lie in
  `R_c`.

## 3. The counting lemma

**Lemma C.** Let `R` be as in Section 2 and `D ∈ R∖{0}`. There are a prime `p` (equal to `char K` in positive
characteristic) and `a >= 1` such that, for `q = p^{aj}`,

```text
N_q = |Hom(R, F_q)| >= 1  for large j,   and   b_q(D) / N_q -> 0  as j -> infinity.
```

*Proof.*
- **Choose `p` and `S`.**
  - In characteristic `p`, put `S = R`. It is a domain with unique minimal prime `0`, which does not contain `D`.
  - In characteristic 0, choose `p` by Lemma D and put `S = R/pR ≠ 0`. The image `D̄` lies in no minimal prime of `S`.
- **Reduce to `S`.** Every `φ: R -> F_q` kills `p`. So `Hom(R, F_q) = Hom(S, F_q)`, and
  `b_q(D) = |Hom(S/(D̄), F_q)|`.
- **Present `S` and `S/(D̄)`.**
  - `S` is a finitely generated `F_p`-algebra. Write `S = F_p[X_1..X_d]/(P_1..P_m)`, which is possible since
    polynomial rings are Noetherian.
  - Let `D̃` be a lift of `D̄`. Then `S/(D̄) = F_p[X]/(P_1..P_m, D̃)`.
  - Let `V` and `W` be the corresponding zero sets in `F̄_p^d`. Both are defined over `F_p` by fixed polynomials,
    independent of `q`.
- **Dimensions.** By Lemma A, `N_q = |V(F_q)|`, `b_q(D) = |W(F_q)|`, `V ≠ ∅`, and `dim V = e := dim S`.
  - By Lemma B, either `W = ∅` (so `b_q = 0`), or `dim W = dim S/(D̄) <= e - 1`.
- **Count points.**
  - By (LW-up) of `lang-weil-point-count`, `b_q(D) <= C_W q^{e-1}` for all `q`.
  - By (LW-low), there are `a` and `j_0` with `N_q >= q^e / 2` for `q = p^{aj}`, `j >= j_0`.
  - Hence `b_q(D)/N_q <= 2 C_W / q -> 0`. ∎

## 4. Proof of Theorem 1

Let `AB = I_d` with `r < d`. Choose `T`, `c` and `D = c · ∏_{g ∈ S_A} c'_g` as in Lemma 2 of the rational route,
inside the ring `R` of Section 2. Take `p` and `a` from Lemma C for this `D`.

The identities in Lemmas 1–3 hold in `R_c`. They are pushed through `φ_c`, so they hold for every such `q`.
- **Lower bound.** `rank(π(A)π(B)) >= dN_q - d b_q(D)`.
- **Upper bound.** `π(A)π(B)` factors through `F_q^{r N_q}`, so its rank is at most `r N_q`.
- **Contradiction.** `(d - r) <= d · b_q(D)/N_q`, which tends to 0. This is false for large `j`. ∎

## 5. Proof of Theorem 2 (faithful σ)

Follow Section 4 of the rational route.
- **Setup.** Let `AB = I_d` and suppose `C = BA - I_d ≠ 0`. Let `y` be a nonzero entry of `C`, with support `T_y`
  of size `t`.
  - Choose one `T` and `c` serving Lemma 2 for `AB` and `BA`, and Lemma 4 for `y`. By (R4), `D_y` is defined as there.
  - Let `D` be the product of the three hypersurface elements. It is divisible by `c` and by `D_y`, so
    `b_q(D_y) <= b_q(D)`.
  - Take `p` and `a` from Lemma C for `D`.
- **Upper bound on `rank π(C)`.** Put `X = π(A)`, `Y = π(B)` and `ε = d · b_q(D)`.
  - `rank(XY - I) <= ε` gives `rank(YX - I) <= 2ε`.
  - `π(C)` differs from `YX - I` only on rows with `φ(D) = 0`, so `rank π(C) <= 3ε`.
- **Lower bound.** `π(y)` is a block of `π(C)`, so by Lemma 4,
  `(N_q - b_q(D)) / (2t+1) <= rank π(y) <= 3 d · b_q(D)`.
- **Contradiction.** Dividing by `N_q` gives `1 - b_q/N_q <= 3d(2t+1) · b_q/N_q`. The right side tends to 0, so
  this fails for large `j`. Hence `C = 0`. ∎

## 6. Local form

Fix `A` and `B`, and in Theorem 2 also `y`, over `K' ⋊ G`. Choose the finite data first:
- `T` contains `S_A ∪ S_B ∪ S_A S_B ∪ S_B S_A`, and, for Theorem 2, `T_y ∪ T_y^{-1}`.
- `E` contains all coefficients of `A` and `B`.
- For Theorem 2 (faithful `σ`), `E` also contains, for each `g ≠ g_0` in `T_y`, one `a_g ∈ K'` with
  `σ_g(a_g) ≠ σ_{g_0}(a_g)`.

Then take a finitely generated subfield `K_0 ⊇ E` with `σ_g(K_0) ⊆ K_0` for all `g ∈ T`. So faithfulness of `σ` on
`K'` already gives `σ_g|_{K_0} ≠ σ_{g_0}|_{K_0}`.

The proofs above use only the following:
- the finitely many coefficient identities of `AB = I_d` and `BA - I_d`. These are computed in `K_0` using
  `σ_g|_{K_0}` for `g ∈ T`;
- `σ_g σ_h = σ_{gh}` on `K_0`;
- `σ_{g^{-1}} σ_g = id`;
- `σ_g|_{K_0} ≠ σ_{g_0}|_{K_0}` for `g ≠ g_0` in `T_y` (Theorem 2 only).

Here each `σ_g|_{K_0}` is an injective ring endomorphism, and Lemmas 1–4 need nothing more. Run Sections 2–5 with
`R ⊂ K_0`.

## 7. Remarks (not part of the established claim)

- **Twist.** A 2-cocycle must become a coboundary on the finite models, as in Remark 5 of the rational route. The
  ternary Leavitt route is exactly such a twist.
- **Non-locally-stable fields.** In `F_p(x_g : g ∈ G)` with a shift action, no finitely generated subfield is stable
  under any `σ_g` with `g` of infinite order that moves a variable. So `Hom(R, F_q)` has no `τ`-stable finite form,
  and a sofic approximation of `G` would be needed instead.
- **Literature novelty** was not checked. The argument is the standard "reduce modulo p and count" pattern.
