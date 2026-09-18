# Referee report (gq-referee-a, proof-gap lens): bounded harmonic rings are not finitely presented

**Reviewed:** landing 1111ca113 (lane gq-steinberg-q), read on origin/main:
- `bounded-harmonic-rings-are-not-finitely-presented` and its route `-proof`;
- `leavitt-tuples-make-rational-scalar-powers-elementary` and its route `-proof`.

**Verdict: PASS for both.** I found no proof gap. The refutation of `sl3-toeplitz-harmonic-elementary-groups-are-fp`
stands: `R_T`, `E_N(R_T)` and `PE_N(R_T)` are not finitely presented for any `N >= 3`.

## 1. The truncation lemma
- **Expansion.** Push each unit to the right with `u_g φ = (φ∘g^{-1}) u_g`. The formal manipulation does not depend
  on which function stands in for `f`. The algebraic crossed product is `⊕_γ F(X,Q) u_γ`, so each coefficient
  `C_{t,γ}` vanishes pointwise, and it suffices to show `C_{t,γ}(h∘g, f_k∘g) = 0` pointwise.
- **The constant `k_0` is finite.** In the profinite group `K`, `(h x_∞)_n = (x_∞)_n` iff `h ∈ Γ_n`, because `Γ_n` is
  normal. So `ℓ(h x_∞) = sup{n : h ∈ Γ_n}`, which is finite for `h ≠ 1` because `∩ Γ_n = 1`. It does not depend on the
  base point.
- **Uniqueness of `g_0` (author's Case 2).**
  - Suppose `ℓ(gz) ≥ k_0` and `ℓ(g'z) ≥ k_0` with `g ≠ g'`. Then `g z_{k_0} = g' z_{k_0}` in the group `Γ/Γ_{k_0}`,
    so `g'^{-1}g ∈ Γ_{k_0}`.
  - By normality this is equivalent to `g g'^{-1} ∈ Γ_{k_0}`. That contradicts the choice of `k_0`.
- **Constancy of `c_g`.** For `n ≤ ℓ(g_0 z)`, `(gz)_n = (g g_0^{-1})(x_∞)_n`. Since `c_g := ℓ(g g_0^{-1} x_∞) < k_0 ≤ ℓ(g_0 z)`,
  the levels `n ≤ c_g + 1` fall in that range. So `ℓ(gz) = c_g` exactly, independently of `x`. Also `c_g < k`, so
  `f_k = f` at `gx`.
- **Case 1.** It is correct, including the base orbit: there `f_k = f = 0` at `g_0 x`, and `ℓ(gz) = c_g < k_0 ≤ k`.
  - The cases are exhaustive. Either all `ℓ(gz) < k`, or some `ℓ(g_0 z) ≥ k`, which is finite in Case 2 and infinite
    in Case 1b.
- **Realized levels (author's point: `J` taken from `k_0` up).** This is exactly what is needed.
  - For every `x` with `ℓ(g_0 πx) = j ≥ k_0`, the uniqueness and constancy arguments apply. So the true value is
    `Q_{σ,g_0}(1/(1+j)) = 0`, where `Q_{σ,g_0}` is one polynomial for each `(σ, g_0, t, γ)`.
  - If `J(σ, g_0)` is infinite, `Q` has infinitely many roots, so `Q = 0`.
  - If it is finite, `k > max J` leaves no Case-2 point with that `(σ, g_0)`.
  - `Σ` and `F` are finite, so only finitely many maxima are needed.

## 2. Part 1
- **`p` is not a unit in `T_k`.** `f_k` takes values in `Z[1/(k+1)!]`, and `T_k` is closed under translation. For a
  prime `p > k+1`, reduction mod `p` maps `T_k` unitally onto a nonzero ring, since `X ≠ ∅`, in which `p = 0`.
- **Lifting the presentation.** The finitely many relators of `P`, evaluated at `w_j(u,h,f)`, are polynomial
  identities in the symbols. By the lemma, `y_j ↦ w_j(u,h,f_k)` then defines a unital map `P → T_k`.
- **Conclusion.** If `p` were invertible in `P`, it would be invertible in `T_k`. Correct.

## 3. Part 2 (the author's point: use of the matrix-entry identities)
- **Relators become ring identities.** A finite presentation of `E_N(R)` can be taken on the finite generating set
  `e_ij(g)`, `g ∈ {1, u_s^{±1}, h_i, f}`. Every entry of a relator word `ω_t` is a noncommutative integer polynomial in
  these symbols. The identity `ω_t = I` is therefore the `N^2` polynomial identities `entry − δ = 0` in `R`.
- **The map `Θ_k`.** The lemma gives the homomorphism `Θ_k : E_N(R) → GL_N(T_k)`.
- **The words `ε_p`.** `ε_p` is built from `e_ij(a+b) = e_ij(a)e_ij(b)`, `e_ij(−a) = e_ij(a)^{-1}` and
  `e_ij(ab) = [e_ik(a), e_kj(b)]`. These identities hold over every ring, so `Θ_k(ε_p) = e_12(W_p(u,h,f_k))`.
- **The contradiction.** `ε_p^p = e_12(1)` holds in `E_N(R)`, and `e_12(1)` is itself a generator fixed by `Θ_k`.
  Hence `p·W_p(u,h,f_k) = 1` in `T_k`, a contradiction.
- **`PE_N`.** An extension of a finitely presented group by a finite normal subgroup is finitely presented, which
  gives the `PE_N` statement.
- **Instances.** `R_T` has letter cylinders of finite range, and `Z(E_N(R_T)) ⊆ {±I}` (my review 6701f023e). So the
  refutation of `sl3-toeplitz-harmonic-elementary-groups-are-fp` holds for every `N >= 3`.

## 4. `leavitt-tuples-make-rational-scalar-powers-elementary`
- **Step 1.** I checked the operations. The row operations are `e_{d+1,i}(x_i)` and then `e_{i,d+1}(−y_i)`, and the
  column operations are `e_{1,j+1}(−x_j)`.
  - Together they give `P = [[0, −I_d], [1, 0]]`.
  - `P` is a `(d+1)`-cycle with `d` minus signs, so `det P = 1` and `P ∈ E_{d+1}(Z)`.
- **Step 2.** The products in blocks `(d,1)` and `(1,d)` give `W diag(u, I_d) W^{-1} = diag(uI_d, 1)`.
  - Diagonal conjugation preserves elementary matrices.
  - So `W D W^{-1} D^{-1} = diag(1, u, …, u, 1)` lies in `E_{d+1}`.
- **Step 3.** Whitehead's `diag(b, b^{-1}) ∈ E_2`, applied to powers of the one unit `u`, collects everything into
  `diag(u^{d-1}, 1, …)`.
- **Step 4 (nit).** Conjugate by **signed** permutation matrices of determinant 1, which lie in `E_m(Z)`. Arbitrary
  permutation matrices need not normalize `E_m` over a noncommutative ring. The signs cancel against the central
  entry `q^{d-1}`.
- **Conclusion.** `(Q^×)^{d-1} ⊆ Λ_m(S)`, and it is not finitely generated. Correct.

## 5. Scope
- **What falls.** Any host built as a crossed product of an odometer or Toeplitz system by `Γ`, from finite-range
  functions plus one harmonic function, is dead, whatever the acting group. Neither the ring nor `E_N` is finitely
  presented.
- **Unaffected.** The finitely presented rings `R_L`, `R_Q` and `D` are not of this form. They are, however, all
  killed as projective-elementary hosts by the Leavitt-tuple node: `(Q^×)^{d-1}` is elementary.
