# Diagonal tensor powers of the Leavitt unit group algebra carry no rank function below the characteristic

Lane `w4-tensor-rankfn`, 2026-09-12. This artifact supports two nodes:
- `odd-char-leavitt-unit-tensor-images-have-no-rank-function`: established on paper, verification requested
  from `w3-vf-linear`;
- `binary-leavitt-unit-tensor-images-have-no-rank-function`: open.

Cited:
- [SG] = `research/artifacts/sylvester-rank-function-two-root-gate-2026-09-12.md`;
- [DI] = `research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md`.

## 0. Setup

- **Ring and group:** `K` is a field of characteristic `p > 0`, `R = L_K(1,2)`, and `Γ = R^x = EL_3(R)`
  through the three-leaf prefix code `(0, 10, 11)`. The element `e_ij(a)` is the matrix unit with entry `a`,
  and `x_ij(a) = 1 + e_ij(a)`. The diagonal units are cylinder projections: `e_11 = p_[0]`, `e_22 = p_[10]`,
  `e_33 = p_[11]`.
- **The handle:** for `n >= 1` let `Δ_n : K[Γ] -> R^(⊗n)` (tensor over `K`) send `[g]` to `g^(⊗n)`. This is a
  unital ring homomorphism; write `B_n` for its image.
  - Take any `R`-module `W`, with `Γ` acting diagonally on `W^(⊗n)`. The representation factors through `B_n`,
    via the ring map `R^(⊗n) -> End_K(W^(⊗n))`.
  - This is the only live handle of [SG] Section 3.4.
- **Rank facts** (Sylvester matrix rank functions, [DI] Sections 1–2):
  - `rk(xy) <= min(rk x, rk y)`;
  - `rk(x + y) <= rk x + rk y`;
  - `rk(u x u^-1) = rk x` for units `u`;
  - orthogonal idempotents add, so an idempotent `f <= e` has `rk f <= rk e`.

## 1. Theorem 1

**Theorem 1.** Let `2 <= n < p`.
- No ring `B` that receives a unital ring homomorphism from `B_n` carries a Sylvester matrix rank function.
- Equivalently, every Sylvester matrix rank function on `K[Γ]` is nonzero somewhere on `ker Δ_n`.

The two forms are equivalent because a rank function that vanishes on `ker Δ_n` descends to `B_n`: its null
set is an ideal ([DI] Remark 1.2).

*Step 1: symmetrized roots lie in `B_n`.*
- **Definition:** for `i != j` and `a_1, ..., a_n in R`, put
  `Sym_ij(a_1, ..., a_n) = Σ_(σ in S_n) e_ij(a_σ(1)) ⊗ ... ⊗ e_ij(a_σ(n))`.
- **Additivity:** `e_ij(a) e_ij(b) = 0`, so `(1 + e_ij(a))(1 + e_ij(b)) = 1 + e_ij(a + b)`, and
  `Δ_n(x_ij(c)) = (1 + e_ij(c))^(⊗n)`.
- **Inclusion–exclusion:** in `Σ_(T ⊆ [n]) (-1)^(n-|T|) Δ_n(x_ij(Σ_(k in T) a_k))`, the only surviving terms
  are those in which every index `k` occupies some slot. With `n` slots and `n` indices that means each index
  occupies exactly one slot, so the sum is `Sym_ij(a_1, ..., a_n)`, which therefore lies in `B_n`.

*Step 2: two isometries with orthogonal ranges.*
- **Setup:** choose `2n` pairwise incomparable words `α_1..α_n, β_1..β_n`, and put `P_i = e_ii^(⊗n)`. Define
  - `S_0 = Sym_12(s_(α_1), ..., s_(α_n))` and `T_0 = (n!)^(-1) Sym_21(t_(α_1), ..., t_(α_n))`;
  - `S_1` and `T_1` the same way from the `β_k`.
  Only here is `n < p` used.
- **Products:** `e_21(t) e_12(s) = e_22(ts)`, and `t_γ s_δ = [γ = δ]` for incomparable words. So
  `T_a S_b = (n!)^(-1) Σ_(σ,τ) ⊗_s e_22(t_(γ_σ(s)) s_(δ_τ(s)))`, where `γ` is family `a` and `δ` is family `b`.
  - If `a = b`, a summand is nonzero only when `σ = τ`, and then it equals `P_2`. So `T_0 S_0 = T_1 S_1 = P_2`.
  - If `a != b`, every summand vanishes, so `T_0 S_1 = T_1 S_0 = 0`.
- **Corners:** each slot factorizes, so `S_a = P_1 S_a P_2` and `T_a = P_2 T_a P_1`.
- **Ranges:** `f_a = S_a T_a` are idempotents in `P_1 B_n P_1`, and they are orthogonal:
  `f_0 f_1 = S_0 (T_0 S_1) T_1 = 0`.

*Step 3: `P_2` has rank zero.*
- **Bound from the ranges:** `rk f_a >= rk(T_a f_a S_a) = rk P_2`. Also `f_0 + f_1 <= P_1`, so
  `rk P_1 >= 2 rk P_2`.
- **Conjugation:** `w = e_12(1) - e_21(1) + e_33(1)` lies in `EL_3(F_p) <= Γ` and satisfies `w e_22 w^-1 = e_11`,
  so `Δ_n(w) P_2 Δ_n(w)^-1 = P_1` and `rk P_1 = rk P_2`.
- **Conclusion:** `rk P_2 = 0`. Note that `P_2 = T_0 S_0` lies in `B_n`.

*Step 4: the identity has rank zero.*
- **Conjugates of `P_2`:** Thompson's group `V <= Γ` acts transitively on proper nonempty clopen subsets of
  `{0,1}^N` (standard), and `g p_A g^-1 = p_(gA)`. So `p_A^(⊗n) = Δ_n(g) P_2 Δ_n(g)^-1` lies in `B_n` and has
  rank `0` for every proper nonempty clopen `A`.
- **Expanding the identity:** partition the Cantor set into `n + 1` nonempty clopens `A_1, ..., A_(n+1)`, and
  expand `1 = (Σ_i p_(A_i))^(⊗n)` as a sum over maps `f : [n] -> [n+1]`. Grouping by the image `S` of `f`
  gives
  `1 = Σ_(1 <= |S| <= n) Σ_(T ⊆ S) (-1)^(|S|-|T|) p_(A_T)^(⊗n)`, with `A_T = ∪_(i in T) A_i`.
- **Why every term is null:** each `A_T` with `T` nonempty is proper, because `|T| <= n < n + 1`, and `T = ∅`
  contributes `0`. So `rk 1 = 0`, contradicting `rk 1 = 1`. ∎

**Remarks.**
- **Where `p` enters:** only through invertibility of `n!`.
  - For `p = 2` only `n = 1` qualifies, and that case is [SG] Section 3.3, the evaluation map.
  - For `p = 3` the case `n = 2` is new.
- **Ternary corner:** a detecting rank function on `F_3[L_(F_3)(1,2)^x]` would refute the ternary corner. By
  Theorem 1 it cannot come from `W ⊗ W`, for any `R`-module `W` and any normalization of ranks on it.
  Ultraproducts, regular envelopes and rank completions of the image all count as rings receiving a map from
  `B_2`.
- **Binary square:** in characteristic two `T_a S_a = 2 P_2 = 0`, and Step 2 dies exactly at the scalar `n!`.
  That case is the open claim `binary-leavitt-unit-tensor-images-have-no-rank-function`.
- **Degrees `n >= p`:** in odd characteristic these are open for the same reason.
