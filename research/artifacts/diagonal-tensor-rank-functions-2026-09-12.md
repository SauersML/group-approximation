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

## 2. Characteristic two: where a rank function on the tensor square must live

Throughout `K = F_2`, `n = 2`, and `B_2` is the image of `Δ_2`.
- `Sym(x, y) = x ⊗ y + y ⊗ x`.
- `N = {Sym-sums}` is the image of `1 + flip` on `R ⊗ R`. It is an ideal of the flip-fixed algebra
  `(R ⊗ R)^(S_2)`, which contains `B_2`.
- For nonempty clopens `X`, `Y`, `u_(XY)` is a partial isometry of `R` with source `Y` and range `X`: a sum
  of monomials `s_γ t_δ` over a matching of cylinders. It satisfies `u_(XY) u_(YX) = p_X`.

**Lemma 2.1 (Tate–Frobenius quotient).** `x -> [x ⊗ x]` is a unital injective ring homomorphism
`Φ : R -> T(R) = (R ⊗ R)^(S_2)/N`. The image of `B_2` in `T(R)` is `Φ(R)`, so `B_2/(B_2 ∩ N) ≅ R`.

*Proof.*
- **Ring map:** `(x + y)^(⊗2) = x^(⊗2) + y^(⊗2) + Sym(x, y)`, so `Φ` is additive modulo `N`. It is exactly
  multiplicative and unital.
- **Image:** `Σ a_g [g ⊗ g] = Φ(Σ a_g g)`, and the evaluation `F_2[Γ] -> R` is onto.
- **`T(R)` has a basis:** take an `F_2`-basis `{b_i}` of `R` containing `1`. The flip permutes the basis
  `b_i ⊗ b_j`, so `T(R)` has basis `[b_i ⊗ b_i]`, and `Φ(1) != 0`.
- **Injectivity:** `R` is simple, so `Φ` is injective. ∎

**Proposition 2.2 (off-diagonal cylinder norms are null).** Let `X`, `Y` be disjoint nonempty clopens whose
union is proper. Then `E_(X,Y) = Sym(p_X, p_Y)` lies in `B_2`, and it has rank `0` under every Sylvester
matrix rank function on every ring receiving a unital map from `B_2`.

*Proof.*
- **Norms of commuting square-zero pairs:** suppose `u, v in R` satisfy `u^2 = v^2 = uv = vu = 0`. Then `1 + u`,
  `1 + v` and `1 + u + v = (1 + u)(1 + v)` lie in `Γ`, and `Σ_(x in {0, u, v, u+v}) (1 + x)^(⊗2) = Sym(u, v)`.
  So `Sym(u, v)` lies in `B_2`.
- **Setup:** take `X = [00]`, `Y = [01]`, `X' = [10]`, `Y' = [11]`, and split `X = X_0 ⊔ X_1`,
  `Y = Y_0 ⊔ Y_1`. Put
  - `S_(ab) = Sym(u_(X_a X'), u_(Y_b Y'))`;
  - `T_(ab) = Sym(u_(X' X_a), u_(Y' Y_b))`.
  All four sets involved are pairwise disjoint, so these lie in `B_2`.
- **Products:** `Sym(u, v) Sym(u', v') = Sym(uu', vv') + Sym(uv', vu')`, so
  - `T_(ab) S_(cd) = [a = c][b = d] Sym(p_(X'), p_(Y'))`;
  - `S_(ab) T_(ab) = Sym(p_(X_a), p_(Y_b)) = E_(ab)`.
  The cross terms vanish because they compose partial isometries between disjoint sets. No scalar `2`
  appears, because the two slots carry different sets.
- **Rank:** the `E_(ab)` are orthogonal idempotents below `E = Sym(p_X, p_Y)`, and each has rank at least
  `rk Sym(p_(X'), p_(Y'))`. Let `g in V` swap the first letter. Then
  `Δ_2(g) Sym(p_(X'), p_(Y')) Δ_2(g)^-1 = E`, so `rk E >= 4 rk E` and `rk E = 0`.
- **All pairs:** `V` acts transitively on ordered pairs of disjoint nonempty clopens with nonempty complement
  of the union (standard). Conjugation carries the model pair to every such pair. ∎

**Corollary 2.3 (diagonal localization).** Let `rk` be a Sylvester matrix rank function on a ring receiving
`B_2`, and let `P = (A_1, ..., A_m)` be a clopen partition with `m >= 3`.
1. **Norm idempotents:** `O_P = Σ_(i<j) Sym(p_(A_i), p_(A_j))` is a null idempotent, and
   `Q_P = 1 - O_P = Σ_i p_(A_i)^(⊗2)` lies in `B_2` with `rk Q_P = 1`.
2. **Localization:** `rk z = rk(Q_P z Q_P)` for every `z in B_2`. Here
   `Q_P Sym(a, b) Q_P = Σ_(i,j) Sym(p_(A_i) a p_(A_j), p_(A_i) b p_(A_j))`.
3. **Positivity:** `rk` is positive on some element of `B_2 ∩ N`. Otherwise it descends through Lemma 2.1
   to `R`, which has no rank function.

So a binary tensor-square rank function, if one exists, is carried by diagonal-block norm elements
`Sym(p_i a p_j, p_i b p_j)` at every scale.

**Theorem 2.4 (the defect is off-diagonal, so it is null).** Every Sylvester matrix rank function on a ring
receiving a unital map from `B_2` kills `Δ_2(D)`. So every Sylvester matrix rank function on `F_2[R^x]` that
factors through `Δ_2` is the augmentation rank.

*Proof.*
- **The defect:** `Δ_2(D) = Δ_2(N_23) Δ_2(N_12) = e_23 ⊗ e_12 + e_12 ⊗ e_23` ([SG] Section 3.4).
- **Left support:** its left support is off-diagonal, since `e_23 = p_[10] e_23` and `e_12 = p_[0] e_12`. So
  `Sym(p_[10], p_[0]) · Δ_2(D) = e_23 ⊗ e_12 + e_12 ⊗ e_23 = Δ_2(D)`, because the cross products
  `p_[10] e_12` and `p_[0] e_23` vanish.
- **Rank:** `[0]` and `[10]` are disjoint and their union misses `[11]`, so Proposition 2.2 gives
  `rk Sym(p_[10], p_[0]) = 0` and hence `rk Δ_2(D) = 0`.
- **Pullback:** a rank function on the receiving ring pulls back along `Δ_2` to a Sylvester matrix rank
  function on `F_2[R^x]` with `rk(D) = 0`. By [SG] Theorem 1 it is `rk_ε`. ∎

**Remarks.**
- **The handle is dead at degree two:** diagonal tensor squares over `F_2` can never give the detecting rank
  function that `binary-leavitt-units-carry-nonaugmentation-rank-function` asks for, whatever `W` and
  whatever normalization. The same argument works in every characteristic. In odd characteristic, Theorem 1
  already gives more.
- **Degree `n >= 3` in characteristic two is open.**
  - Why the argument stops: `Δ_n(D)` contains terms such as `e_23 ⊗ e_12 ⊗ 1`. Splitting the idle slot
    `1 = p_[0] + p_[10] + p_[11]` produces supports with a repeated set, for example
    `p_[10] ⊗ p_[0] ⊗ p_[10]`.
  - Why Proposition 2.2 doesn't cover them: nulling those with norms has to symmetrize two slots carrying
    the same set. That brings back the scalar `2`.
- **Whether `B_2` carries a rank function at all:** still open. By Theorem 2.4 such a function would satisfy
  `rk_B(x) = [ε(x) != 0]`, so it exists iff `ker Δ_2 ⊆ ker ε`.
