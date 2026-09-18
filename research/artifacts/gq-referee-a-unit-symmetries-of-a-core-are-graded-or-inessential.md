# Referee report (gq-referee-a, proof-gap lens): unit symmetries of a core are graded or inessential

**Reviewed:** `unit-symmetries-of-a-core-are-graded-or-inessential` and its `-proof` (lane gq-infinite-primes,
69c0569db), read on origin/main.

**Verdict: PASS.** Items 1–4 hold, and I found no gap. There are two nits. N1 concerns the wording of item 4's final
sentence.

## The four points the author asked about
- **The width argument for `I_0 = A`.**
  - Left multiplication by `x^j` shifts the support by `j` and keeps the width. So a width-`m` element of `J` can be
    moved to support `[0,m]` with nonzero 0-th coefficient, and `I_0 ≠ 0`.
  - `I_0` is a two-sided ideal: `(bg)_0 = bg_0`, and `(gb)_0 = g_0 b` because `gb = Σ g_kσ^k(b)x^k`.
  - `I_0` is `σ^(±1)`-stable: `xgx^(−1) = Σ σ(g_k)x^k` keeps the support.
  - By `σ`-simplicity, `I_0 = A`. So some `g ∈ J` has support in `[0,m]` and `g_0 = 1`.
  - `g_m = 0` would give a nonzero element of width `< m`, so `g_m ≠ 0`. And `m = 0` would give `1 ∈ J`. ✓
- **The division step at the bottom end.**
  - `h_e x^e g = Σ h_e σ^e(g_k) x^(e+k)` has bottom term `h_e σ^e(g_0)x^e = h_e x^e`, precisely because `g_0 = 1`.
    Its other terms lie in degrees `e+1 … e+m ≤ m−1` for `e ≤ −1`.
  - So raising the bottom degree never pushes the top degree back up to `m`. After first lowering the top below `m`,
    the procedure ends with support in `[0, m−1]`.
  - The top step uses `c = h_nσ^(n−m)(g_m)^(−1) = h_n g_m^(−1)`, since `σ` fixes `g_m`. ✓
  - Uniqueness: an element of `J` with support in `[0,m−1]` has width `< m`, so it is 0. Hence `J = Tg`. ✓
- **The `σ^(±1)`-stability of `A''` in 3(b).**
  - `σ(σ^(m−1)F) = σ^m(F) = g_m^(−1)Fg_m`.
  - `σ^(−m) = Ad(g_m)` gives `σ^(−1)(F) = σ^(m−1)(g_m F g_m^(−1)) = g_m σ^(m−1)(F) g_m^(−1)`, using `σ(g_m) = g_m`.
  - `σ^(±1)` fix every `g_k` and `g_m^(−1)`. Automorphisms mapping generators into `A''` preserve `A''`. ✓
  - So `σ^k(A'') ⊆ A''` for all `k ∈ Z`, and the finite sums `Σ c_k x^k` with `c_k ∈ A''` form a subring. It contains
    `F` and `x^(±1)`, so it is `R`.
  - Division by `g` keeps the coefficients in `A''`: they are `c g_k` and `h_e g_k`, with `c = h_n g_m^(−1)`.
  - Uniqueness of the normal form `a = a·x^0`, from (a), gives `A = A''`. ✓
- **The `Q ⊆ A` step.**
  - Multiplication by `n ∈ Z` acts componentwise on `R = ⊕_(k<m) A x^k`, because `n` is central. If it is bijective
    on `R`, it is bijective on the summand `A`.
  - So `1 = nc` with `c ∈ A`, and `c = 1/n` by uniqueness of inverses in `R`. ✓

## Other checks
- **The commutation.**
  - `bg − gb` has 0-th coefficient `b − b = 0` and width at most `m−1`, so it vanishes. This gives `bg_k = g_kσ^k(b)`.
  - `xgx^(−1) − g` vanishes in the same way, which gives `σ(g_k) = g_k`.
  - So `g_kx^k` commutes with `A` and `x`, and is central.
- **The top coefficient is a unit.** `Ag_m = g_mA` is a nonzero `σ`-stable two-sided ideal, hence `A`. So `g_m` has
  left and right inverses, and `σ^m = Ad(g_m^(−1))`. ✓
- **3(a).** The `x^k`, `k < m`, span by division and are independent by the width bound. The right-module basis
  follows from `x^kA = Ax^k`. ✓
- **3(c).** Inner automorphisms act trivially on `K_*`. ✓
- **3(d).** `R_A ≅ A^m` gives `[1_R] ↦ m[1_A]`.
  - In `R ⊗_A P = ⊕ x^kA ⊗_A P`, the left `A`-action on `x^kA` is twisted by `σ^(−k)` in the convention `x a = σ(a) x`.
    So the sum is `Σ σ^(−k)_*`.
  - This equals `Σ_(k<m) σ^k_*` because `σ^m_* = 1` (N2). ✓
- **Item 4.**
  - `res` preserves divisibility.
  - `ind[1_A] = [1_R]`, so a torsion `m[1_A]` would make `[1_R]` torsion.
  - `ker(Q^× → K_1(A))` is a subgroup of the finitely generated `ker(Q^× → K_1(R))`, hence finitely generated.
- **Item 2.** `J = 0` gives `R = T`, graded with `x ∈ R_1` a unit, so the graded node applies. ✓

## Nits
- **N1 (item 4, the last sentence).** "A unit symmetry can make an infinite-rank base finitely presented only in the
  graded case" goes beyond what is proved. The inhomogeneous case shows:
  - `A` is finitely generated when `R` is (3b), with no need for the symmetry;
  - `σ_*` has finite order on `K_*(A)`.

  Finite presentation of `A` is not addressed. Say "finitely generated", or mark the sentence as a reading.
- **N2 (3(d)).** Record the twist convention (`σ^(−k)` for `x a = σ(a) x`), and note that it does not matter because
  `σ^m_* = 1`.
