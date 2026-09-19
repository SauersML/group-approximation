---
rg: 2
id: leavitt-units-are-prefix-rigid-on-deep-cylinders-proof
kind: route
title: Compress by a deep cylinder to land in S + T, then kill the extreme graded components by one-sided injectivity and a dimension count at a finite matrix stage
target: leavitt-units-are-prefix-rigid-on-deep-cylinders
requires: []
---

Notation as in `leavitt-units-are-prefix-rigid-on-deep-cylinders`. `R` is `Z`-graded with `deg s_i = 1` and
`deg t_i = -1`. `R_d` is spanned by the `s_α t_β` with `|α| - |β| = d`.

## Step 0. Standard facts

- (a) `R_0 = ⋃_n A_n`, with `A_n = span{s_α t_β : |α| = |β| = n}`.
  - The `s_α t_β` are matrix units: `t_β s_γ = δ_(βγ)` for `|β| = |γ|`.
  - Their span is a nonzero image of the simple algebra `M_(2^n)(K)`, so `A_n ≅ M_(2^n)(K)`.
  - The unit of `A_n` is `Σ_(|α|=n) p_α = 1`.
  - `s_α t_β = s_(α0) t_(β0) + s_(α1) t_(β1)` gives `A_n ⊆ A_(n+1)`.
- (b) For `k >= 0` and `0 != σ = Σ_(|w|=k) λ_w s_w`, left multiplication by `σ` is injective on `R`.
  - Suppose `σ y = 0`, and pick `w_0` with `λ_(w_0) != 0`.
  - Then `0 = t_(w_0) σ y = λ_(w_0) y`, since `t_(w_0) s_w = δ_(w w_0)` for `|w| = k`.
- (b') Symmetrically, for `0 != τ = Σ_(|w|=k) μ_w t_w`, right multiplication by `τ` is injective. Multiply
  `y τ = 0` on the right by `s_(w_0)`.
- (c) For `x = Σ_i x_i` and `y = Σ_j y_j` with top degrees `i_1, j_1`, the degree `i_1 + j_1` component of `xy` is
  `x_(i_1) y_(j_1)`. The same holds for bottom degrees.

## Step 1. No homogeneous unit of nonzero degree

- Let `u ∈ R_A ∩ R^×`, and replace `u` by `u^(-1)` if needed so that `A >= 0`.
- **The inverse is homogeneous.** Write `u^(-1) = Σ_j w_j`. Then `Σ_j u w_j = 1 ∈ R_0` with `u w_j ∈ R_(A+j)`.
  So `u w_j = 0` for `j != -A`, and `w_j = 0` there because `u` is a unit.
- **`R_A = u R_0`.** Any `z ∈ R_A` is `u (u^(-1) z)`, and `u^(-1) z ∈ R_0`.
- **`R_A = ⊕_(|w|=A) s_w R_0`** as right `R_0`-modules.
  - A monomial `s_α t_β` of degree `A` has `|α| >= A`. With `α = wα'`, it equals `s_w (s_(α') t_β)`.
  - The sum is direct: apply `t_(w')`.
  - Each `y -> s_w y` is injective, with inverse `t_w ·`.
- So `R_0 ≅ R_A ≅ R_0^m` with `m = 2^A`.
- **Finite stage.** Such an isomorphism is given by a row `r ∈ R_0^(1×m)` and a column `c ∈ R_0^(m×1)` with
  `rc = 1` and `cr = I_m`. All `2m` entries lie in one `A_n`, and `A_n` contains the unit.
- Then `A_n ≅ A_n^m` as right `A_n`-modules. Comparing `K`-dimensions gives `4^n = m·4^n`, so `m = 1` and
  `A = 0`. ∎

## Step 2. Item 1: units in `S + T` are scalars

- Let `u ∈ (S + T) ∩ R^×` and `w = u^(-1)`.
- The components of `u` are: `u_d ∈ S_d = span{s_w : |w| = d}` for `d > 0`, `u_0 ∈ K`, and
  `u_d ∈ T_(-d) = span{t_w : |w| = -d}` for `d < 0`.
- Let `A >= a` be the top and bottom degrees of `u`, and `W >= W'` those of `w`.
- Since `uw = wu = 1 ∈ R_0`, any extreme component of `uw` or `wu` that is nonzero must sit in degree `0`.
- **Case `A > 0`, `a < 0`.**
  - By (b) and (c), the top component `u_A w_W` of `uw` is nonzero, so `A + W = 0`.
  - By (b') and (c), the bottom component `w_(W') u_a` of `wu` is nonzero, so `W' + a = 0`.
  - Then `W' = -a > 0 > -A = W`, contradicting `W' <= W`.
- **Case `A > 0`, `a >= 0`, so `u ∈ S`.**
  - The top of `uw` gives `A + W = 0`.
  - The bottom `u_a w_(W')` of `uw` is nonzero: `u_a ∈ S_a`, or `u_a ∈ K^×` if `a = 0`, and (b) applies. So
    `a + W' = 0`.
  - Then `-a = W' <= W = -A`, so `a = A` and `u` is homogeneous of degree `A > 0`. Step 1 rules this out.
- **Case `A <= 0`, `a < 0`, so `u ∈ T + K`.**
  - Use `wu = 1` and (b'). The top of `wu` is `w_W u_A`, which gives `W + A = 0`, and the bottom gives
    `W' + a = 0`.
  - As before `a = A < 0`, and Step 1 rules this out.
- **Case `A <= 0 <= a`.** Then `A = a = 0` and `u ∈ K^×`. ∎

## Step 3. Item 2: deep compressions

- Take a monomial `s_α t_β` of `x`, so `|β| <= N <= |v|`.
- `t_β s_v` is `s_(v'')` if `v = βv''`, and `0` otherwise.
- So `t_(v') s_α t_β s_v` is `0` or `t_(v') s_(αv'')`.
- For words `y, z`, the product `t_y s_z` is `t_(y')` if `y = zy'`, `s_(z')` if `z = yz'`, and `0` otherwise. So
  the product lies in `S + T`.
- **Case `v' = v` and `|v| >= N'`.**
  - Then `t_v s_α = t_(v_1)` if `v = αv_1`, and `0` otherwise.
  - `t_(v_1) t_β s_v = t_(βv_1) s_v`, where `|βv_1| = |v| + |β| - |α|`.
  - So the result is `s_w` or `t_w` with `|w| = ||β| - |α|| <= N`, or `0`. ∎

## Step 4. Item 3: prefix rigidity

- Put `σ = t_(v') u s_v` and `τ = t_v u^(-1) s_(v')`.
- `στ = t_(v') u p_v u^(-1) s_(v') = t_(v') p_(v') s_(v') = 1`.
- `τσ = t_v (u^(-1) p_(v') u) s_v = t_v p_v s_v = 1`.
- By Step 3, `σ ∈ S + T` (only `|v| >= N` is used). By Step 2, `σ = λ ∈ K^×`.
- Finally `u s_v = u p_v s_v = p_(v') u s_v = s_(v') σ = λ s_(v')`.
- If `v' = v`, then `u p_v = λ s_v t_v = λ p_v`. Over `F_2`, `λ = 1`. ∎

## Step 5. Item 4: block collapse

- Let `q = s_v e t_v ∈ Q`. Then `qRq = s_v eRe t_v`.
- `ψ_q : qRq -> eRe`, `y -> t_v y s_v`, is a unital isomorphism with inverse `z -> s_v z t_v`. It uses
  `t_v s_v = 1` and `ψ_q(q) = e`.
- `ψ_q(qaq) = e (t_v a s_v) e`, because `t_v q = e t_v` and `q s_v = s_v e`.
- `qa = aq` gives `qa = qaq`, so `I_q` is the kernel of `x -> e σ_a e`, `y -> e σ_c e` into `eRe`. Here
  `σ_a = t_v a s_v`.
- By Step 3, since `|v| >= N`, `σ_a` and `σ_c` lie in the finite set `W_N`, and `e` lies in the finite set of
  depth-`<= (M, M)` idempotents.
- So `I_q` takes finitely many values `I_1, ..., I_r`. `F_2[x^(±1), y^(±1)]` is a domain, and
  `I_1 ⋯ I_r ⊆ ⋂ I_j`. So `⋂ I_j = 0` forces some `I_j = 0`.
- If `e = 1`, Step 4 gives `qa = q = qc`, so `I_q ⊇ (x - 1, y - 1)`. Equality holds because the image `F_2 q` is
  nonzero. ∎
