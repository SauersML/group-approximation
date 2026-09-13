---
rg: 2
id: leavitt-square-chen-line-action-proof
kind: route
title: Realize GL_m(F_p) by product matrix units, then drive stabilizer germ columns over F_p[s_1^±, s_2^±] to the base vector by four elementary moves through a fresh point
target: leavitt-square-units-act-two-transitively-on-chen-lines
requires:
  - leavitt-algebras-l-k-1-n-are-simple
  - odd-leavitt-unit-groups-mod-scalars-are-fp-simple
---

**Notation.** As in the target.
- Unprimed letters `s_i, t_i` mean `s_i ⊗ 1, t_i ⊗ 1`, and primed letters mean
  `1 ⊗ s_i, 1 ⊗ t_i`. Primed and unprimed letters commute.
- For a word `α = a_1...a_k` put `s_α = s_(a_1)...s_(a_k)`, `t_α = t_(a_k)...t_(a_1)`. Then:
  - `t_α s_β = δ_αβ` for words of one length;
  - `t_β s_α = 0` for incomparable words;
  - `t_α s_(αζ) = s_ζ`.
- `[0]`, `[1]` are the cones of `D` of points starting with `0`, `1`.
- `Λ = K[s_1^±, s_2^±]`, `ev: Λ → K` is evaluation at `(1,1)`, and `I = ker ev = (s_1 − 1, s_2 − 1)`.

**0. Faithful module and monomial independence.**
- *`π` injective.* The representation `π: L → End(W)` is nonzero and `L` is simple
  (`leavitt-algebras-l-k-1-n-are-simple`), so `π` is injective.
- *`π_2` injective.* `π_2 = π ⊗ π` factors as `L ⊗ L → End(W) ⊗ End(W) → End(W ⊗ W)`.
  - The first map is injective, being a tensor product of injective maps over a field.
  - For the second, let `Σ A_i ⊗ B_i ↦ 0` with the `A_i` linearly independent. For all
    `v, w` and every functional `φ` on `W`, `Σ φ(B_i w) A_i v = 0`. So `Σ φ(B_i w) A_i = 0`,
    each `φ(B_i w) = 0`, and each `B_i = 0`.
- *Independence.* Let `(γ_j, γ'_j)` be distinct pairs of words. Take `τ = 1^M 0^∞` with `M`
  above every word length. Then `π_2(s_(γ_j) s'_(γ'_j)) δ_(τ,τ) = δ_(γ_j τ, γ'_j τ)`, and
  these points are distinct because the last `1` of `γτ` sits at position `|γ| + M`. So
  the monomials `s_γ s'_γ'` are linearly independent.

**1. Faithful modulo scalars.** If `u ∈ U` fixes every line, `π_2(u) = λ·id = π_2(λ)`, so
`u = λ ∈ K^×`. Conversely `K^×` fixes every line.

**2. 2-transitive.**
- *Setup.* Let `([v_1],[w_1])`, `([v_2],[w_2])` be pairs of distinct lines. Let `Φ` be the
  union of the supports and `m = |Φ| >= 2`.
- *Common length.* Choose `N` beyond the last `1` of every coordinate of every point. Write
  `x = (p_x 0^∞, q_x 0^∞)` with `|p_x| = |q_x| = N`, so `x ↦ (p_x, q_x)` is injective.
- *Matrix units.* `e_xy = s_(p_x) t_(p_y) s'_(q_x) t'_(q_y)` satisfy
  `e_xy e_x'y' = δ_yx' e_xy'`, and `π_2(e_xy) δ_z = δ_yz δ_x` for `z ∈ Φ`.
- *The units.* With `P_Φ = Σ e_xx` and `A ∈ GL_m(K)`, `u_A = (1 − P_Φ) + Σ A_xy e_xy` is a
  unit with inverse `u_(A^-1)`. It acts by `A` on `span δ_Φ`, since `π_2(1 − P_Φ) δ_z = 0`.
- *Conclusion.* Some `u_A` sends `(v_1, w_1)` to `(v_2, w_2)`.

**3. Germ columns.** Put `F = ⊕_(x ∈ D×D) Λ e_x`.
- *Star-free form.* Let `u = Σ λ s_α t_β s'_α' t'_β'` and `q = (c0^∞, d0^∞)`. For `k, k'`
  at least the longest `t`-word of `u`, `u s_(c0^k) s'_(d0^k')` is a combination
  `Σ μ_(γγ') s_γ s'_γ'`.
- *Definition.* Put `col_q(u) = Σ μ_(γγ') s_1^(|γ|−|c|−k) s_2^(|γ'|−|d|−k') e_(γ0^∞, γ'0^∞)`.
  It is well defined by 0. It does not depend on `k, k'`, because raising `k` appends `0`
  to every `γ`.
- *The matrix `M(u)`.* Let `M(u)` be the `Λ`-linear map with `M(u) e_q = col_q(u)`.
- *(a) Evaluation.* `π_2(u) δ_q = Σ_x ev(col_q(u)_x) δ_x`.
- *(b) Multiplicativity.* `col_q(uv) = M(u) col_q(v)`, so `M(uv) = M(u) M(v)`.
  - Choose `k, k'` so large that every monomial `s_γ s'_γ'` of `v s_(c0^k) s'_(d0^k')` has
    `|γ|, |γ'|` at least the longest `t`-word of `u`.
  - Writing `γ = e0^j` with `x = (e0^∞, e'0^∞)`, the monomials of `u s_γ s'_γ'` give
    `col_x(u)` with exponent offsets `−|e| − j` and `−|e'| − j'`.
  - Multiplying by `s_1^(|γ|−|c|−k) s_2^(|γ'|−|d|−k')` gives exactly the exponents of
    `col_q(uv)`.
- *(c) Unimodular.* If `u ∈ U`, the entries of `c = col_b(u)` generate `Λ`: the
  `b`-entry of `M(u^-1) c = col_b(1) = e_b` is a finite sum `Σ_x col_x(u^-1)_b c_x = 1`.
- *(d) Trivial germ.* `col_b(u) = e_b` iff `u s_(0^k) s'_(0^k) = s_(0^k) s'_(0^k)` for some
  `k`, by 0.

**4. The subgroups.**
- *`H`.* For `u ∈ H` and `c = col_b(u)`, (a) gives `ev(c_b) = 1` and `ev(c_x) = 0` for
  `x ≠ b`. So `c_b − 1 ∈ I` and `c_x ∈ I` for `x ≠ b`.
- *`H_k`.* `H_k = {u : u s_(0^k) s'_(0^k) = s_(0^k) s'_(0^k)} ⊂ H`. With `ĝ = g ⊗ g`,
  `ĝ s_(0^k) s'_(0^k) = s_(0^(k+1)) s'_(0^(k+1))` for `k >= 1`. So `H_(k+1) = ĝ H_k ĝ^-1`,
  and `H^0 := {u ∈ H : col_b(u) = e_b} = ∪_k H_k ⊂ ⟨H_1, ĝ⟩` by 3(d).
- *The corner isomorphism.* `Y X = 1`, `X Y = 1 − P`, `P X = 0` and `Y P = 0`, by
  `t_1 s_0 = t_0 s_1 = t'_1 s'_0 = 0`.
- *`H_1 = N ⋊ Q`.* Since `u s_0 s'_0 = s_0 s'_0` iff `uP = P`, every `u ∈ H_1` has
  `u = (1 + P u (1−P) q')(P + q)`, with `q = (1−P) u (1−P)`, `q' = (1−P) u^-1 (1−P)` and
  `q q' = q' q = 1 − P`.
  - `Q = {P + X c Y : c ∈ U} ≅ U`, with inverse `P + X c^-1 Y`.
  - `N = {1 + s_0 s'_0 a Y : a ∈ R} ≅ (R, +)`. Here `P R (1−P) = s_0 s'_0 R Y`, and `a` is
    recovered as `t'_0 t_0 (·) X`.
  - A direct computation gives
    `(P + X c Y)(1 + s_0 s'_0 a Y)(P + X c^-1 Y) = 1 + s_0 s'_0 a c^-1 Y`.
- *`R` is spanned by `U`.* `S = span_K U` is a subalgebra, so it suffices that `L ⊗ 1`,
  `1 ⊗ L ⊂ S`. In one factor:
  - for incomparable `α, β`, `1 + s_α t_β` is a unit, so `s_α t_β ∈ S`;
  - `P_0 = (s_0 t_1)(s_1 t_0)` and `P_00 = (s_00 t_1)(s_1 t_00)` lie in `S`;
  - `g^-1 P_00 = s_0 t_00` and `s_1 t_01 ∈ S` give `t_0 = s_0 t_00 + s_1 t_01 ∈ S`;
  - `g P_0 = s_00 t_0` gives `s_0 = s_00 t_0 + s_01 t_1 ∈ S`;
  - the index swap `0 ↔ 1` gives `s_1, t_1`.
- *`H_1` is finitely generated.* `N` is generated by the `Q`-conjugates of
  `1 + s_0 s'_0 Y`. `U` is a central extension of the finite group `K^×` by the finitely
  presented group `G` (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`). So
  `H_1 = ⟨Q, 1 + s_0 s'_0 Y⟩` is finitely generated.

**5. Moves.** Let `u ∈ H` with column `c`. Left multiplication by `y ∈ H` replaces `c` by
`M(y) c`. Below, `supp c` is the set of points with nonzero entry.
- **(E1)** *Distinct `x, x' ≠ b`, `λ ∈ K`, `m ∈ Z^2`: add `λ s_1^(m_1) s_2^(m_2) c_x` to
  `c_x'`, within `H^0`.*
  - *Choice.* Write `x = (b_1 0^∞, b_2 0^∞)`, `x' = (a_1 0^∞, a_2 0^∞)`,
    `β = b_1 0^i`, `β' = b_2 0^i'`, `α = a_1 0^j`, `α' = a_2 0^j'`. Take `i, i'` so large
    that `x` is the only point of `supp c` in `[β] × [β']`, and that in some coordinate
    where `x, x'` differ the two words are incomparable. Then choose `j, j'` for the
    exponents.
  - *Unit.* `e = 1 + λ s_α t_β s'_α' t'_β'` is a unit: the tensor factor in that coordinate
    squares to `0`.
  - *In `H^0`.* Some coordinate of `x` is not `0^∞`, so `t_β s_(0^k) t'_β' s'_(0^k) = 0` for
    large `k`, and `e ∈ H_k`.
  - *Effect.* `col_x(e) = e_x + λ s_1^(|α|−|β|) s_2^(|α'|−|β'|) e_x'`, and `col_y(e) = e_y` for
    the other `y ∈ supp c`.
- **(E2)** *The same with `x' = b`,* using `α = 0^j`, `α' = 0^j'` and incomparability in a
  coordinate where `x` is not `0^∞`.
- **(W1)** *For `μ ∈ Λ`: add `μ (s_1 − 1) c_b` to `c_(p_1)`, `p_1 = (10^∞, 0^∞)`, provided
  `supp c` meets `[0] × D` only in `b`.*
  - *The nilpotent.* `n = s_10 t_0 − s_10 t_00` has `n^2 = 0`, and `(1 + λn) δ = δ`.
    - `col_b(1 + λn) = e_b + λ(s_1 − 1) e_(p_1)`, since `n s_(0^k) = s_(10^k) − s_(10^(k−1))`.
    - `col_x(1 + λn) = e_x` for `x ∈ [1] × D`, since `n s_(1γ) = 0`.
  - *`r`.* `r = s_0 t_0 + s_100 t_10 + s_101 t_110 + s_11 t_111`. It lies in `H_1`, fixes
    `[0] × D` with germ `1`, preserves `[1] × D`, and has germ `s_1` at `p_1`.
  - *`z`.* `z = s_0 t_0 + s_1 t_1 g'`, a unit with inverse `s_0 t_0 + s_1 t_1 g'^-1`. It
    lies in `H_1`, fixes `[0] × D` with germ `1`, preserves `[1] × D`, and has germ `s_2`
    at `p_1`.
  - *The move.* Put `h = r^(m_1) z^(m_2)` and `y = h^-1 (1 + λn) h`.
    - Under the proviso, `M(h) c` is supported in `{b} ∪ [1] × D` with `b`-entry `c_b`.
    - Applying `1 + λn` adds `λ(s_1 − 1) c_b e_(p_1)`.
    - `M(h^-1)` restores `c` and multiplies that term by `s_1^(−m_1) s_2^(−m_2)`.

    Products of such `y` give any `μ`, and `supp c` never gains a point of `[0] × D`.
- **(W2)** *Symmetrically: add `μ(s_2 − 1) c_b` to `c_(p_2)`, `p_2 = (0^∞, 10^∞)`, provided
  `supp c` meets `D × [0]` only in `b`.* Use `w_2`, `1 ⊗ r` and `s'_0 t'_0 + s'_1 t'_1 g`.
- **(T)** *For `x ∈ [1] × [1]` and `t ∈ I`: add `t c_b` to `c_x`, provided
  `supp c ⊂ {b} ∪ [1] × [1]`.*
  - Write `t = μ_1 (s_1 − 1) + μ_2 (s_2 − 1)`.
  - Apply W1(`μ_1`), then E1 from `p_1` to `x` with coefficient `1`, then W1(`−μ_1`).
  - Then apply W2(`μ_2`), E1 from `p_2` to `x`, and W2(`−μ_2`).
  - *Provisos hold at each step.* `p_1 ∈ [1] × [0]` never meets `[0] × D`. `p_2 ∈ [0] × [1]`
    never meets `D × [0]`. When W2(`μ_2`) runs, `c_(p_1) = 0` again.

**6. The reduction.** Let `u ∈ H` and `c = col_b(u)`. Each move is invertible, so the
entries keep generating `Λ`. Non-base entries stay in `I` and `c_b − 1` stays in `I`.
1. *Clear.* By E1, copy each `x ∈ supp c ∖ {b}` to a fresh point of `[1] × [1]` and
   subtract it back. Now `supp c ⊂ {b} ∪ [1] × [1]`.
2. *Fresh row.* Put `a = c_b`, choose `v_x ∈ Λ` with `Σ_x v_x c_x = 1`, and pick a fresh
   `y ∈ [1] × [1]`.
   - Apply T at `y` with `t = (1 − a) v_b ∈ I`.
   - Apply E1 from each `x ∈ supp c ∖ {b, y}` to `y` with coefficient `(1 − a) v_x`.
   - Now `c_y = 1 − a`.
3. *Base.* E2 from `y` to `b` with coefficient `1` makes `c_b = 1`.
4. *Finish.* For each non-base `x ∈ supp c`, apply T at `x` with `t = −c_x ∈ I`.

Now `c = e_b`. So `y' u ∈ H^0` with `y' ∈ ⟨H_1, ĝ, w_1, w_2⟩`, since E1 and E2 lie in
`H^0 ⊂ ⟨H_1, ĝ⟩` and W1, W2 in `⟨H_1, w_1, w_2⟩`. Hence
`H = ⟨H_1, ĝ, w_1, w_2⟩`, which is finitely generated by 4.

**7. Line stabilizers.**
- *In `U`.* `Stab_U([δ]) = K^× H` with `K^× ∩ H = 1`.
- *In `G`.* The stabilizer is `≅ H`.
- *Every line.* By 2, every line stabilizer is conjugate to this one. `∎`

**Remark.** The four-step reduction in 6 uses only unimodularity and `I = ker ev`. It
applies verbatim to the one-factor algebra, where it replaces the Euclidean algorithm of
`leavitt-chen-module-line-action-proof`.
