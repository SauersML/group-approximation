# Referee report (gq-referee-a, proof-gap lens): the harmonic Cuntz ring C_h

**Reviewed:** `harmonic-cuntz-ring-is-purely-infinite-simple` with its route `-proof` (lane
gq-cuntz-cstar, f07d0119c), read on origin/main.

**Verdict: PASS.** No gaps found.

- **Part 1 (`Q ⊂ C_h`).** Correct. Evaluating `t_0 t_1^k m_η s_1^k s_0` pointwise gives
  `u(w) · η(1^k 0 w) = u(w)/(k+1)`.
- **Part 2 (normal form).** Correct.
  - The algebra `𝒜` refines levelwise, since `k(0z) = 0` and `k(1z) = 1 + k(z)`. It is closed under
    `f_α` and `f^α`.
  - (W2) holds pointwise. The product formula for `s_α m_f t_β · s_γ m_g t_δ` follows from (W1) and
    (W2), so the span `S` is a subring with `C_h ⊆ S`.
- **(C3) independence.** Correct.
  - Take a point `w` that is not eventually periodic. Its shifts are distinct, so applied to the
    indicator of `σ^{|μ|}w`, only the `μ` term survives at `w`.
  - Given any `z` that is not eventually periodic, `w = μz` gives `g_μ(z) = 0`, so `g_μ = 0` by (A6).
- **Grading.** Correct. After lengthening to one right length `L`, the words `a_d s_β` of different
  degrees have different lengths. So (C3) applies, and `Σ_β s_β t_β = 1` recovers `a_d`.
- **Part 3 (two-sided division).** Correct.
  - Cutting `b = a s_β` at a longest word gives `c = m_{g_0} + Σ t_{τ_j} m_{h_j}` with every `τ_j`
    nonempty.
  - (A5) gives `δ_0` with `(g_0)_{δ_0} ≡ λ ≠ 0`.
  - The words `δ_0 ε` with `|ε| = e` and `2^e >` the number of `j` include one that is a prefix of
    no `τ_j^∞`.
  - So `t_δ c s_δ = λ`, since `t_{τ_jδ} s_δ = 0` by (W4).
  - The witnesses `λ^{-1} t_δ t_{μ*}` and `s_β s_δ` lie in `C_h`.
- **Part 4 (centre).** Correct.
  - Components are central, because the generators are homogeneous and `S` is graded.
  - For `d ≠ 0`, `z_d = t_γ z_d s_γ`. Each term becomes `t_{γ'} s_{γ''} m_{f_{γ''}}`, which is nonzero
    only when `γ'` (or `γ''`) is a prefix of `θ^∞`. The choice `γ = πε` avoids the finitely many
    periodic prefixes, so `z_d = 0`.
  - For degree 0, commuting with the projections `s_α t_α` kills the off-diagonal blocks. So
    `z_0 = m_f`, and `f(iz) = f(z)` forces `f ≡ r_{0^n}(0)`.
- **Parts 5 and 6.** Correct and standard. Zero-testing reduces through (C3) to finitely many
  rational-function vanishing tests.
