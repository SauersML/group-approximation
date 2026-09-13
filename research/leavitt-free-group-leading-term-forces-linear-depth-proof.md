---
rg: 2
id: leavitt-free-group-leading-term-forces-linear-depth-proof
kind: route
title: Bi-invariant orders make leading terms multiplicative, and a comparable leading pair containing its periodic point never dies
target: leavitt-free-group-leading-term-forces-linear-depth
requires: []
artifacts: [research/artifacts/leavitt-unit-depth-growth-lemmas-2026-09-13.md]
---

The full proof is Section 1 of `research/artifacts/leavitt-unit-depth-growth-lemmas-2026-09-13.md`
(Lemmas 1 and 2, Proposition 3).

1. **Grading.** The relations `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1` are homogeneous for
   `deg s_i = x_i`, `deg t_i = x_i^(-1)`, and normal-form monomials are homogeneous. If `x in R_N` and
   `x_g != 0`, then `|g| <= 2N`.
2. **Leading term.** For a bi-invariant order, `h_i <= g` gives `h_1 ... h_m <= g^m`, with equality only if
   every `h_i = g`. So `(x^m)_(g^m) = (x_g)^m`.
3. **Persistence.**
   - If `μ = νγ`, then `(s_μ 1_E t_ν)^m = s_ν 1_(E_m) s_γ^m t_ν`, where `E_m = γE ∩ ... ∩ γ^m E`.
   - `E_m` is nonempty iff `w, γw, ..., γ^(m-1)w` lie in `E` for some `w`. This holds for all `m` iff
     `γ^∞` is in `E`, since `E` is clopen.
   - The case `ν = μγ` follows through the anti-automorphism `s_μ t_ν -> s_ν t_μ`.
   - If `μ` and `ν` are incomparable, then `t_ν s_μ = 0`.
4. **Conclusion.**
   - Under the hypotheses, `g^m` lies in the support of `u^(km)` for all `m`.
   - Also `|g^m| >= m` for `g != 1`. By step 1, `ell(u^(km)) >= m/2`.
   - `max(ell(u^n), ell(u^-n))` is subadditive in `n`, so `lambda(u) >= 1/(2k)`. ∎
