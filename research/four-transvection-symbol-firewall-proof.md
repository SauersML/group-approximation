---
rg: 2
id: four-transvection-symbol-firewall-proof
kind: route
title: The code-(0,1) frame, the Jacobson symbol, and a character from eventually-zero sequences
target: four-transvection-units-have-a-weakly-finite-symbol-image
requires: []
artifacts:
  - research/artifacts/four-transvection-escape-set-2026-09-12.md
---
Artifact Sections 2 and 3 (Theorem 2.1, Lemma 2.2, Propositions 3.2 and 3.3). Held OPEN until `w4-vf-gate`
re-derives it.
1. **Frame** (Theorem 2.1(a), (b)). `Φ(s_σ t_κ) = s_(σ') t_(κ') e_(σ_1 κ_1)`. The span contains `M_2(F_3)`, `s_0 I`
   and `t_0 I`, and `-I` lies in `<E_01(1), E_10(1)> = SL_2(F_3)`. Injectivity of the Jacobson algebra into `T` is the
   normal-form basis of Alahmedi–Alsulami–Jain–Zelmanov.
2. **Symbol** (Theorem 2.1(c), (d), Lemma 2.2). The kernel of `T -> F_3[ζ, ζ^(-1)]` is spanned by the matrix units
   `s_0^a s_1 t_1 t_0^b`. The image contains `h = diag(ζ^(-1), ζ)`, hence all elementary matrices, and `E_2 = SL_2`
   over this Euclidean ring. A unital algebra map into a weakly finite algebra sends `ε_-` to `1`.
3. **Five transvections** (Proposition 3.3). With `Φ(T) = E_ij(λm)`, the span is `M_2(F_3<s_0, t_0, m>)`. On
   `F_3[Ω]`, `Ω` the eventually-`0` sequences, one of three things gives the character: the line through `e_(0^∞)`,
   the quotient by the other basis vectors, or the symbol at `ζ = 1`.
4. **Frames and six transvections** (Propositions 3.2 and 3.3(d)). The six roots of either code have `Φ`-entries
   `t_0`, `s_0`, `t_1`, `s_1`, `s_0 t_1` and `s_1 t_0`, and only the first two lie in `T`. `S6` adds `s_1` and `t_1`,
   and `R` is simple and not directly finite.

*Verified independently by `w4-vf-gate` (2026-09-12), Sections 36.2–36.3 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
