
## 36. w7-escape-set (45282c2142)

Sources:
- Artifact `four-transvection-escape-set-2026-09-12.md` (blob `cb33ab0f`), Sections 0–5.
- The claims `four-transvection-set-escapes-depth-monotone-units` (blob `1339c38f`),
  `four-transvection-units-have-a-weakly-finite-symbol-image` (blob `fcc45de7`) and
  `depth-monotone-units-carry-weakly-finite-nonzero-defect` (blob `9e696bc5`).
- The OPEN claim `four-transvections-and-x23-force-defect-vanishing` (blob `1f3ccdee`).
- The routes `four-transvection-escape-proof` (blob `384f5613`), `four-transvection-symbol-firewall-proof` (blob
  `85927ae8`), `depth-monotone-tensor-cube-defect-proof` (blob `06b2138e`) and
  `summand-obstruction-from-four-transvection-defect` (blob `0aff6a1e`).
- The entries on `ternary-leavitt-units-have-no-weakly-finite-representation` (blob `a274ca7f`) and
  `ternary-weakly-finite-representations-kill-two-root-defect` (blob `99a42c33`).

**Verdict: PASS on Sections 1–4, the three claim displays and the three proof routes.** The OPEN claim is correctly
OPEN, and `summand-obstruction-from-four-transvection-defect` is a valid implication. There are three wording
advisories (36.5) and no correction.

It is decision-level for the ternary counterexample route:
- the defect form (iv) is firewalled on every sofic subgroup of `G` containing `z` and the standard frame, and
  explicitly, without soficity, on `H^ω_≤` with `ω(0) <= ω(1)`;
- so a proof of `ternary-weakly-finite-representations-kill-two-root-defect` must use relations that hold in none
  of them;
- the smallest known input for `ternary-anti-central-summand-has-no-weakly-finite-image` is `Γ_5 = <S4, x_23(1)>`,
  which is OPEN, and soficity of `Γ_5` would refute it.

Every model built here is nontrivial, with `z -> -1` and `D != 0`. Nothing proves that rank models are trivial.
Gottschalk on `G`, the gate and Plan 1 stay OPEN.

### 36.1 The escape invariant (Section 1). PASS

- **Theorem 1.1, recomputed.** Put `A = s_0 t_1`, `A' = s_1 t_0`, `B = s_1 t_00` and `B' = s_00 t_1`, the four
  transvections minus `1`.
  - `B'A' = s_00 t_0`, `A'A = s_1 t_1` and `AB = s_0 t_00`.
  - `x = s_00 t_0 + s_1 t_1` and `y = s_0 t_00 + s_1 t_1` give `yx = s_0 t_0 + s_1 t_1 = 1`, because
    `t_00 s_1 = 0 = t_1 s_00`.
  - `xy = s_00 t_00 + s_1 t_1 = 1 − s_01 t_01`.
  - A conjugate of `<S4>` inside `H^ω_≤` would put the conjugated pair inside the stably finite `R^ω_≤`
    (`depth-monotone-leavitt-subalgebras-are-stably-finite`). The `≥` side is the same.
- **Remark 1.2, recomputed.** With `ω(0) = a` and `ω(1) = b`, the roots compare `a : b` (`A`), `b : a` (`A'`),
  `b : 2a` (`B`) and `2a : b` (`B'`).
  - `{A, A', B}` lies on the `≤` side and `{A, A', B'}` on the `≥` side, both with `a = b`.
  - `{A, B, B'}` lies on the `≤` side and `{A', B, B'}` on the `≥` side, both with `b = 2a`.
  - The inverses `1 − n` stay in each span.
- **Proposition 1.3.** It rests on Lemma 1.2 of `depth-monotone-leavitt-firewall-2026-09-12.md`, read at its lines
  66–72:
  - each `F_r` is finite-dimensional, `F_r ⊆ F_r'` for `r <= r'`, and `C = ∪_r F_r`;
  - `π(s_μ t_ν) F_r ⊆ F_r` when `ω(μ) <= ω(ν)` and `ω(μ) <= r`.

  So a finite combination of `≤` monomials preserves `F_r` for large `r` and is locally finite.
  - If `π(ugu^(-1))` is locally finite, so is `π(g) = π(u)^(-1) π(ugu^(-1)) π(u)`.
  - On the `≥` side, `(ugu^(-1))^* = (u^*)^(-1) g^* u^*` lies on the `≤` side.
- **Corollary 1.4, recomputed.** `x_0 = s_0 t_00 + s_10 t_01 + s_11 t_1`.
  - On `1_[1^n]` with `n >= 1`, only `s_11 t_1` contributes, and it gives `1_[1^(n+1)]`. So the orbit of `1_[1]`
    spans an infinite-dimensional space.
  - `x_0` is the element `00y -> 0y`, `01y -> 10y`, `1y -> 11y` of `V`, so `x_0^* = x_0^(-1)`.
  - An invertible locally finite operator maps each finite-dimensional invariant subspace bijectively onto itself,
    so its inverse is locally finite. Both sides fail for `x_0`.

### 36.2 The symbol image (Section 2). PASS

- **Theorem 2.1(a), recomputed.** For incomparable `σ = σ_1 σ'` and `κ = κ_1 κ'`, the formula
  `t_i s_σ t_κ s_j = δ_(i σ_1) δ_(j κ_1) s_(σ') t_(κ')` gives `Φ(S4) = {E_01(1), E_10(1), E_10(t_0), E_01(s_0)}`.
  - `e_10 (s_0 e_01) = s_0 e_11` and `(s_0 e_01) e_10 = s_0 e_00`, so `s_0 I` lies in the span, and likewise `t_0 I`.
    With `M_2(K)` this gives `M_2(T)`.
  - Conversely every generator and its inverse lies in `M_2(T)`.
  - `T = K<s_0, t_0>` is the Jacobson algebra, by the normal-form basis `s_0^a t_0^b`.
- **(b).** `E_01(1)` and `E_10(1)` generate `SL_2(F_3)`, which contains `−I`. So `z in <S4>`.
- **(c), recomputed.** Under `s_0 -> ζ`, `t_0 -> ζ^(-1)`:
  - `w(ζ) = E_01(ζ) E_10(−ζ^(-1)) E_01(ζ) = [[0, ζ], [−ζ^(-1), 0]]`, `w = w(1)`, and
    `w(ζ) w^(-1) = diag(ζ, ζ^(-1))`, the inverse of `h = diag(ζ^(-1), ζ)`;
  - conjugating `E_01(1)` and `E_01(ζ)` by `h^n` gives `E_01(ζ^(-2n))` and `E_01(ζ^(1-2n))`, so `E_01(p)` for every
    Laurent polynomial `p`, and conjugating by `w` gives `E_10(p)`;
  - `F_3[ζ, ζ^(-1)]` is Euclidean, so `E_2 = SL_2` and the image is `SL_2(F_3[ζ, ζ^(-1)])`, with `z -> −I`.
  - The kernel of `T -> F_3[ζ, ζ^(-1)]` is spanned by `s_0^a (1 − s_0 t_0) t_0^b = s_0^a s_1 t_1 t_0^b`.
- **(d) and Lemma 2.2.** A unital algebra map into a weakly finite algebra with `[z] -> −1` sends
  `ε_- = 2(1 − [z])` to `4 = 1`. So `ε_- F_3[<S4>]` maps unitally onto a nonzero weakly finite algebra. Conjugation
  gives an isomorphic group algebra.
