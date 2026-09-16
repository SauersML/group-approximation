---
rg: 2
id: sl2-root-triangle-tensor-reps-iff-zero-holonomy-proof
kind: route
title: Compose the zero-holonomy map onto SL_2(q^2) with a twisted tensor module; for nonzero holonomy use the commutant argument, and when 2·hol = 0 compare the exact commutator scalars, which differ by a Frobenius power of s not in k
target: sl2-root-triangle-tensor-reps-iff-zero-holonomy
requires: [sl2-root-triangle-tensor-vertex-reps-force-2hol-zero, sl2-root-triangle-2dim-iff-zero-frobenius-holonomy, sl2-root-triangle-char2-frobenius-spectrum-transport, kazhdan-hyperbolic-sl2-root-triangles]
---

Notation as in the target and in `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero` and its route. We use:
- the coefficient operators `X_c^p` and their uniqueness;
- the tensor-model operators `x_c, y_c`;
- the edge-23 operators `z_d = X^v_d` at `A_2`.

In characteristic 2, `[E_12, E_21] = E_11 - E_22 = 1` in `End(K^2)`.

**Step 1. `hol = 0` gives a tensor-type representation.** By `sl2-root-triangle-2dim-iff-zero-frobenius-holonomy`
there are `g_i ∈ GL_2(F)` and exponents `b_i` with:
- `ρ_i = conj_{g_i} ∘ Frob^{b_i}` on `A_i`;
- `b_3 = 0`;
- `ρ_1, ρ_2` defined on `SL_2(k) ⊂ SL_2(F)`.

These glue to a homomorphism `π: Λ -> SL_2(F)`. Fix a nonempty `T_3 ⊆ Z/2f` injective mod `f`, and put
`ρ = L_F(T_3) ∘ π`.
- `ρ|_{A_3} = L_F(T_3) ∘ conj_{g_3}`, which is isomorphic to `L_F(T_3)`.
- `V^{(t)}` restricted to `SL_2(k)` is `V^{(t mod f)}`, and `L(T) ∘ Frob^{b} = L(T + b)`. So
  `ρ|_{A_i} ≅ L((T_3 mod f) + b_i)` for `i = 1, 2`, a nonempty subset of `Z/f`.

So `ρ` is tensor-type.

**Step 2. Tensor-type restrictions satisfy (T) and (P).** (T) at `A_1` holds by definition. (P) at `A_2` and `A_3`
is Step 5 of the route of `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero`. We also record the exact
commutators.
- **At `A_2`.** `ρ|_{A_2} = conj_g ∘ L(T_2)`. By uniqueness the coefficient operators are
  `X^u_e = g E_12^{(e)} g^{-1}` and `X^v_e = g E_21^{(e)} g^{-1}` for `e ∈ T_2`. So `[X^u_e, X^v_e] = 1`.
- **At `A_3`.** `ρ|_{A_3} = conj_{g'} ∘ L_F(T_3)`. For `y ∈ k`, `u(y)` acts in slot `t` as `1 + y^{2^{t mod f}} E_12`,
  and `v(sy)` as `1 + s^{2^t} y^{2^{t mod f}} E_21`. So `X^u_e = g' E_12^{(t_e)} g'^{-1}` and
  `X^{v(s·)}_e = s^{2^{t_e}} g' E_21^{(t_e)} g'^{-1}`, where `t_e ∈ T_3` is the unique lift of `e ∈ S_3`. Hence
  `[X^u_e, X^{v(s·)}_e] = σ_e := s^{2^{t_e}}`.

**Step 3. `2·hol ≠ 0`.** By Step 2 the hypotheses of `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero`
hold, and it rules out every such `ρ`.

**Step 4. `2·hol = 0 ≠ hol`, the operators.** Now `f` is even and `hol = h = f/2`. Run Steps 0 to 3 of the route
of `sl2-root-triangle-tensor-vertex-reps-force-2hol-zero`; they use only `hol ≠ 0`.
- `M = ⊗_{c ∈ T_1} K^2`, with `y_c = X^u_c` and `x_c = X^v_c` at `A_1`.
- Exact transport (its Step 1) gives scalars `m_c, n_c, p_d ∈ k^*` with:
  - `X^u_{c - a_12} = m_c y_c` at `A_2`;
  - `X^u_{c - a_13} = n_c x_c` at `A_3`;
  - `X^{v(s·)}_{d - a_23} = p_d z_d` at `A_3`.
- For `d ∈ S_2`, put `c_1 = d + a_12` and `c_2 = c_1 - hol = c_1 + h`. Then
  `z_d = β x_{c_1} + γ y_{c_2} + δ x_{c_1} y_{c_2}` for some `β, γ, δ ∈ K`.

Apply Step 2 to the pairs of labels.
- **At `A_2`, label `d = c_1 - a_12`.** `[m_{c_1} y_{c_1}, z_d] = 1`. Also
  `[y_{c_1}, z_d] = β + δ y_{c_2}`, because `[y_{c_1}, x_{c_1}] = 1` and `y_{c_1}` commutes with `y_{c_2}`.
  Since `1` and `y_{c_2}` are linearly independent, `δ = 0` and `β = m_{c_1}^{-1}`.
- **At `A_3`, label `d - a_23 = c_2 - a_13`.** `[n_{c_2} x_{c_2}, p_d z_d] = σ_{c_2 - a_13}`. Also
  `[x_{c_2}, β x_{c_1} + γ y_{c_2}] = γ`. So `γ = γ_d := σ_{c_2 - a_13} n_{c_2}^{-1} p_d^{-1}`.

So `z_d = m_{c_1}^{-1} x_{c_1} + γ_d y_{c_2}`.

**Step 5. `2·hol = 0 ≠ hol`, the contradiction.**
- By `sl2-root-triangle-char2-frobenius-spectrum-transport` (d), `d' := d + h ∈ S_2`, and `d' ≠ d`.
- For `d'` the labels are `c_1' = c_2` and `c_2' = c_1`, so `z_{d'} = m_{c_2}^{-1} x_{c_2} + γ_{d'} y_{c_1}`.
- `x_{c_1}` commutes with `x_{c_2}`, and `y_{c_2}` with `y_{c_1}`, because the slots differ. So
  `[z_d, z_{d'}] = m_{c_1}^{-1} γ_{d'} [x_{c_1}, y_{c_1}] + γ_d m_{c_2}^{-1} [y_{c_2}, x_{c_2}] = m_{c_1}^{-1} γ_{d'} + m_{c_2}^{-1} γ_d`.
- `z_d` and `z_{d'}` are coefficient operators of one parametrization, so they commute. Hence
  `γ_d / γ_{d'} = m_{c_2} / m_{c_1} ∈ k^*`.
- Since `n_c, p_d ∈ k^*`, this gives `σ_{c_2 - a_13} / σ_{c_1 - a_13} ∈ k^*`.

The labels `c_1 - a_13` and `c_2 - a_13` differ by `h` in `Z/f`. So their lifts `t_1, t_2 ∈ T_3 ⊆ Z/2f` satisfy
`t_2 - t_1 ∈ {h, h + f}`. Put:
- `w := σ_{c_1 - a_13} = s^{2^{t_1}}`, which lies in `F \ k`: Frobenius powers are automorphisms of `F`
  preserving `k`, so `w ∈ k` would force `s ∈ k`;
- `r := 2^h`, so `r^2 = q`.

Then `σ_{c_2 - a_13} = w^{2^{t_2 - t_1}}`, which is `w^r` or `w^{rq}`, so `w^e ∈ k^*` for some `e ∈ {r - 1, rq - 1}`.

*Exponent lemma.* `gcd(e, q + 1) = 1`.
- `r` is even, since `h >= 2` because `f >= 4`.
- `q + 1 = (r - 1)(r + 1) + 2`, so `gcd(r ± 1, q + 1)` divides `2`, and both `r ± 1` are odd. Hence `gcd(r - 1, q + 1) = 1`.
- `rq - 1 ≡ -(r + 1) mod (q + 1)`, hence `gcd(rq - 1, q + 1) = 1`.

Now `w^e ∈ k^*` means `w^{e(q-1)} = 1`. So the order of `w` divides
`gcd(e(q - 1), q^2 - 1) = (q - 1) · gcd(e, q + 1) = q - 1`, which means `w ∈ k`. Contradiction.

**Machine checks** (`experiments/sl2-root-triangle-frobenius-holonomy-2026-09-16/scalar_pairing.py`, output in
`out-scalar-pairing.txt`). The proof above does not depend on them.
- **(1)** The exponent lemma for `f = 4, ..., 12`.
- **(2)** For `f = 4`, all `7680` ratios `s^{2^{t_2}}/s^{2^{t_1}}` with `s ∈ F_256 \ F_16` and `t_2 - t_1 ∈ {2, 6}` lie
  outside `F_16`.
- **(3)** The three commutator identities of Steps 4 and 5, mod 2, on `(K^2)^{⊗4}`.

∎
