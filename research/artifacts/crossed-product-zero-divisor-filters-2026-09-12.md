# Zero-divisor filters for Cohn-family witnesses in the odd-measure crossed product

Lane `w4-cohn-gram`, 2026-09-12. Supports `mixed-depth-leavitt-lift-is-a-left-zero-divisor` (Section 1).
Later sections support the filters named there. Targets they bear on:
`ternary-anti-central-summand-has-cohn-family` and
`odd-measure-crossed-product-unit-below-cylinder-idempotent`.

## 0. Setup

Notation follows `research/artifacts/ternary-lift-signed-thompson-crossed-product-2026-09-12.md` and
`research/artifacts/ternary-cohn-mixed-depth-lifts-2026-09-12.md`.
- `G = L_(F_3)(1,2)^x`, `S_- = eps_- F_3[G]`, `H = E x| V`, and
  `B = F_3[H] eps_- ~= C(M_-, F_3) x|_alg V ⊆ S_-`.
- `U_C = { mu in M_- : mu(C) = 1 }`, `P_C = 1_(U_C)`, and `g U_C = U_(gC)`.
- Conventions: `[g] f [g]^-1 = g.f` with `(g.f)(mu) = f(g^-1 mu)`. So `[g] 1_U = 1_(gU) [g]` and
  `1_U [g] = [g] 1_(g^-1 U)`.
- The linear map `* : [g] -> [g^-1]` is an anti-automorphism of `F_3[G]`. It fixes `eps_-` and every
  function in `C(M_-, F_3)`, and on `B` reads `([g] f)* = f [g^-1]`.
- Every `x in B` has a unique form `x = sum_(g in F) [g] b_g` with `F ⊆ V` finite and
  `b_g in C(M_-, F_3)`.

A ring element `x` is a *left zero divisor* if `x y = 0` for some `y != 0`. It is then not left
invertible in any ring containing both: `z x = 1` would give `y = z x y = 0`.

## 1. The mixed-depth lift is a left zero divisor

Take the data of Lemma 2.1 of the mixed-depth artifact: Thompson units `g_0, g_1` with
`g_0(0x) = 00x` and `g_1(1x) = 01x`, and

```text
sigma = [g_0] P_0 + [g_1] P_1,        tau = [g_0^-1] P_00 + [g_1^-1] P_01,
A = g_1^-1(00),   B' = g_0^-1(01),   h = g_0^-1 g_1,
W_1 = U_A ∩ U_1,   W_2 = U_0 ∩ U_(B'),   F = 1_(W_1) + 1_(W_2),   D = [h]1_(W_1) + [h^-1]1_(W_2),
e' = 2(F - D).
```

**Proposition 1.1.** For every choice of `g_0, g_1`:
1. `sigma F = sigma D = [g_1] 1_(W_1) + [g_0] 1_(W_2)`, so `sigma e' = 0`.
2. `tau = sigma*`, `D* = D` and `e'* = e'`, so `e' tau = 0`.
3. `e' != 0`. Hence `e'` is not in `S_- sigma`, `sigma` is not left invertible in any ring containing
   `B`, and `tau` is not right invertible in any such ring.
4. No `2 x 2` Gram matrix `[tau_i sigma_j]` over any ring containing `B` is invertible when some
   `sigma_j = sigma` or some `tau_i = tau`, whatever the other three entries are.

*Proof.* The set computations below use `mu(X) = 1` and additivity mod 2. From the definitions,
`h(A) = 0`, `h(1) = B'`, `h(0) = 0 ∪ (1 \ B')`, `h^-1(0) = A` and `h^-1(1) = 1 ∪ (0 \ A)`
(Lemma 2.1, item 2, of the mixed-depth artifact).

*Item 1, `sigma F`.* `W_2 ⊆ U_0`, `W_1 ⊆ U_1` and `U_0 ∩ U_1 = ∅`. So
`[g_0] P_0 F = [g_0] 1_(W_2)` and `[g_1] P_1 F = [g_1] 1_(W_1)`.

*Item 1, `sigma D`, four terms.*
- `[g_0] P_0 [h] 1_(W_1) = [g_0 h] 1_(U_(h^-1(0)) ∩ W_1) = [g_1] 1_(U_A ∩ W_1) = [g_1] 1_(W_1)`.
- `[g_0] P_0 [h^-1] 1_(W_2) = [g_0 h^-1] 1_(U_(h(0)) ∩ W_2)`. For `mu in W_2`: `mu(0) = 1` and
  `mu(B') = 1`, so `mu(1) = 0`, `mu(1 \ B') = 1` and `mu(0 ∪ (1 \ B')) = 0`. The set is empty.
- `[g_1] P_1 [h] 1_(W_1) = [g_1 h] 1_(U_(h^-1(1)) ∩ W_1)`. For `mu in W_1`: `mu(A) = mu(1) = 1`, so
  `mu(0) = 0`, `mu(0 \ A) = 1` and `mu(1 ∪ (0 \ A)) = 0`. The set is empty.
- `[g_1] P_1 [h^-1] 1_(W_2) = [g_1 h^-1] 1_(U_(h(1)) ∩ W_2) = [g_0] 1_(U_(B') ∩ W_2) = [g_0] 1_(W_2)`,
  since `g_1 h^-1 = g_0`.

So `sigma D = [g_1] 1_(W_1) + [g_0] 1_(W_2) = sigma F`, and `sigma e' = 2 sigma (F - D) = 0`.

*Item 2.* `sigma* = P_0 [g_0^-1] + P_1 [g_1^-1] = [g_0^-1] 1_(U_(g_0(0))) + [g_1^-1] 1_(U_(g_1(1)))
= [g_0^-1] P_00 + [g_1^-1] P_01 = tau`. Next `([h] 1_(W_1))* = 1_(W_1) [h^-1] = [h^-1] 1_(h W_1)
= [h^-1] 1_(W_2)`, and symmetrically `([h^-1] 1_(W_2))* = [h] 1_(W_1)`, because `h W_1 = W_2`. So
`D* = D` and `e'* = e'`. Applying `*` to `sigma e' = 0` gives `e' tau = 0`.

*Item 3.* The identity grade of `e'` is `2F`, a nonzero function, because `W_1` and `W_2` are nonempty
(Lemma 2.1, item 1). If `z sigma = eps_-` then `e' = z sigma e' = 0`. The right-hand statement for
`tau` is the image of this under `*`.

*Item 4.* Put `Sigma = (sigma_1, sigma_2)` and `T = (tau_1, tau_2)^t`, so the Gram matrix is `T Sigma`.
If `T Sigma` has an inverse `N`, then `(N T) Sigma = I_2`, so `Sigma` is left invertible as a map on
column vectors. But `Sigma` kills the column with `e'` in slot `j` and `0` in the other slot. Dually
`T (Sigma N) = I_2`, and the row with `e'` in slot `i` kills `T`. QED

**Remarks.**
- The same computation with first letters exchanged (`g_0(0x) = 10x`, `g_1(1x) = 11x`) shows the
  natural lift of `s_1` is a left zero divisor too. Section 3 derives both from a general dichotomy.
- `tau sigma = 1 + D` and `(1 + D) e' = e' + D e' = e' - e' = 0`, which is consistent with item 1.
- On a generic orbit, `sigma` sends the two points `mu in W_2` and `h^-1 mu in W_1` to the single point
  `g_0 mu` of `U_00 ∩ U_01`. The vector `delta_mu - delta_(h^-1 mu)` is killed, and `e'` is the ring-level
  form of that kernel vector.
- The correction `tau''` of Lemma 2.1 cannot be completed to a left inverse: the defect `e'` is not
  removable, it is annihilated.
