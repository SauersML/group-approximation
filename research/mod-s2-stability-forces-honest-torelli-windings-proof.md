---
rg: 2
id: mod-s2-stability-forces-honest-torelli-windings-proof
kind: route
title: Pull a Dadarlat asymptotic homomorphism of Sp4(Z) back to Mod(S_2), straighten it to honest representations, and read its winding off one separating twist
target: mod-s2-stability-forces-honest-torelli-windings
requires:
  - dadarlat-linear-groups-have-nonzero-h2-windings
  - sp4-quasirep-windings-budget-and-saturation
  - mod-s2-real-untwisting-identifies-deligne-norm-parameters
  - deligne-torelli-character-counts-separating-twists
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
---

Notation as in the target. Inputs:
- **[D]** `dadarlat-linear-groups-have-nonzero-h2-windings`: for a finitely generated linear group and a
  non-torsion `x in H_2` represented by `prod [a_i, b_i]`, some unital asymptotic homomorphism
  `V_n : Gamma -> U(k_n)` has `kappa(prod [V_n(a_i), V_n(b_i)]) != 0` for all large `n`
  (Lemma 2.1 there: this is `(1/2 pi i) Tr log`, an integer, locally constant).
- **[R]** `sp4-quasirep-windings-budget-and-saturation`: a relator `R = prod [a_i, b_i]` of `Gamma` with
  `prod [a_i^, b_i^] = zeta^k` in `E_infinity = Gamma x_b Z`, `k != 0`.
- **[U1]** `mod-s2-real-untwisting-identifies-deligne-norm-parameters`: `f : M -> R` with
  `f(m) + f(m') - f(mm') = b(pi m, pi m')`, `f|_K = r sigma`, `sigma(t_s) = 1`, `r = a/10`, `3 not | a`.
- **[ST]** `deligne-torelli-character-counts-separating-twists` (ST1, ST2): separating twists form one
  conjugacy class, `K` is its normal closure, and every `k in K` is `prod_j g_j t_s^(e_j) g_j^(-1)`.
- **[H]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`: `H_1(M;Z) = Z/10`, and
  `1 -> K -> M -> Gamma -> 1`.

**Step 0: the class of `R` is non-torsion.** For the central extension `E_infinity`, the rule
`prod [a_i, b_i] |-> prod [a_i^, b_i^]` is well defined on `H_2(Gamma;Z)` (Hopf) and is a homomorphism
into the central `Z` (it is the boundary map `H_2(Gamma;Z) -> H_1(Z)_Gamma = Z` of the five-term
sequence). It sends `x = [R]` to `k != 0`, so `x` has infinite order. `Gamma = Sp_4(Z)` is finitely
generated and linear, so [D] applies to `x`: fix `V_n` with integer windings
`kappa_n := kappa(prod [V_n(a_i), V_n(b_i)]) != 0`.

**Step 1: `sigma(w) = -k/r`.** Since `b` is normalized and integral, `phi(m) = (pi m, -f(m))` is a
homomorphism `M -> Gamma x_b R`: `-f(mm') = -f(m) - f(m') + b(pi m, pi m')`. Commutators ignore the central
coordinate, so `phi(w) = prod [phi(a_i~), phi(b_i~)] = prod [a_i^, b_i^] = (e, k)`. Hence `f(w) = -k`. As
`w in K`, `sigma(w) = f(w)/r = -k/r`.

**Step 2: local additivity of `kappa`.** Let `A_1, ..., A_L` be unitaries in `U(d)` with
`||A_j - 1|| <= eta` and `L eta < 2`. Put `A_j(t) = exp(t log A_j)`, `0 <= t <= 1` (principal log). Since
`|exp(i t theta) - 1| <= |exp(i theta) - 1|` for `|theta| <= pi`, `||A_j(t) - 1|| <= eta`, so
`P(t) = A_1(t) ... A_L(t)` has `||P(t) - 1|| <= L eta < 2` and `kappa(P(t))` is continuous in `t`. The function
`F(t) = kappa(P(t)) - sum_j t kappa(A_j)` is continuous, takes values in `Z` because both terms exponentiate to
`det P(t) = prod det A_j(t)`, and `F(0) = 0`. So `kappa(A_1 ... A_L) = sum_j kappa(A_j)`. Also
`kappa(g A g^-1) = kappa(A)` and `kappa(A^-1) = -kappa(A)`.

**Step 3: (TW1).** By [ST] write `w = prod_{j<=L} g_j t_s^(e_j) g_j^(-1)` with `e_j = +-1`; its exponent sum
is `sigma(w)` (ST2 with integer coefficients: `sigma` is a homomorphism equal to `1` on every separating
twist, [U1]). For an honest `rho`, every factor `rho(g_j t_s^(e_j) g_j^-1)` is at distance
`||rho(t_s) - 1||` from `1`. If `L ||rho(t_s) - 1|| < 2`, Step 2 gives
`kappa(rho(w)) = sigma(w) kappa(rho(t_s))`, and `rho(w) = prod [rho(a_i~), rho(b_i~)]`. Finally
`exp(2 pi i kappa(rho(t_s))) = det rho(t_s)`, and `det o rho` factors through `H_1(M;Z) = Z/10` [H], so
`kappa(rho(t_s)) in (1/10)Z`.

**Step 4: (TW2).** `W_n = V_n o pi` is a unital asymptotic homomorphism of `M` with the same pairwise
defects. By stability there are honest `rho_n` with `||rho_n(m) - V_n(pi m)|| -> 0` for every fixed `m`.
- At `m = t_s`: `V_n(pi t_s) = V_n(e) = 1`, so `eta_n = ||rho_n(t_s) - 1|| -> 0`.
- At the `2g` letters: `delta_n = max_y ||rho_n(y~) - V_n(y)|| -> 0`. For `t in [0,1]` let `u_t(y)` be the unitary
  part of `(1-t) V_n(y) + t rho_n(y~)`; for `delta_n < 1` it is within `2 delta_n` of both endpoints. The words
  `P_t = prod [u_t(a_i), u_t(b_i)]` are within `8 g delta_n` of `P_0 = prod [V_n(a_i), V_n(b_i)]`, and
  `P_0 -> 1` because `V_n` is an asymptotic homomorphism and `R = 1` in `Gamma`. So for large `n`,
  `||P_t - 1|| < 2` for all `t`, each `P_t` has determinant `1`, and `kappa(P_t)` is a continuous integer:
  `kappa(prod [rho_n(a_i~), rho_n(b_i~)]) = kappa_n`.
- For large `n`, `L eta_n < 2`, so Step 3 gives `sigma(w) kappa(rho_n(t_s)) = kappa_n`, that is
  `kappa(rho_n(t_s)) = -r kappa_n / k = -a kappa_n / (10 k)`, nonzero and of absolute value at least
  `1/(10|k|)` since `|a|, |kappa_n| >= 1`.

**Step 5: (TW3)** is the contrapositive of (TW2).
