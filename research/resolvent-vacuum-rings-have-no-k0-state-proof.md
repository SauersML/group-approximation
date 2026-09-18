---
rg: 2
id: resolvent-vacuum-rings-have-no-k0-state-proof
kind: route
title: Distinct N-eigenvalues make the vacuum copies orthogonal; fullness then leaves no room for a state
target: resolvent-vacuum-rings-have-no-k0-state
requires: []
---

Lane proof, elementary, not independently reviewed.

## 1. Orthogonal copies
- **Idempotents.** `P_m^2 = x_m (y_m x_m) y_m = x_m E y_m = x_m y_m`, since `x_m ∈ RE` and
  `y_m ∈ ER`.
- **Orthogonality.** For `m ≠ m'`,
  `λ_(m') y_m x_(m') = y_m N x_(m') = λ_m y_m x_(m')`. So `(λ_(m') − λ_m) y_m x_(m') = 0`, and
  `y_m x_(m') = 0` because `λ_(m') − λ_m` is a non-zero-divisor. Hence
  `P_m P_(m') = x_m (y_m x_(m')) y_(m') = 0`.
- **Equivalence.** `x_m : ER -> P_m R` and `y_m : P_m R -> ER`, acting by left multiplication,
  are mutually inverse isomorphisms of right modules, since `y_m x_m = E` and
  `x_m y_m = P_m`. So `P_m ~ E`.
- **Counting.** For `M >= 1`,
  `R = P_1 R ⊕ ... ⊕ P_M R ⊕ (1 − P_1 − ... − P_M) R`, and the last summand is a module
  because the `P_i` are orthogonal idempotents. So `M[E] <= [1]` in `V(R)`.

## 2. A full vacuum
- **Fullness gives a bound.** Suppose `R E R = R`, so `1 = Σ_(i<=k) a_i E b_i`. The map
  `(ER)^k -> R`, `(E r_i) ↦ Σ a_i E r_i`, hits `1`, hence is a split surjection of right
  modules. So `R` is a direct summand of `(ER)^k`, and `[1] <= k[E]`.
- **(b) No state.** A state `f` would give `M f([E]) <= 1 <= k f([E])` for every `M`, by §1
  and the bound. Taking `M = 2k` gives `2k f([E]) <= k f([E])`, so `f([E]) <= 0`. Then
  `1 <= k f([E]) <= 0`, a contradiction.
- **(a) Not stably finite.** Put `P = (ER)^k`. By the bound, `P ≅ R ⊕ Z` for some `Z`. By
  §1 with `M = 2k`, `R ≅ (ER)^(2k) ⊕ Y` for some `Y`. So
  `P ≅ (ER)^(2k) ⊕ Y ⊕ Z ≅ P ⊕ P ⊕ Y ⊕ Z`. Then `End(P)` contains a split injection
  `P -> P` that is not surjective, since its cokernel `P ⊕ Y ⊕ Z` is nonzero, so `End(P)` is
  not directly finite. `End(P)` is the corner `e M_k(R) e`, with
  `e = diag(E, ..., E)`, and a corner of a directly finite ring is directly finite. Hence
  `M_k(R)` is not directly finite. ∎

## 3. The instances
- **R_L.** `t_2 t_1^(m−1) s_1^(m−1) s_2 = 1`. `N s_1^(m−1) s_2 = s_1^(m−1)(N + m − 1) s_2`,
  which equals `(m − 1) s_1^(m−1) s_2` because `N s_2 = 0`. Dually, `t_1 N = (N+1) t_1` and
  `t_2 N = 0` give `t_2 t_1^(m−1) N = (m−1) t_2 t_1^(m−1)`. This is §1 of
  `leavitt-resolvent-ring-is-fp-simple-of-char-zero-proof`.
- **R_T.** `N E = E N = 0` and `T N = (N+1) T`, from `N = N(ST + E)` and `NS = S(N+1)`.
  These give the same two identities for `S^(m−1) E` and `E T^(m−1)`.
- **R_k.** Replace `s_1` by `s_n` and `s_2` by `s_v`, and `N` by the register `N`.
