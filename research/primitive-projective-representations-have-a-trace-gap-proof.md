---
rg: 2
id: primitive-projective-representations-have-a-trace-gap-proof
kind: route
title: Clifford along a minimal normal subgroup above the scalars; Heisenberg-basis coefficients constant on Im(g-1); tensor slots permuted or normalized
target: primitive-projective-representations-have-a-trace-gap
requires: []
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-part2-2026-09-13.md
---

Complete proof: Theorem 15 of the artifact. Inputs are textbook: Clifford
homogeneity, Skolem--Noether, Burnside's theorem, and the Schur multiplier of a
product of perfect groups [recalled].

* **Reduction.** `Z = { x : sigma(x) scalar }`. Choose `N/Z` minimal normal in
  `X/Z`. Isotypic components under `N` would form a system of imprimitivity, so
  there is one, and `V = V_tau (x) W` with `span sigma(N) = End(V_tau) (x) 1`.
  Skolem--Noether gives `sigma(x) = taut(x) (x) pit(x)`, where `pit` is an
  irreducible primitive projective representation of `X/N`, since blocks of
  `pit` give blocks of `sigma`. If `taut(h)` is scalar, then
  `|tr sigma(h)|/d = |tr pit(h)|/dim W`, and induction on `|X|` applies.
* **Symplectic case.** `N/Z = F_p^(2a)` with nondegenerate commutator form,
  since a trivial form would make `End(V_tau)` commutative. The unitary lifts
  `U_v` form an orthonormal basis of `End(V_tau)`, with `tr U_v = 0` for `v != 0`.
  Write `taut(h) = sum c_v U_v` and `taut(h) U_w taut(h)^-1 = lambda_w U_(gw)`.
  If `g = 1`, `lambda` is a character, so `taut(h)` is a scalar multiple of some
  `U_(v_0)`, and its trace is `0`. If `g != 1`, comparing coefficients gives
  `|c_v| = |c_(v + (g-1)w)|`, so `p |c_0|^2 <= sum |c_v|^2 = 1`.
* **Tensor case.** `N/Z = T^s` gives `V_tau = V_1 (x) ... (x) V_s`, each of
  dimension `d_0 >= 2`. `taut(h)` is a scalar times `P_pi (A_1 (x) ... (x) A_s)`.
  If `pi != 1`, the trace is a product over cycles, and `|tr|/dim <= d_0^-1 <= 1/2`.
  If `pi = 1`, a non-scalar `A_j` normalizes `tau_j(T)`, and the ratio is at most
  `gamma(T)`.
* **`gamma(T) < 1`.** If two unitaries induce the same automorphism, the
  discrepancy is a character of the perfect group `T`, hence trivial. So there are
  finitely many values, each `< 1` for a non-scalar unitary.
