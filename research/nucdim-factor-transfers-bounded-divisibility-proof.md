---
rg: 2
id: nucdim-factor-transfers-bounded-divisibility-proof
kind: route
title: Divide colour by colour in the first factor and cut the order zero maps by functional calculus
target: nucdim-factor-transfers-bounded-divisibility
requires: []
artifacts:
  - research/artifacts/nucdim-factor-comparison-divisibility-2026-09-16.md
---

Full proof: artifact Section 6 (Theorem B and Corollary B'), with the
elementary comparison lemmas of artifact Section 1, all proved there.

Normalize `||a|| <= 1`, put `eta = eps/(4(m+1))` and `kappa = min(eta^2, eps/2)`.
Take a piecewise contractive `m`-decomposable approximation `(F, psi, phi)` of
`B` such that `T = id tensor phi psi` satisfies `||T(a) - a|| < kappa`.  For each
colour `i`, `D^(i) = cA tensor F^(i)` has Cuntz semigroup a finite product of
copies of `Cu(A)`, so it is almost divisible; `c_i = (id tensor psi^(i))(a)` is
a positive contraction, and `theta_i = id tensor phi^(i)` is c.p.c. order zero
(Winter--Zacharias, arXiv:0903.3290, Cor. 3.3), written `theta_i = h_i pi_i`
(ibid. Thm 2.3).  Put `s = h_i`, `t = pi_i(c_i)` and use the cut map
`theta_(i,eta) = (h_i - eta)_+ pi_i` (ibid. Cor. 3.2).

- Almost divisibility applied to `[(c_i-2eta)_+] << [(c_i-eta)_+]` gives `w_i`
  with `N[w_i] <= [(c_i-eta)_+]` and `[(c_i-2eta)_+] <= (N+1)[w_i]`; put
  `Y = sum_i [theta_(i,eta)(w_i)]`.  Order zero maps preserve Cuntz comparison
  of amplifications (ibid. Cor. 3.5).
- Upper bound: `(s-eta)_+(t-eta)_+` has support inside `{st > eta^2}`, so it is
  Cuntz below `(T_i(a) - eta^2)_+` (artifact Lemma 1.9, a support lemma in the
  commutative algebra `C*(1,s,t)`), and `T_i(a) - kappa <= a` gives
  `(T_i(a)-kappa)_+ <~ a` (artifact Lemma 1.6).  Hence `N Y <= (m+1)[a]`.
- Lower bound: `[(a-eps)_+] <= [(T(a)-eps/2)_+] <= sum_i [(T_i(a)-2eta)_+]`
  (artifact Lemmas 1.8, 1.7), and `{st > 2eta}` lies in
  `{(s-eta)_+(t-2eta)_+ > 0}` because `s, t <= 1`, so each summand is at most
  `(N+1) [theta_(i,eta)(w_i)]`.

Corollary: given `x' << x = [a]`, choose `eps` with `x' <= [(a-3eps)_+]` and apply
the theorem to `(a-eps)_+`, tolerance `eps`, and `N-1` (if `N >= 2`); then
`x' << [(a-2eps)_+] <= N y` and `N y <= 2(N-1) y <= 2(m+1)[(a-eps)_+] << 2(m+1)x`.
For `N = 1` take `y = [(a-2eps)_+]`.

Imports: Winter--Zacharias, Munster J. Math. 2 (2009), Thm 2.3, Cors 3.2, 3.3,
3.5 (arXiv numbering); Kirchberg--Rordam, Adv. Math. 167 (2002), Lemma 2.2.
