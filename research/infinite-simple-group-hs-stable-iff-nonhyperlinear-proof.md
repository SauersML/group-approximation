---
rg: 2
id: infinite-simple-group-hs-stable-iff-nonhyperlinear-proof
kind: route
title: Kernel and projective kernel of a tracial limit are normal, simplicity kills both, and conjugate tensor powers turn a nontrivial limit into hyperlinearity
target: infinite-simple-group-hs-stable-iff-nonhyperlinear
requires: []
artifacts:
  - research/artifacts/solve-hyperlinear-not-sofic-2026-09-13.md
---

**Conventions.** `tr = Tr/d` on `M_d`, `||X||_2 = tr(X^* X)^(1/2)`. Hyperlinearity of
`S` means: for every finite `F ⊆ S` and `epsilon > 0` there is `sigma : S -> U(d)`
with `||sigma(gh) - sigma(g) sigma(h)||_2 < epsilon` for `g, h ∈ F` and
`|tr sigma(g)| < epsilon` for `g ∈ F \ {1}`. Enlarging `F` to `F^(-1) F` and using
`||u - v||_2^2 = 2 - 2 Re tr(u^* v)` shows that this agrees with the separation form
`||sigma(g) - sigma(h)||_2 > sqrt 2 - epsilon` for distinct `g, h ∈ F`.

**Two identities.**
- (SC) Let `u` be a unitary in a tracial von Neumann algebra `(M, tau)` and `t = tau(u)`.
  Then `tau((u - t)^*(u - t)) = 1 - |t|^2 - |t|^2 + |t|^2 = 1 - |t|^2`. The trace is
  faithful, so `|tau(u)| = 1` forces `u = tau(u) 1`.
- (TE) For unitaries `A, A'` and `B, B'`,
  `||A ⊗ B - A' ⊗ B'||_2 <= ||(A - A') ⊗ B||_2 + ||A' ⊗ (B - B')||_2 = ||A - A'||_2 + ||B - B'||_2`,
  because the normalized norm is multiplicative on tensor products. So for
  `sigma(g) = (phi(g) ⊗ conj phi(g))^(⊗k)`, where `conj` is entrywise conjugation, the defect
  `||sigma(gh) - sigma(g) sigma(h)||_2` is at most `2k ||phi(gh) - phi(g) phi(h)||_2`, and
  `tr sigma(g) = |tr phi(g)|^(2k)`.

**Lifting.** Let `pi : S -> U(M_omega)`, `M_omega = prod_omega (M_(d_n), tr)`, be a
homomorphism. Each `pi(g)` lifts to a sequence of unitaries `phi_n(g)`: take any bounded
representative and replace each coordinate by the unitary of its polar decomposition.
Enumerate `S = {g_1, g_2, ...}`. For each `m`, the set `A_m` of indices `n` where all defects
on `{g_1..g_m}` are `< 1/m` and `| ||phi_n(g_i) - 1||_2 - ||pi(g_i) - 1||_2 | < 1/m` for
`i <= m` lies in `omega`. The `A_m` decrease and are infinite, so some increasing `n_m ∈ A_m`
exists. Then `psi_m = phi_(n_m)` is an asymptotic representation with
`||psi_m(g) - 1||_2 -> ||pi(g) - 1||_2` for every `g`.

**(2) ⇒ (3).** Apply the lifting to `pi`. By 2 the limit is `0`, so `pi(g) = 1` for all `g`.

**(3) ⇒ (2).** Suppose `phi_n` is asymptotic and `||phi_n(g_0) - 1||_2 >= epsilon` along a
subsequence. Take a free ultrafilter on that subsequence. The ultraproduct of the `phi_n(g)`
is a unitary, the defects vanish along it, so this is a homomorphism into `U(M_omega)` with
`pi(g_0) != 1`. That contradicts 3.

**(1) ⇒ (3).** Let `pi : S -> U(M)` be a nontrivial homomorphism into a tracial von Neumann
algebra `(M, tau)`.
- `ker pi` is normal and not `S`, so `pi` is injective.
- `Z = pi^(-1)(T 1)` is normal, because conjugation preserves scalars. If `Z = S`, then
  `pi(S)` is abelian and `pi` is injective, so `S` is abelian. A simple abelian group is cyclic
  of prime order, and `S` is infinite. So `Z = {1}`.
- For `g != 1`, `pi(g)` is not a scalar, so `|tau(pi(g))| < 1` by (SC). This is the "moreover"
  clause of the claim.
- Now take `M = M_omega` and lift `pi` to `phi_n` as above. Fix a finite `F` and `epsilon`.
  Choose `k` with `|tau(pi(g))|^(2k) < epsilon/2` for all `g ∈ F \ {1}`. Put
  `sigma_n(g) = (phi_n(g) ⊗ conj phi_n(g))^(⊗k)`. By (TE), along `omega` the defects on `F`
  tend to `0`, and `tr sigma_n(g) = |tr phi_n(g)|^(2k) -> |tau(pi(g))|^(2k)`. Some `n` meets both
  requirements with `epsilon`, so `S` is hyperlinear. That contradicts 1.

**(3) ⇒ (1).** If `S` is hyperlinear, take finite `F_m` increasing to `S` and `sigma_m` witnessing
hyperlinearity on `F_m` with `epsilon = 1/m`. This is an asymptotic representation with
`tr sigma_m(g) -> 0`, so `||sigma_m(g) - 1||_2^2 = 2 - 2 Re tr sigma_m(g) -> 2` for `g != 1`.
Such a `g` exists because `S` is infinite. So 2 fails, and 3 fails by (3) ⇒ (2).

**(2) ⇒ (4).** Take `rho_n` trivial.

**(4) ⇒ (5).** Take `D_n = d_n` and `P_n = 1`.

**(5) ⇒ (2).** Every `lambda_n : S -> U(D_n)` is trivial by hypothesis, so
`P_n lambda_n(g) P_n = 1` on `C^(d_n)`, and the flexible distance is `||phi_n(g) - 1||_2 -> 0`.

The hypothesis on finite-dimensional representations enters only in (5) ⇒ (2). ∎
