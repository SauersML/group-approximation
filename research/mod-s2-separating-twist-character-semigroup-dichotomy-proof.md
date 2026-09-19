---
rg: 2
id: mod-s2-separating-twist-character-semigroup-dichotomy-proof
kind: route
title: Direct sums convexify, tensor products multiply and duals conjugate the separating-twist trace, and powers of a tangent trace sweep the circle
target: mod-s2-separating-twist-character-semigroup-dichotomy
requires:
  - deligne-torelli-character-counts-separating-twists
  - mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors
---

Notation as in the target. Let `S` be the set of values `tr rho(t_s)`, so `X` is its closure.

**(D1).**
- `|tr U| <= 1` for unitary `U`. So `X` lies in the closed unit disc and is compact.
- The trivial representation gives `1 in S`.
- *Products.* `tr (rho tensor sigma)(t_s) = tr rho(t_s) tr sigma(t_s)`. So `S`, and hence `X`, is closed under
  products.
- *Conjugation.* The contragredient `conj(rho)` has trace `conj(tr rho(t_s))`.
- *Convexity.* Take `p` copies of `rho_1`, of dimension `d_1`, and `q` copies of `rho_2`, of dimension `d_2`.
  Their direct sum has trace `lambda x_1 + (1 - lambda) x_2`, where `lambda = p d_1/(p d_1 + q d_2)`. These
  `lambda` are dense in `[0,1]`. So the closure `X` is convex.

**(D2).**
- `G_2` is closed and closed under products.
- For `|x| = 1`, `conj(x) = x^(-1)`, so `G_2` is closed under inverses.
- `1 in G_2`. So `G_2` is a closed subgroup of `S^1`, and such subgroups are `S^1` or `mu_m`.

**(D3).**
- The displayed identity is `||U - a||_2^2 = 2 - 2 Re(conj(a) tr U)`, valid for unitary `U` and `|a| = 1`.
- So `inf_rho ||rho(t_s) - omega I||_2 = 0` iff `sup_(x in X) Re(conj(omega) x) = 1`. Since `X` is compact
  and lies in the disc, this holds iff `omega in X`, iff `omega in G_2`.
- By conjugation, `omega in G_2` iff `omega^2 in G_2`.
- `omega in G_2` iff `G_2 = S^1` or `3 | m`.

**(D4).**
- *(=>)* If `G_2 = S^1`, take `x_n = exp(i/n)`. Then `1 - |x_n| = 0`.
- *(<=)* Let `x = r exp(i phi)` in `X`, with `r = 1 - a`, `a <= 1/2`, `a = o(|phi|)`, and `phi != 0` small.
  - By conjugation, assume `phi > 0`.
  - Fix `psi in (0, 2 pi)` and put `k = floor(psi/phi)`. Then `x^k in X`, with `|k phi - psi| <= phi`.
  - Also `|x^k| = (1 - a)^k >= exp(-2 a k) >= exp(-2 a psi/phi)`.
  - Along the sequence, `x_n^(k_n) -> exp(i psi)`, so `exp(i psi) in X` because `X` is closed.
  - So `G_2 = S^1`.

**(D5).**
- The cone condition fails iff there is a sequence `x_n -> 1` in `X` with `1 - |x_n| < |arg x_n|/n`.
  - This forces `arg x_n != 0`.
  - Such a sequence is exactly the tangent sequence of (D4).
- Hence the cone condition holds iff `G_2 != S^1`, iff `G_2` is finite.

**(D6).**
- The expansion comes from averaging `exp(i phi) = 1 + i phi - phi^2/2 - i phi^3/6 + O(phi^4)` over the
  spectrum.
- It gives `|tr|^2 = 1 - v + O(eps^4)` and `arg tr = mu + O(eps^3)`.
- Suppose `v = o(|mu|)` and `eps^3 = o(|mu|)`. Then `(1 - |x|)/|arg x| -> 0`, and (D4) gives `G_2 = S^1`.
- Then `omega in G_2`, and the honest representations `rho_n` with `||rho_n(t_s) - omega I||_2 -> 0` give
  vanishing defect. By (E2) of `mod-s2-exact-models-are-fd-character-limits-of-deligne-sectors`, `E_3` is
  hyperlinear.
