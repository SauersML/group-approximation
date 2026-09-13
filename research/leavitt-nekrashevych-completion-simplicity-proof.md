---
rg: 2
id: leavitt-nekrashevych-completion-simplicity-proof
kind: route
title: Minimal-support reduction to the core, then saturation
requires:
  - leavitt-nekrashevych-completion-embeds-and-is-fp
target: leavitt-nekrashevych-completion-simplicity-criterion
---

Notation as in the claim; `psi` injective, so `B ⊆ O_psi` by
`leavitt-nekrashevych-completion-embeds-and-is-fp`. Write `O = O_psi`.

## 1. Grading and normal form

The free product `B *_K L_d` is `Z`-graded with the stated degrees, and every
defining relator of `O` is homogeneous of degree 0. So `O = ⊕_k O_k`.

From the covariance relation, multiplying on the right by `s_j` or on the left by
`t_i` and using `t_i s_j = delta_{ij}`:

```text
b s_j = sum_i s_i psi(b)_{ij},        t_i b = sum_j psi(b)_{ij} t_j.
```

These two rules and `t_i s_j = delta_{ij}` rewrite every word in the generators
into a combination of monomials `s_mu b t_nu`. Padding,
`s_mu b t_nu = sum_{i,k} s_{mu k} psi(b)_{k i} t_{nu i}`, raises both lengths by one.
So every `y in O_k` can be written `y = sum_{|mu| = N+k, |nu| = N} s_mu Y_{mu nu} t_nu`
for all large `N`. Since `t_{mu'} s_mu = delta_{mu' mu}` for words of equal length,
`t_{mu'} y s_{nu'} = Y_{mu' nu'}`, which proves part 1.

## 2. Graded ideals

**(a)** Let `J` be a graded ideal. For `y in J_k` with `k > 0`,
`y = sum_{|alpha| = k} s_alpha (t_alpha y)` with `t_alpha y in J_0`. For `k < 0`,
`y = sum_{|alpha| = -k} (y s_alpha) t_alpha` with `y s_alpha in J_0`. So `J` is generated
by `J_0`. By section 1, `J_0` is spanned by `s_mu c t_nu` with `c = t_mu y s_nu in J ∩ B`.
So `J = < J ∩ B >`.

**(b)** `I = J ∩ B` is psi-saturated: if `b in I` then `psi(b)_{ij} = t_i b s_j in I`;
if `psi(b) in M_d(I)` then `b = sum s_i psi(b)_{ij} t_j in J ∩ B`.

**(c)** For a psi-saturated `I`, `psi` induces `psibar : B/I -> M_d(B/I)`, which is
injective because `I = psi^{-1}(M_d(I))`. The presentations give
`O_psi / <I> ≅ O_psibar`. By `leavitt-nekrashevych-completion-embeds-and-is-fp`,
`B/I -> O_psibar` is injective, so `<I> ∩ B = I`. The ideal `<I>` is graded
because it is generated in degree 0.

(a)–(c) give part 2.

## 3. Simplicity (part 3)

*Converse.* A psi-saturated `0 ≠ I ≠ B` gives the ideal `<I>` with
`<I> ∩ B = I ≠ B`, so `<I>` is proper and nonzero.

*Main direction.* Let `J ≠ 0` be an ideal. Choose `x in J \ {0}` whose set of
degrees `supp(x)` has minimal size, and let `m = min supp(x)`.

- If `m > 0`, pick `alpha` with `|alpha| = m` and `t_alpha x_m ≠ 0`. This exists since
  `x_m = sum_alpha s_alpha t_alpha x_m`. Replace `x` by `t_alpha x`.
- If `m < 0`, replace `x` by `s_1^{-m} x`, which kills no component because
  `t_1^{-m} s_1^{-m} = 1`.

The support size does not grow, so by minimality it stays the same, and now
`0 = min supp(x)`. Let `S = supp(x)` and `J_S = { y in J : supp(y) ⊆ S }`.

- *Injectivity of the degree-0 part.* If `y in J_S` and `y_0 = 0`, then
  `|supp y| < |S|`, so `y = 0`.
- *An ideal of the core.* `I_0 = { y_0 : y in J_S }` is a two-sided ideal of `C`.
  It is closed under `y_0 |-> t_i y_0 s_j` and `y_0 |-> s_i y_0 t_j`, since those
  operations preserve degrees and map `J_S` to `J_S`.
- *A saturated ideal of B.* `I = I_0 ∩ B` is an ideal of `B`, and it is
  psi-saturated by the argument of 2(b), using these closure properties. It is
  nonzero: a nonzero `y_0 in I_0` has a nonzero entry `t_mu y_0 s_nu in I_0 ∩ B`.
- By psi-minimality `I = B`, so `1 in I_0`: there is `y in J_S` with `y_0 = 1`.
- For every `c in C`, the element `cy - yc` lies in `J_S` and has degree-0 part
  `c - c = 0`, so `cy = yc`. Comparing components, `y_k c = c y_k` for every `k`.
- By aperiodicity, `y_k = 0` for `k ≠ 0`. So `y = 1 in J` and `J = O`.

## 4. Leavitt calibration (part 4)

Here `B = K` and `C` is the direct limit of `M_{d^N}(K)`, containing the matrix
units `e_{ab} = s_a t_b` for `|a| = |b| = N`.

**No off-degree centralizer.** Let `y in O_k`, `k > 0`, commute with `C`. Write
`y = sum Y_{mu nu} s_mu t_nu` at level `N`, with `Y_{mu nu} in K`.

- *Commuting at level N.* `t_b s_mu = s_omega` if `mu = b omega`, and `0` otherwise, so
  `e_{ab} y = sum Y_{b omega, nu} s_{a omega} t_nu` and `y e_{ab} = sum_mu Y_{mu a} s_mu t_b`.
  Comparing coefficients by part 1 gives `Y_{b omega, nu} = delta_{nu b} w_omega` for some
  `w in K^{d^k}`. So `y = sum_{|nu| = N, |omega| = k} w_omega s_{nu omega} t_nu`.
- *Commuting at level N+1.* Padding gives the coefficient `w_omega` at index
  `(nu omega i, nu i)`, and the same computation at level `N+1` forces each nonzero
  coefficient into position `(b' omega', b')` with `|b'| = N+1`. That needs
  `omega i = i omega'`.
- *Conclusion.* If `w_omega ≠ 0`, choose `i ≠ omega_1`, which is possible because
  `d >= 2`. Then no `omega'` satisfies `omega i = i omega'`, a contradiction. So
  `w = 0` and `y = 0`.
- *Negative degrees.* The case `k < 0` follows by applying the anti-automorphism of
  `L_d` exchanging `s_i` and `t_i`, which preserves `C` and maps `O_k` to `O_{-k}`.

`K` is trivially psi-minimal. So by part 3, `L_d` is simple.

**Center.** If `z` is central, each component `z_k` commutes with `C`, since `C`
lies in degree 0. So `z_k = 0` for `k ≠ 0`. Then `z = z_0` is represented at
some level `N` by a matrix commuting with every matrix unit of `M_{d^N}(K)`, hence
is scalar.
