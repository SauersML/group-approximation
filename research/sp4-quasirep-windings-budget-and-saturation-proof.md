---
rg: 2
id: sp4-quasirep-windings-budget-and-saturation-proof
kind: route
title: Telescope the relator word, read the winding off eigenvalue angles, and feed parameter models through it
target: sp4-quasirep-windings-budget-and-saturation
requires:
  - deligne-sep7-norm-parameter-closed-subgroup
  - deligne-sep8-first-order-tensor-threshold
  - dadarlat-linear-groups-have-nonzero-h2-windings
---

**Step 0: a relator with `k != 0`.** Suppose `[E,E]` meets `<zeta>` trivially, where `E = E_infinity`. Then `<zeta>`
injects into `E^ab`. Since `<zeta> = Z`, some homomorphism `f : E -> Z` has `f(zeta) = n != 0`. Put
`s(g) = f(g^)`. From `g^ h^ = zeta^(b(g,h)) (gh)^` we get `s(g) + s(h) = n b(g,h) + s(gh)`, so `n b = delta s`.
Then `n c = 0` in `H^2(Gamma;Z)`, where `c = [b]`. This contradicts the fact that `c` has infinite order: the real
class of the integral Maslov cover is nonzero, and `H^2(Gamma;Q) = Q`. So some `zeta^k` with `k != 0` is a product of
commutators in `E`. Central factors drop out of commutators, so the product can be written as
`prod [a_i^, b_i^]` with `a_i, b_i in Gamma`. Its image `prod [a_i, b_i]` in `Gamma` is `1`.

**Step 1: telescoping.** Use the cocycle model `(g,i)(h,j) = (gh, i+j+b(g,h))`, with `zeta = (e,1)`. Since `b` is
normalized, `(g,0)^(-1) = (g^(-1), -b(g,g^(-1)))`. Given `U` as in item 2, put `rho(g,i) = exp(2 pi i t i) U(g)`.
For `x = (g,i)` and `y = (h,j)`, we have `||rho(x)rho(y) - rho(xy)|| = ||U(g)U(h) - exp(2 pi i t b(g,h)) U(gh)||`,
which is at most `eta` on `W_r`.

Inverse letters:
- `U(g)U(g^(-1))` is within `eta` of `exp(2 pi i t b(g,g^(-1))) I`.
- So `rho((g^)^(-1)) = exp(-2 pi i t b(g,g^(-1))) U(g^(-1))` is within `eta` of `U(g)^*`, since `U(g)` is unitary.
- In the word `prod [pi(a_i), pi(b_i)]` there are `2g` starred letters. Replacing each by the matching `rho` of an
  inverse lift costs at most `2g eta`, because `U` takes unitary values, so every factor of the word has norm `1`.
  The `Gamma`-parts of these inverse lifts are the letters `a_i^(-1), b_i^(-1)`, so the pairs used below lie in
  `W_r`.

Chain: the `4g` letters are multiplied left to right. This takes `4g-1` products, each replacing
`rho(p_j) rho(y_(j+1))` by `rho(p_j y_(j+1))` at cost `eta`. The final product is `rho(zeta^k) = exp(2 pi i t k) I`.

Total: `||W_r(U) - exp(2 pi i t k) I|| <= (6g-1) eta`.

**Step 2: eigenvalues (item 2).** Put `delta = (6g-1) eta <= 1` and `V = exp(-2 pi i t k) W_r(U)`. Then `V` is
unitary with `||V - I|| <= delta`. Each eigenvalue `exp(i phi_j)` of `V`, with `|phi_j| <= pi`, satisfies
`|exp(i phi_j) - 1| = 2 |sin(phi_j/2)| <= delta`, so `|phi_j| <= 2 arcsin(delta/2) <= pi/3`.

The eigenvalues of `W_r(U)` are `exp(i(2 pi t k + phi_j))`. Since `|2 pi t k| <= pi/2`, each angle
`2 pi t k + phi_j` lies in `(-pi, pi)`. So the principal branch applies, `||W_r(U) - 1|| < 2`, and

```text
kappa_r(U) = (1/2 pi) sum_j (2 pi t k + phi_j) = k t d + (1/2 pi) sum_j phi_j.
```

It is an integer: `W_r(U)` is a product of commutators, so its determinant is `1`, and `exp(2 pi i kappa) = 1`.
The error is at most `(d/2 pi) 2 arcsin(delta/2) = (d/pi) arcsin(delta/2)`. The bound `arcsin y <= pi y/2` on
`[0,1]` gives `(d/pi) arcsin(delta/2) <= d delta/4`.

**Item 1 (budget).** Apply Step 2 with `t = 0` and `U = pi`: the relevant defect is the plain defect, so `eta = eps`
on `W` containing `W_r`. For a normalized `pi` this uses `pi(e) = I`, as `unital` requires. Then
`|kappa_r(pi)|/d <= (6g-1) eps / 4`.

**Item 3 (saturation).** Suppose `P_op = R/Z`. By assertion 3 of `deligne-sep8-first-order-tensor-threshold`, there
are `t_n -> 0`, `t_n != 0`, and `t_n`-models `U_n` with errors `eta_n = o(|t_n|)` on `W`.
- As plain maps on `Gamma`, their defect on `W` is `eps_n <= eta_n + |exp(2 pi i t_n b) - 1| <= eta_n + 2 pi B_W |t_n|`.
- For large `n`, `|k t_n| <= 1/4` and `(6g-1) eta_n <= 1`. By Step 2,
  `|kappa_r(U_n)|/d_n >= |k||t_n| - (6g-1) eta_n / 4`.
- Dividing: `S_W(eps_n)/eps_n >= (|k||t_n| - o(|t_n|)) / (2 pi B_W |t_n| + o(|t_n|)) -> |k| / (2 pi B_W)`.

`B_W > 0`: otherwise `b = 0` on `W`, so `eps_n = eta_n = o(|t_n|)`, and items 1 and 2 give
`|k||t_n| <= (6g-1) eps_n/4 + (6g-1) eta_n/4 = o(|t_n|)`, which is impossible since `k != 0`. Also `eps_n -> 0`.

**Item 4 (floor).** Suppose `liminf f_W(t)/|t| < a < 4|k|/(6g-1)`. Choose `t_n -> 0` and `t_n`-models with errors
`eta_n < a |t_n|`. Step 2 gives `|kappa_r(U_n)|/d_n >= (|k| - (6g-1) a/4) |t_n|`, which is a positive multiple of
`|t_n|`, and `eps_n <= (a + 2 pi B_W) |t_n|`. So `limsup S_W(eps)/eps > 0`, contradicting `S_W = o(eps)`. Finiteness
of `P_op`: if `P_op = R/Z`, item 3 contradicts `S_W = o(eps)`. By `deligne-sep7-norm-parameter-closed-subgroup`,
the only other closed subgroups containing `1/2` are `(1/m)Z/Z` with `m` even.

**Item 5 (Dadarlat).** `dadarlat-linear-groups-have-nonzero-h2-windings` records asymptotic homomorphisms
`pi_n` of `Sp_4(Z)` with `kappa_r(pi_n) != 0` for large `n`, on a non-torsion class of `H_2`. The class of `r` is
such a class, since `<c, [r]> = k != 0`. Moreover `H_2(Gamma;Q) = Q`, and for an asymptotic homomorphism the
winding is eventually additive on `H_2` and vanishes on torsion, being integer valued. So a nonzero winding on one
non-torsion class gives, after passing to the word for a suitable multiple, a nonzero winding on `[r]`. Since `|kappa| >= 1`, this gives `S_W(eps) >= 1/d_n > 0` along the
sequence, and nothing more. The ratio `S_W(eps_n)/eps_n >= 1/(d_n eps_n)` is bounded below only if
`d_n = O(1/eps_n)`, and the quasidiagonality argument gives no such dimension bound.

**Corollary recorded in the claim's consequences.** Let `D_W(eps)` be the least `d` carrying a nonzero-winding
`eps`-quasi-representation on `W`. Then `S_W(eps) >= 1/D_W(eps)`. So `S_W = o(eps)` forces `eps D_W(eps) -> infinity`.
