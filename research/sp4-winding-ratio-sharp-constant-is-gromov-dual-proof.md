---
rg: 2
id: sp4-winding-ratio-sharp-constant-is-gromov-dual-proof
kind: route
title: Telescope the relator into conjugated defects, take Tr log, and dualize the rephasing LP against l1 cycles
target: sp4-winding-ratio-sharp-constant-is-gromov-dual
requires:
  - sp4-quasirep-windings-budget-and-saturation
  - deligne-sep8-first-order-tensor-threshold
  - deligne-sep7-norm-parameter-closed-subgroup
  - sp4-fd-projective-multiplier-is-finite
  - sp2g-central-commutators-of-universal-lifts-are-torsion
---

Notation as in the claim. "Defect `eps` on `W`" means `||pi(g)pi(h) - pi(gh)|| <= eps` for `(g,h)` in `W`. For
unital `pi`, `D(g,h) = I` whenever `g = e` or `h = e`, so degenerate pairs carry no defect and `beta_pi` is normalized.

## Step 0: the relator cycle

`d c_r`:
- `sum_{j<4g} d[p_j|y_(j+1)] = sum_{j<4g} ([p_j] + [y_(j+1)] - [p_(j+1)]) = sum_j [y_j] - [p_(4g)]`, and
  `p_(4g) = e`, so this is `sum_j [y_j]`.
- `sum_i (d[a_i|a_i^-1] + d[b_i|b_i^-1]) = sum_i ([a_i] + [a_i^-1] + [b_i] + [b_i^-1])`, which is the same sum.

So `d c_r = 0`.

`<b, c_r> = k`: in `E_infinity`, `(g,0)^(-1) = (g^-1, -b(g,g^-1))` (Step 1 of
`sp4-quasirep-windings-budget-and-saturation-proof`). Multiplying the `4g` lifted letters left to right accumulates
`b(p_j, y_(j+1))` at each product. The starred letters contribute `-b(a_i,a_i^-1)` and `-b(b_i,b_i^-1)`. The product
is `zeta^k`, so `k = <b, c_r>`.

`c_r` is supported on `W_r`, and `||c_r||_1 <= 6g-1`.

## Step 1: Tr log is additive on near-identity products (Lemma L)

**Lemma L.** Let `U_1, ..., U_n` be unitaries with `sum_m ||U_m - I|| < 2`. Then
`Tr log(U_1 ... U_n) = sum_m Tr log U_m`, with principal logarithms throughout.

*Proof.*
1. Write `U_m = exp(i H_m)`, with `H_m` Hermitian and spectrum in `(-pi, pi)`. Let `th_m = ||H_m||`, so
   `||U_m - I|| = 2 sin(th_m/2)`.
2. For `s` in `[0,1]`, `||exp(i s H_m) - I|| = max 2|sin(s phi/2)| <= 2 sin(th_m/2)`, the max over eigenvalues
   `phi` of `H_m`. So `U(s) = prod_m exp(i s H_m)` satisfies `||U(s) - I|| <= sum_m ||U_m - I|| < 2`.
3. Then `U(s)` never has eigenvalue `-1`, and `s -> Tr log U(s)` is continuous.
4. `exp(Tr log U(s)) = det U(s) = exp(i s sum_m Tr H_m)`. So `Tr log U(s) - i s sum_m Tr H_m` is a continuous
   function with values in `2 pi i Z`. It vanishes at `s = 0`, hence at `s = 1`.

Also `Tr log (V U V^*) = Tr log U` and `Tr log U^* = -Tr log U` when `-1` is not an eigenvalue. QED

## Item 1: the exact winding formula

Let `pi` be unital with defect `eps` on `W_r`. Write `Q_j = pi(y_j)` for an unstarred letter and `Q_j = pi(x)^*`
for a starred letter `y_j = x^-1`, so that `W_r(pi) = Q_1 ... Q_(4g)`.

*Starred letters.* `D(x,x^-1) = pi(x) pi(x^-1)`, so
`pi(x)^* = pi(x^-1) D(x,x^-1)^* = Ad(pi(x^-1))(D(x,x^-1)^*) pi(x^-1)`.

*Chain.* Moving every such conjugated factor to the left, past the preceding `pi(y)`s, only conjugates it further.
This gives `W_r(pi) = [prod of 2g unitary conjugates of D(x,x^-1)^*] . pi(y_1) ... pi(y_(4g))`. By induction,
`pi(y_1) ... pi(y_j) = D(p_1,y_2) ... D(p_(j-1),y_j) pi(p_j)`, and `pi(p_(4g)) = pi(e) = I`.

So `W_r(pi)` is a product of `6g-1` unitaries. Each is a unitary conjugate of `D(q_m)^(sigma_m)`, where the pairs
`q_m` and signs `sigma_m` are exactly the terms of `c_r`.

Each factor is within `eps` of `I`. If `(6g-1) eps < 2`, Lemma L applies. It gives `||W_r(pi) - I|| < 2`, so
`kappa_r` is defined, and

```text
kappa_r(pi) = (1/2 pi i) sum_m sigma_m Tr log D(q_m) = d <beta_pi, c_r>.
```

## Item 2: the determinant cocycle

*Cocycle identity.* For all `g, h, l`, pure algebra gives
`D(g,h) D(gh,l) = pi(g)pi(h)pi(l)pi(ghl)^* = Ad(pi(g))(D(h,l)) D(g,hl)`.

Let `(g,h,l)` be in `T(W)` and `eps < 1`. Each side is a product of two unitaries within `eps` of `I`, so Lemma L
applies to each side. Taking Tr log gives `beta(g,h) + beta(gh,l) = beta(h,l) + beta(g,hl)`, which is
`delta beta_pi(g,h,l) = 0`. Degenerate faces have `D = I`, consistent with normalization.

*Bound.* The eigenvalues `exp(i phi)` of `D(g,h)` satisfy `2|sin(phi/2)| <= eps`, so `|phi| <= 2 arcsin(eps/2)`.
Hence `|beta_pi| <= a(eps)`.

*Integrality.* `exp(2 pi i d beta_pi(g,h)) = det D(g,h) = det pi(g) det pi(h) / det pi(gh)`. So
`d beta_pi - delta theta` is integer valued.

## Item 3: sharp budget

For `eps < min(1, 2/(6g-1))`, items 1 and 2 show that `beta_pi / a(eps)` is feasible for `N_W`, and
`|kappa_r|/d = |<beta_pi, c_r>|`. The feasible set is symmetric under `beta -> -beta`. So
`|kappa_r(pi)|/d <= a(eps) N_W`.

Since `a(eps)/eps -> 1/(2 pi)`, we get `Theta(W) <= N_W/(2 pi)`. Also:
- `|beta| <= 1` gives `N_W <= ||c_r||_1 <= 6g-1`;
- `arcsin y <= pi y/2` on `[0,1]` gives `a(eps) <= eps/4`.

## Item 4: duality and the l1 constant

**(a) LP duality.** `beta*_W` is the `l_infinity` distance on `W` from `b|W` to the subspace
`L = { (delta psi)|W }`, a finite-dimensional problem. So the minimum is attained. By finite-dimensional
`l_infinity`/`l_1` duality (Hahn-Banach, equivalently LP duality), it equals `max { <b,z> : z in L^perp, ||z||_1 <= 1 }`.
Now `z` in `L^perp` means `<psi, d z> = <delta psi, z> = 0` for every normalized `psi`, that is, `d z = 0`.

**(b) `H_2` is a line spanned by `[c_r]`.** `sp4-fd-projective-multiplier-is-finite` gives
`H_2(Gamma;Z) = Z + F` with `F` finite. By universal coefficients over the flat module `R`,
`H_2(Gamma;R) = R`. The normalized bar complex computes it. `[c_r] != 0` because `<b, c_r> = k != 0` and `b` is a
cocycle. So every real cycle `z` has `[z] = mu(z) [c_r]`, and then `<b,z> = mu(z) k`.

**(c) `nu > 0`.**
1. *Import.* The Ben Simon--Burger--Hartnick--Iozzi--Wienhard import, verbatim below, gives a homogeneous
   quasimorphism `f` of `G^`, the universal cover of `Sp_4(R)`, with defect `D_f < infinity` and
   `f(zeta_0) = c_0 != 0` on a generator `zeta_0` of `ker(G^ -> G)`. This is the `Use` paragraph of
   `sp2g-central-commutators-of-universal-lifts-are-torsion-proof`.
2. *Restriction to `E_infinity`.* Since `b` represents the actual universal-cover extension
   (`deligne-sep7-norm-parameter-closed-subgroup`), `E_infinity` is the preimage of `Gamma` in `G^`, with `zeta` a
   generator of `ker`, so `f(zeta) = c = +-c_0 != 0`.
3. *Central shift.* A homogeneous quasimorphism is additive on commuting pairs: `n |f(xy) - f(x) - f(y)| <= D_f`
   when `xy = yx`. `zeta` is central, so `f(zeta^m x) = m c + f(x)`.
4. *A bounded representative.* Put `s(g) = f((g,0))`, so `s(e) = 0`. Since `(g,0)(h,0) = zeta^(b(g,h)) (gh,0)`,
   the quasimorphism inequality reads `|c b - delta s| <= D_f`. So `phi = b - delta s / c` is a normalized real
   cocycle with `||phi||_inf <= D_f/|c|`.
5. *Lower bound.* For `z` homologous to `c_r`, `k = <b, c_r> = <phi, c_r> = <phi, z> <= ||phi||_inf ||z||_1`.
   Coboundaries pair to zero with cycles, and cocycles pair to zero with boundaries. So `nu >= |k||c|/D_f > 0`.
6. `nu <= ||c_r||_1 < infinity`.

**(d) `beta*_W` increases to `|k|/nu`.**
- *Monotone.* A larger `W` only adds constraints to the minimization, so `beta*_W` is nondecreasing.
- *Upper bound.* For feasible `z` in (a), with `mu = mu(z)`: if `mu = 0` then `<b,z> = 0`. Otherwise `z/mu` is
  homologous to `c_r`, so `||z||_1 >= |mu| nu`, and `<b,z> = mu k <= |k| ||z||_1 / nu <= |k|/nu`.
- *Lower bound.* Given `z` homologous to `c_r` with `||z||_1 <= nu + eta`, the cycle `sgn(k) z/||z||_1` is feasible
  for every `W` containing `supp z`. It has value `|k|/||z||_1 >= |k|/(nu + eta)`.
- *Positive.* `beta*_W >= |k|/||c_r||_1 > 0`, taking `z = sgn(k) c_r/||c_r||_1`.

**(e) `N_W` decreases to `nu`.**
- *Monotone.* Restricting a local cocycle on `W'` containing `W` to `W` gives a local cocycle on `W`, since
  `T(W)` is contained in `T(W')`. So `N_W` is nonincreasing.
- *`N_W >= |k|/beta*_W`.* Take `psi*` optimal. Then `beta = sgn(k)(b + delta psi*)/beta*_W` is a global, hence
  local, cocycle with `|beta| <= 1` on `W`, and `<beta, c_r> = |k|/beta*_W`, because `<delta psi*, c_r> = 0`.
- *`|k|/beta*_W >= nu`,* by (d).
- *Upper bound.* Let `z` be homologous to `c_r` with `c_r = z + d u`, where `u` is a finitely supported normalized
  3-chain. Take `W` containing `supp c_r`, `supp z` and every nondegenerate face of every triple in `supp u`. Then
  `supp u` lies in `T(W)`. For every local cocycle `beta` on `W` with `|beta| <= 1`,
  `<beta, c_r> = <beta, z> + <delta beta, u> = <beta, z> <= ||z||_1`. So `lim N_W <= nu`.

**(f) Independence of `r`.** `nu/|k| = inf_z ||z||_1 / |<b,z>|` over cycles with `<b,z> != 0`, by (b).

## Item 5: sharp saturation

Suppose `P_op = R/Z`, and let `W` contain `W_r`.
1. *Models.* By assertion 3 of `deligne-sep8-first-order-tensor-threshold`, there are `t_n -> 0`, `t_n != 0`, and
   unital `U_n` with `||U_n(g)U_n(h) - exp(2 pi i t_n b(g,h)) U_n(gh)|| <= eta_n` on the finite set `W`, where
   `eta_n = o(|t_n|)`.
2. *Rephasing.* Put `U'_n(g) = exp(2 pi i t_n psi*(g)) U_n(g)`, which is unital because `psi*(e) = 0`. Then
   `U'_n(g)U'_n(h) = exp(2 pi i t_n (psi*(g) + psi*(h))) U_n(g) U_n(h)`. So
   `||U'_n(g)U'_n(h) - exp(2 pi i t_n (b + delta psi*)(g,h)) U'_n(gh)|| <= eta_n` on `W`.
3. *Plain defect.* The plain defect of `U'_n` on `W` is at most
   `eps_n := eta_n + max_W |exp(2 pi i t_n (b + delta psi*)) - 1| <= eta_n + 2 pi |t_n| beta*_W`.
4. *Winding.* Scalars cancel in commutators, so `W_r(U'_n) = W_r(U_n)` and `kappa_r(U'_n) = kappa_r(U_n)`. By
   item 2 of `sp4-quasirep-windings-budget-and-saturation`, for large `n`,
   `|kappa_r(U_n)|/d_n >= |k||t_n| - (6g-1) eta_n / 4`.
5. *Ratio.* `S_W` is nondecreasing in `eps`, so
   `S_W(eps_n)/eps_n >= (|k||t_n| - o(|t_n|)) / (2 pi beta*_W |t_n| + o(|t_n|)) -> |k|/(2 pi beta*_W)`.
   Here `eps_n -> 0` and `eps_n > 0`, since `beta*_W > 0` and `t_n != 0`.

## Items 6 and 7

`S_W` is nonincreasing in `W`, so `Theta(W)` is nonincreasing in `W` and `Theta_inf` exists.

*Item 6.* Item 3 gives `Theta_inf <= lim N_W/(2 pi) = nu/(2 pi)`. If `P_op = R/Z`, the chain
`nu <= |k|/beta*_W` (item 4(e)), then item 5, then item 3, gives the displayed inequalities, and both ends converge
to `nu/(2 pi)`.

*Item 7.* This is the contrapositive of item 5, followed by `deligne-sep7-norm-parameter-closed-subgroup`: the closed
subgroups other than `R/Z` that contain `1/2` are `(1/m)Z/Z` with `m` even. If `Theta_inf < nu/(2 pi)`, some `W`
has `Theta(W) < nu/(2 pi) <= |k|/(2 pi beta*_W)`.

## Item 8: the determinant relaxation

*Upper bounds.* `S_W <= R_W`: by items 1 and 2, the data `(beta_pi, theta, n)` of any `pi` with defect `eps` on `W`
are feasible, and `|kappa_r|/d = |<beta_pi, c_r>|`. `R_W <= a(eps) N_W`: `beta/a(eps)` is feasible for `N_W`.

*Lower bound.* Take `d >= 1`, `lambda = floor(d a(eps)/beta*_W)/d`, and put:
- `beta = lambda (b + delta psi*)`;
- `n = d lambda b`, integral because `d lambda` and `b` are;
- `theta = d lambda psi*`, which is normalized.

Then:
- `beta` is a genuine cocycle;
- `|beta| <= lambda beta*_W <= a(eps)` on `W`;
- `d beta = delta theta + n`;
- `<beta, c_r> = lambda k`.

Letting `d -> infinity` gives `R_W(eps) >= |k| a(eps)/beta*_W`. Dividing by `eps` and letting `eps -> 0` gives the
threshold `|k|/(2 pi beta*_W)` of item 7.

*Realization when `P_op = R/Z`.* In item 5, `D'(g,h) = U'_n(g)U'_n(h)U'_n(gh)^*` is within `eta_n` of the scalar
`exp(2 pi i t_n (b + delta psi*)(g,h))`. For large `n` its eigenvalue angles lie within `2 arcsin(eta_n/2)` of
`2 pi t_n (b + delta psi*)(g,h)`, which is small. So
`beta_(U'_n) = t_n (b + delta psi*) + O(eta_n) = t_n (b + delta psi*) + o(|t_n|)` on `W`. These are the extremal
data of the lower bound, with `lambda = t_n`.

*Consequence.* Suppose an argument bounds `|kappa_r(pi)|/d` using only properties of the scalar data
`(d, eps, beta_pi, theta, n)` that the data `lambda (b + delta psi*)` also have. Then its bound is at least
`R_W(eps)`, so its ratio bound is at least `|k|/(2 pi beta*_W)`. It therefore cannot establish the hypothesis of
item 7, nor `S_W = o(eps)`. Such arguments include:
- the Tr log and determinant of the defects;
- `K_1` classes of the word, which are determined by the determinant for unitary matrices;
- any integrality of `kappa_r`.

## Import (verbatim)

The quotation below was read by `sp2g-central-commutators-of-universal-lifts-are-torsion-proof`: G. Ben Simon,
M. Burger, T. Hartnick, A. Iozzi, A. Wienhard, *On weakly maximal representations of surface groups*,
arXiv:1305.2620v2, pages 8--10.

- **p. 8, (3.6)--(3.8).** "Then f′nκ(g,m) = (1/n)m is a Borel quasimorphism such that df′nκ represents p∗nκ(κ).
  Its homogenization fnκ : Gnκ → R is a continuous homogeneous quasimorphism [13, Lemma 7.4] such that (3.7)
  [dfnκ] = p∗nκ(κ), and (3.8) fnκ(i(m)) = (1/n)m."
- **p. 10, §3.3.** "Since π1(G) is isomorphic to Z modulo torsion, there is a unique connected central Z-extension
  Ĝ and, as a result, the connected component of the identity (Gκ)◦ is isomorphic to Ĝ. We denote by fĜ : Ĝ → R the
  continuous homogeneous quasimorphism corresponding to fκ under this isomorphism".

The claim node records how it applies to `Sp_(2g)(R)`, including `g = 2`, and that `f(zeta_0) != 0`.
