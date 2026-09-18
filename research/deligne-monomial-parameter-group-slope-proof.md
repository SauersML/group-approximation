---
rg: 2
id: deligne-monomial-parameter-group-slope-proof
kind: route
title: Product models make the monomial defect subadditive, the Weil double cover makes it half-periodic, and subadditivity turns the small-parameter slope into a supremum
target: deligne-monomial-parameter-group-is-governed-by-maslov-slope
requires:
  - deligne-covers-of-sp2g-z-have-finite-residual-2z
---

Notation of the target. Write `e(x) = exp(2 pi i x)`. For a phase function `a`, `a~` is a real lift. `delta a~ (x,r)`
is the sum of `+-a~` along the loop that reads `r` from `x`; that loop closes because the action is exact. Its
class mod `Z` is `delta a (x,r)`, and `rho(r~(S)) e_x = e(delta a (x,r)) e_x`.

**Step 1: Diophantine form (item 1).**
- *Upper bound on the norm.* Take a model `a` attaining `mu = mu_theta(X)`. The attainment holds because
  `(R/Z)^(X x S)` is compact and the defect is continuous. Write
  `delta a~ - theta kappa = n + eps`, with `n` an integral 2-cochain and `|eps| = dist(., Z) <= mu` cellwise.
  `Y_X` is 2-dimensional, so every 2-cochain is a cocycle and `H^2 = C^2 / delta C^1`. Hence `eps` represents
  `-(theta kappa_R + u_R)` with `u = [n]`, and `||theta kappa_R + u_R||_cell <= ||eps||_inf = mu`.
- *Reverse bound.* Let `u = [n]` be any integral class, and let `eps'` be any real representative of
  `-(theta kappa_R + u_R)`. Then `eps' + theta kappa + n = delta b` for a real 1-cochain `b`. Put `a = b mod Z`.
  Then `delta a - theta k_r = eps' mod Z` on each cell, so `mu_theta(X) <= ||eps'||_inf`.
- Minimizing over `eps'` and `u` gives equality. `L_X` is a lattice, and the quotient norm on a finite-dimensional
  space attains its infimum, so the minimum is attained.
- *Norm of `kappa`.* Let `pi : Y_X -> P` be the covering of degree `|X|` induced by `X -> pt`. Then `kappa = pi^* kappa`.
  - Pullback of cochains does not increase the sup norm, so `||pi^* c|| <= ||c||`.
  - The transfer `(tr v)(sigma) = sum over the lifts sigma' of v(sigma')` satisfies `||tr v||_inf <= |X| ||v||_inf`
    and `tr pi^* = |X|`. Hence `||c|| <= ||pi^* c||`.
  - So `||kappa_R||_cell(Y_X) = c_K`.

**Step 2: elementary properties of `m` (item 2).**
- *Well defined on `R/Z`.* `theta -> theta + 1` shifts `theta k_r` by an integer.
- *Evenness.* The model `-a` has holonomy `-delta a`, so `mu_(-theta) = mu_theta`.
- *Subadditivity.* Let `X x X'` carry the diagonal action and `a''((x,x'),s) = a(x,s) + a'(x',s)`. The loop reading
  `r` from `(x,x')` projects to the loops from `x` and from `x'`, so `delta a'' = delta a + delta a'`. The triangle
  inequality for `dist(., Z)` gives `mu_(theta+theta')(X x X') <= mu_theta(X) + mu_theta'(X')`. Hence
  `m(theta + theta') <= m(theta) + m(theta')`.
- *Linear bound.* For `theta in [-1/2, 1/2]`, item 1 at `X = pt` with `u = 0` gives
  `m(theta) <= mu_theta(pt) <= |theta| c_K`. Together with subadditivity this gives
  `|m(theta) - m(theta')| <= c_K |theta - theta'|`.
- *Half parameter.* Apply `(DR2)` of `deligne-covers-of-sp2g-z-have-finite-residual-2z` with `g = 2` and `n = 4`.
  Then `Res_fin(Gamma~/<z^4>) = <z^2>`, which does not contain `z`. So there is a finite quotient
  `phi : Gamma~ -> Q` with `c = phi(z) != 1` and `c^2 = 1`; `c` is central.
  - Let `V = { f in l^2(Q) : f(qc) = -f(q) }`. It is invariant under left translation `lambda`.
  - Fix a transversal `T` of `<c>`. Then `{ delta_t - delta_(tc) : t in T }` is a basis of `V`. In this basis each
    `lambda(q)` is a signed permutation over the `Q`-set `X = Q/<c>`.
  - `z` acts on `X` by `c`, which is central, so trivially. Hence `X` is a `Gamma`-set with an exact action, and
    `rho(s) = lambda(phi(s~))|_V` is a monomial model with phases in `{0, 1/2}`.
  - Moreover `rho(r~(S)) = lambda(c)^(k_r)|_V = (-1)^(k_r)`. So `delta a = k_r / 2` exactly, and
    `mu_(1/2)(X) = 0`.
  - Hence `m(1/2) = 0`. Subadditivity then gives `m(theta + 1/2) = m(theta)`.

**Step 3: `P_mon` is a closed subgroup (item 2).**
- The zero set of a nonnegative, even, subadditive function vanishing at `0` is a subgroup.
- It is closed because `m` is Lipschitz, and it contains `1/2` by Step 2.
- The closed subgroups of `R/Z` are `R/Z` and the finite cyclic groups `(1/m)Z/Z`. The finite case has `m` even.

**Step 4: `P_mon <= P_op` (item 2).**
- For each `g` in `Gamma`, fix a word `w_g` in `S`, with `w_e` empty. Define `b` by
  `w_g(S~) w_h(S~) = z^(b(g,h)) w_(gh)(S~)` in `Gamma~`.
  - `b` is a normalized integral cocycle representing the extension `Z -> Gamma~ -> Gamma`.
  - Any other such cocycle differs from `b` by an integral coboundary `delta beta`.
  - Replacing `U(g)` by `e(theta beta(g)) U(g)` absorbs that coboundary, so this is the setting of
    `deligne-sep7-norm-parameter-closed-subgroup`.
- In the free group, `w_g w_h w_(gh)^(-1) = prod_(i <= A) v_i r_i^(eps_i) v_i^(-1)`, with `A = A(g,h)` finite.
  Evaluating in `Gamma~` gives `sum_i eps_i k_(r_i) = b(g,h)`.
- Given a model with `mu_theta(X) = mu`, put `U(g) = rho(w_g)`. Each `rho(r~)` is diagonal, and it lies within
  `2 pi mu` of `e(theta k_r)` in operator norm. Hence
  ```text
  || U(g) U(h) - e(theta b(g,h)) U(gh) ||_op <= 2 pi A(g,h) mu.
  ```
- If `mu_theta(X_n) -> 0`, these maps witness `theta in P_op`, with `d_n = |X_n|`.

**Step 5: slope law (item 3).**
- Regard `m` as a function on `R`. Fix `t > 0` and `0 < tau < t`, and write `t = n tau + r` with `n >= 1` an integer
  and `0 <= r < tau`.
- Subadditivity and the linear bound give `m(t) <= n m(tau) + c_K r <= (t / tau) m(tau) + c_K tau`, so
  ```text
  m(t)/t <= m(tau)/tau + c_K tau / t.
  ```
- Take `liminf` as `tau -> 0+`. This gives `sup_t m(t)/t <= liminf_(tau -> 0) m(tau)/tau`, which is at most the
  `limsup`, which is at most the `sup`. So the limit exists and equals the supremum.
- `s <= c_K` by the linear bound.
- `(MP3)`:
  - If `s = 0`, then `m(t) <= s t = 0` for all `t`, so `P_mon = R/Z`.
  - If `P_mon = R/Z`, then `m = 0`, so `s = 0`.
  - If `m(t_n) = o(t_n)` along some `t_n -> 0+`, then `s = 0`, because the limit exists.

**Step 6: transference (item 4).**
- Evenness and half-periodicity give `m(1/6) = m(1/6 - 1/2) = m(1/3)`.
- For `t in (0, 1/6]`, write `1/6 = n t + r` with `n = floor(1/(6t))` and `0 <= r < t`, as in Step 5. Then
  `m(1/6) <= m(t)/(6t) + c_K t`.
- Finally `m(t) <= mu_t(X)` for every finite `X`.

**Step 7: decomposition and interlock (items 5 and 6).**
- *The floor is `1/6 notin P_mon`.* `F` says `1/3 notin P_mon`. Since `P_mon` is a group containing `1/2`,
  `1/3 in P_mon` iff `1/6 = 1/2 - 1/3 in P_mon`. By Step 3, `1/6 in P_mon` iff either `P_mon = R/Z`, or
  `P_mon = (1/m)Z/Z` with `6 | m`, i.e. with `3 | m` since `m` is even.
- *The split.* By `(MP3)`, "`P_mon = R/Z`" is the failure of (A). So `F` iff (A) and (B).
- *Independence.* The two witnesses in item 5 are consistent with Steps 2-5, and no step decides between them.
- *Interlock with `P_op`.* If `P_op` is finite, then `P_mon <= P_op` is finite; this gives (A). If moreover
  `3` does not divide `|P_op|`, then `1/3 notin P_op`, which contains `P_mon`; this gives `F`, hence (B).
- *The flagship implies `F`.* Suppose `1/3 in P_op` with witnesses `U_n`.
  - On `E_3 = Gamma~ / <z^3>`, written as pairs `(g, j)` with the cocycle `b` mod 3, put
    `U~_n(g, j) = e(j/3) U_n(g)`.
  - Then `U~_n(g,j) U~_n(h,k) - U~_n(gh, j + k + b(g,h)) -> 0` pointwise.
  - This is a norm-matrix-corona representation of `E_3` with `z -> e(1/3) != 1`. So `z notin Rad_MF(E_3)`, and
    `(DER2)` fails.
  - Contrapositively, the flagship gives `1/3 notin P_op`, which contains `P_mon`; that is `F`.

**Step 8: uniform lattice systole (item 7).**
- For `u_R = 0`, item 1 gives `||t kappa_R|| = t c_K`.
- For `u_R != 0`, `||t kappa_R + u_R|| >= sigma - t c_K > t c_K` once `t c_K < sigma / 2`.
- So `mu_t(X) = t c_K` for all small `t` and all `X`, hence `m(t) = c_K t` and `s = c_K`.

**Remark (presentation independence).** `P_mon` does not depend on the finite presentation. Tietze moves change `mu`
by at most a factor `C`:
- *Adding a consequence relator* `r' = prod v_i r_i^(+-1) v_i^(-1)`. It has `k_(r') = sum +- k_(r_i)`, and its
  holonomy defect is at most the sum of the `A'` defects.
- *Adding a generator* `s' = w`. Give it the phase that `w` induces, and choose its lift so that `k_(s' w^-1) = 0`;
  the new relator then has defect `0`.

So `m' <= C m` in both directions, and the zero sets agree. The constants `c_K` and `s` are presentation-dependent,
but whether `s > 0` is not, since `s > 0` iff `P_mon != R/Z`.
