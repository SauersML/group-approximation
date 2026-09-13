---
rg: 2
id: leavitt-units-of-infinite-order-have-linear-depth-growth
kind: claim
title: Every infinite-order unit of the binary Leavitt algebra over F_2 has linearly growing depth
distinct_from:
  thompson-elements-are-undistorted-in-leavitt-unit-group: that proves linear depth growth for units conjugate into V through germs at periodic points; this asks it for every unit, including linear units with no point dynamics.
  leavitt-unit-group-has-no-integer-heisenberg-subgroup: that is one subgroup obstruction; this is a uniform metric statement about all cyclic subgroups, which implies it and also excludes BS(1,k).
---

**OPEN.** Let `R = L_(F_2)(1,2)` with `t_i s_j = delta_ij` and `s_0 t_0 + s_1 t_1 = 1`, and
`Q = R^x`. Put `R_N = span{ S[alpha]T[beta] : |alpha|, |beta| <= N }` and
`ell(x) = min{ N : x in R_N }`. Since `R_N R_M <= R_(N+M)`, the function
`D_u(m) = max(ell(u^m), ell(u^-m))` is subadditive in `m`, and
`lambda(u) = lim_m D_u(m)/m` exists for every `u` in `Q`.

**Claim.** `lambda(u) > 0` for every `u` in `Q` of infinite order.

**Consequences.**
- Every infinite cyclic subgroup of `Q` is undistorted, since `|u^m|_S >= ell(u^m)/L_S` for a finite
  generating set `S` with `L_S = max(1, max_(s in S) ell(s))`.
- `Q` has no subgroup `H_3(Z)` and no `BS(1,k)` with `|k| >= 2`
  (`no-heisenberg-from-linear-depth-growth`). Through
  `kun-thom-wreath-nonembedding-from-no-heisenberg`, no Kun--Thom wreath or double over a
  Theorem E actor embeds in `Q`, for any parameter.
- Known case: units conjugate into `V`
  (`thompson-elements-are-undistorted-in-leavitt-unit-group`).

**Grading.** `deg S[alpha]T[beta] = |alpha| - |beta|` makes `R = ⊕_(k in Z) R_k` a graded algebra.
`R_0 = ⋃_n M_(2^n)(F_2)` is locally finite. Every monomial of depth `N` has degree in `[-N, N]`.

## Attempts

**Top and bottom degree components (proved, partial).** If some power `v = u^k` has a top-degree
component `v_d` with `d > 0` and `v_d` not nilpotent, then `(v^j)_(jd) = v_d^j != 0`, so
`ell(u^(kj)) >= jd` and `lambda(u) >= d/k > 0`. The same holds for bottom components. What remains
are units all of whose powers have nilpotent extreme components. Mod-2 cancellation between monomials
is then not controlled, and this is where the direct argument stops.

**Bounded degree range (partial structure, not a proof).** Suppose every power `u^m`, `m in Z`, has
all its degrees in `[-D, D]`, and `u` has infinite order. Then `A = F_2[u^(+-1)]` is a Laurent
polynomial ring contained in `⊕_(|k| <= D) R_k`, and `A ∩ R_(>=0) = A ∩ R_(<=0) = F_2`.
- `R_(>=0)` is a graded subalgebra, and `x -> x_0` is a ring map `R_(>=0) -> R_0` with kernel `R_(>0)`.
- An element of `A ∩ R_(>0)` has degrees in `[1, D]`, so its `(D+1)`-st power has degrees `>= D+1`
  and lies in `A`, hence vanishes. `A` is a domain, so `A ∩ R_(>0) = 0`.
- So `A ∩ R_(>=0)` embeds in `R_0`. Every element of `R_0` is algebraic over `F_2`, and the only
  algebraic elements of `F_2[x^(+-1)]` are constants.

So a bounded-degree counterexample needs growing spatial resolution with bounded lag, and every
nonconstant element of `A` has both positive and negative components. No contradiction follows yet.

**Counting.** `dim R_N <= 4^(N+1)`. The `2M+1` powers `u^m`, `|m| <= M`, are distinct elements of
`R_(D_u(M))`, so `D_u(M) >= log_4 log_2 (2M+1) - 1`. This is far from linear and does not exclude a
Heisenberg center, whose depth may grow like `sqrt(m)`.

**Frobenius squaring.** In characteristic two, `(1 + x)^(2^k) = 1 + x^(2^k)`, and `lambda(u) = 0` iff
`D_u(2^k) = o(2^k)`. So `k` squarings test the power `2^k`, and a small-depth power is cheap to
store.
- The shape of a counterexample. Let `phi(x) = s_0 x t_0 + s_1 x t_1`, a unital ring endomorphism with
  `ell(phi(x)) <= ell(x) + 1`. A unit `y` with `y^2 = phi(y)` has `y^(2^k) = phi^k(y)`, so
  `D_y(2^k) <= D_y(1) + k` and `lambda(y) = 0`.
- The odometer `O = s_1 t_0 + s_0 O t_1` satisfies `O^2 = phi(O)`, but it is not in `R`: its recursion
  never terminates.
- Whether some finite-depth unit of infinite order obeys a self-similar squaring law of this kind is
  open. It would be a counterexample, a unit of logarithmic depth growth.
