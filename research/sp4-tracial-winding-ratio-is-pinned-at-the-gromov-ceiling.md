---
rg: 2
id: sp4-tracial-winding-ratio-is-pinned-at-the-gromov-ceiling
kind: claim
title: Over all tracial C*-algebras the winding-to-defect ratio of Sp4(Z) maps sits exactly at the l1-dual ceiling, so the winding deficit is a strict matricial-versus-tracial gap
distinct_from:
  sp4-winding-deficit-fails-in-twisted-tracial-algebras: that gives tracial witnesses whose ratio exceeds tau_W at every scale, with no upper bound in the tracial class; this proves the matching tracial upper bound a(eps) N_W (determinant-free Lemma L), so the tracial supremum is pinned between |k| a(eps)/beta*_W and a(eps) N_W and its limit over windows is exactly nu/(2 pi).
  sp4-winding-ratio-sharp-constant-is-gromov-dual: that proves the ceiling nu/(2 pi) for matrices and the all-MF floor; this extends the ceiling to every tracial C*-algebra without integrality and shows the tracial class attains it unconditionally, so the ceiling is a tracial invariant and the deficit is a statement comparing M_d with that class.
  sp4-quasirep-winding-ratio-has-a-deficit: that is the open matricial inequality; this restates it, with no change in strength, as strict inequality between the matricial and the (computed) tracial ratio.
---

**ESTABLISHED** (route `sp4-tracial-winding-ratio-is-pinned-at-the-gromov-ceiling-proof`). Unreviewed. Written
as the small-gap repair of the 2026-09-19 audit by swarm-0917-w18c-w18c-deligne-audit.

**Setting.** Notation of `sp4-winding-ratio-sharp-constant-is-gromov-dual` and
`sp4-winding-deficit-fails-in-twisted-tracial-algebras`: `Gamma = Sp_4(Z)`, relator `r` with lifted value
`zeta^k`, `k != 0`, finite windows `W` containing `W_r`, `a(eps) = (1/pi) arcsin(eps/2)`, `a_g = 1/(6g-1)`, the
LP constants `N_W`, `beta*_W`, `tau_W = |k|/(2 pi beta*_W)`, and `nu = ||[r]||_1`. For a unital C*-algebra `A` with
tracial state `tau`, `S_W^A(eps)` is the tracial winding supremum of the twisted-tracial node. Put

```text
S_W^tr(eps) = sup_(A, tau) S_W^A(eps),    Theta^tr(W) = limsup_(eps -> 0+) S_W^tr(eps)/eps,
Theta^tr_inf = lim_W Theta^tr(W)   (nonincreasing in W).
```

**Theorem.**
1. **Tracial Lemma L.** If `U_1, ..., U_n` are unitaries in `A` with `sum ||U_m - 1|| < 2`, then
   `tau(log(U_1 ... U_n)) = sum_m tau(log U_m)` (principal logarithms). No determinant or integrality is used.
2. **Tracial sharp budget.** For every `(A, tau)` and `0 < eps < min(1, 2/(6g-1))`,
   `S_W^A(eps) <= a(eps) N_W`. In particular this holds for the twisted algebras `A_t`.
3. **Two-sided pinning.** For `0 < eps <= a_g`,

   ```text
   |k| a(eps) / beta*_W   <=   S_W^tr(eps)   <=   a(eps) N_W .
   ```

   The lower bound is attained by the rephased twisted regular unitaries `pi_(t(eps))` in `A_(t(eps))`.
   These are the same two bounds as for the determinant relaxation `R_W(eps)` in item 8 of the sharp-constant node.
4. **The tracial ratio is the ceiling.** `tau_W <= Theta^tr(W) <= N_W/(2 pi)` for every `W`, and
   `Theta^tr_inf = nu/(2 pi)` unconditionally.
5. **Reformulation of the deficit.** `S_W(eps) <= S_W^tr(eps)` because `(M_d, tr/d)` is tracial. Hence:
   - `Theta_inf < nu/(2 pi)` (the window-free form of `sp4-quasirep-winding-ratio-has-a-deficit`) holds iff
     `Theta_inf < Theta^tr_inf`;
   - `P_op = R/Z` forces `Theta(W) >= tau_W`, the tracial lower bound, on every window. So on the all-MF branch
     matrices reach the tracial ratio in the limit, `Theta_inf = Theta^tr_inf`.

**What this changes.**
- The twisted-tracial kill is sharp in both directions: tracial models cannot exceed the matricial ceiling
  `N_W/(2 pi)`, and the scalar-defect witnesses already reach the matricial all-MF floor `tau_W`. So the tracial
  class is not "much larger" than the matricial one in this invariant. It sits exactly at the all-MF value.
- The deficit (and so the winding route to the flagship) is precisely a *strict gap between matrices and tracial
  C*-algebras* for one explicit functional of `Sp_4(Z)`. Any proof must exhibit a matricial loss relative to the
  twisted algebras `A_t` at small `t`. No bound, however sharp, that holds in every tracial algebra can do it.
- Nothing here decides `P_op`, (SSD), or the flagship.
