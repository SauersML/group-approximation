---
rg: 2
id: deligne-sp2g-covers-not-mf-from-operator-hs-stability
kind: route
title: Round the mark to exact order, compress to a nontrivial eigenspace, round the compression through the universal-cover lattice, and apply Malcev
target: deligne-sp2g-covers-mf-radical-is-2z-at-genus-three
requires: [sp2g-universal-cover-lattice-is-operator-hs-stable, deligne-covers-of-sp2g-z-have-finite-residual-2z, finitely-generated-linear-groups-are-residually-finite]
---

Notation of the target. `q : Gamma~ -> Gamma_n` is the quotient by `<z^n>`. An operator-norm
asymptotic homomorphism satisfies `||phi_k(x)phi_k(y) - phi_k(xy)||_op -> 0` for all `x, y`.
Norms: `||.||_HS <= ||.||_op`.

**Step 0.** `phi_k(1)` is unitary and `||phi_k(1)^2 - phi_k(1)||_op -> 0`, so `phi_k(1) -> I`.
Telescoping over `J^m = 1` gives `||A_k^m - I||_op -> 0` for `A_k = phi_k(J)`. Since `J` is central,
`||[A_k, phi_k(x)]||_op -> 0` for every `x`.

**Step 1: spectrum near the roots.** Put `eps_k = ||A_k^m - I||_op`. Every eigenvalue `lambda` of
`A_k` has `|lambda^m - 1| <= eps_k`, and by `(R1)` of
`deligne-symplectic-covers-are-not-schatten-approximated-proof` its nearest `m`-th root `f(lambda)`
satisfies `|lambda - f(lambda)| <= eps_k`. Suppose, for contradiction, `||A_k - I||_op >= delta > 0`
along a subsequence. Some eigenvalue has `|lambda_k - 1| >= delta`, so `xi_k = f(lambda_k) != 1`
once `eps_k < delta`. Pass to a subsequence with `xi_k = xi` fixed.

**Step 2: an asymptotically central projection.** Let `r = sin(pi/m)`, half the distance between
distinct `m`-th roots. Fix a continuous `h` on the circle with `h = 1` within `r/2` of `xi` and
`h = 0` outside distance `r` from `xi`. Once `eps_k < r/2`, the spectrum of `A_k` lies in the
`eps_k`-disks around the roots, so `P_k = h(A_k)` is the spectral projection of `A_k` onto
eigenvalues near `xi`. It is nonzero by Step 1, and `||(A_k - xi I) P_k||_op <= eps_k`.
- Approximate `h` uniformly within `eta` by a trigonometric polynomial `p`. For unitary `A` and
  contractive `B`, `||[p(A), B]||_op <= C_p ||[A, B]||_op`, since `[A^j, B]` telescopes into `|j|`
  commutators with `A` and `A^*`.
- So `limsup_k ||[P_k, phi_k(x)]||_op <= 2 eta` for every `eta > 0`, i.e.
  `||[P_k, phi_k(x)]||_op -> 0` for every `x`.

**Step 3: compression (BDL Proposition 2.4, p = infinity, re-derived).** On `V_k = Im P_k` put
`M_k(x) = P_k phi_k(x) P_k`.
- `||M_k(x) M_k(y) - M_k(xy)||_op <= ||phi_k(x)phi_k(y) - phi_k(xy)||_op + ||[phi_k(x), P_k]||_op`,
  which tends to 0. Taking `y = x^(-1)` and using `phi_k(x^(-1)) ~ phi_k(x)^*` gives
  `||M_k(x)^* M_k(x) - I_(V_k)||_op -> 0`.
- Let `psi'_k(x)` be the unitary part of the polar decomposition of `M_k(x)` on `V_k`. Then
  `||psi'_k(x) - M_k(x)||_op = || |M_k(x)| - I ||_op <= ||M_k(x)^* M_k(x) - I||_op -> 0`.
- So `psi'_k : Gamma_n -> U(V_k)` is an operator-norm asymptotic homomorphism, and by Step 2
  `||psi'_k(J) - xi I_(V_k)||_op <= ||P_k A_k P_k - xi P_k||_op + o(1) <= eps_k + o(1) -> 0`.

**Step 4: round through the universal cover.** `psi'_k o q : Gamma~ -> U(V_k)` is an operator-norm
asymptotic homomorphism of `Gamma~`. By `sp2g-universal-cover-lattice-is-operator-hs-stable` there
are genuine `rho_k : Gamma~ -> U(V_k)` with `||rho_k(z^2) - psi'_k(J)||_HS -> 0`.

**Step 5: Malcev.** `z^2` lies in every finite quotient's kernel of `Gamma~`. Indeed, if `z` has order
`n'` in a finite quotient `Q`, then `Q` is a quotient of `Gamma~/<z^(n')>`. For `n' <= 2`, `z^2` dies
trivially. For `n' >= 3`, `z^2` lies in `Res_fin(Gamma_(n'))` by
`deligne-covers-of-sp2g-z-have-finite-residual-2z`. `rho_k(Gamma~)` is finitely generated and linear,
hence residually finite (`finitely-generated-linear-groups-are-residually-finite`). If
`rho_k(z^2) != I`, a finite quotient of `rho_k(Gamma~)`, which is a finite quotient of `Gamma~`, would
separate `z^2`. So `rho_k(z^2) = I`.

**Step 6: contradiction.** `|1 - xi| = ||I - xi I_(V_k)||_HS <= ||rho_k(z^2) - psi'_k(J)||_HS +
||psi'_k(J) - xi I||_op`, and both terms tend to 0. But `xi != 1`. Hence `||phi_k(J) - I||_op -> 0`
for every operator-norm asymptotic homomorphism, i.e. `J = z^2 in Rad_MF(Gamma_n)`, and `Gamma_n` is
not MF.

**Equality.** Every finite quotient is an exact operator-norm model, so `Rad_MF(Gamma_n)` lies in
`Res_fin(Gamma_n) = <z^2>` (equation `(DR2)` of the finite-residual citation). With Step 6 this gives
`Rad_MF(Gamma_n) = <z^2>`.

**Scope.**
- `g >= 3` enters only through the hypothesis, which is where `[T_2]` makes it an instance of BDL
  Conjecture 1.8.
- Steps 0--6 work for any central extension `1 -> Z -> G~ -> G -> 1` with `G~` operator-HS-stable
  and `z^2` in its finite residual. This is how BDL's Proposition 1.5 extends from order two to every
  order and from the group itself to its `[T_2]` cover.
