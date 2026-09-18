---
rg: 2
id: corona-fixed-projection-membership-is-finite-markov-gap-proof
kind: route
title: Diagonalize almost-invariant vectors orthogonal to Fix(L) across coordinates into one exactly invariant vector that the lift of P_L kills
target: corona-fixed-projection-membership-is-finite-markov-gap
requires: []
---

Notation is that of the target. Write `U_f=pi(sigma~(f))` and, on `H_omega`,
`U^omega_f=pi_omega(sigma~(f))`.

## Step 0: preliminaries

- *`sigma~` is a unitary representation of `G` into `B`.* Each `Ad V_n(g)` is
  within `2||V_n(g)-W||_op` of the unitary `Ad W` on `(M_(d_n),||.||_2)` for
  the polar part `W` of `V_n(g)`, and
  `||Ad A - Ad A'|| <= (||A||+||A'||) ||A-A'||_op`. Asymptotic
  multiplicativity in operator norm therefore gives
  `sigma~(gh)=sigma~(g)sigma~(h)` and `sigma~(g^(-1))=sigma~(g)^*` in `B`.
- *`pi` is faithful.* If `b=[T_n]` and `||T_n||` does not tend to `0`, pick an
  infinite set `I` with `||T_n||>=c` on `I`, unit `x_n` with
  `||T_n x_n||>=c/2`, and a free ultrafilter containing `I`. Then
  `||pi_omega(b)[x_n]||>=c/2`. So spectra of elements of `B` agree with
  those of their images under `pi`.
- *Reduction to coordinates.* Each `H_omega` reduces `pi(B)`. Hence
  `Fix(L)=direct_sum_omega Fix_omega(L)` and
  `Fix(L)^perp=direct_sum_omega Fix_omega(L)^perp`, and if `P_L=pi(b)` then
  `pi_omega(b)` is the projection of `H_omega` onto `Fix_omega(L)`.
- *Strict convexity.* For finite `F` and a unit `xi`,
  `(1/|F|) sum_F U_f xi = xi` iff `U_f xi=xi` for all `f in F`. So
  `ker(1-pi(h_F))=Fix(F)`.

## Step 1: (1) implies (2), by saturation

Let `P_L=pi(b)` with `b=[T_n]`, `sup_n||T_n||<infinity`. Suppose (2) fails.
Enumerate `L={g_1,g_2,...}` and put `F_k={g_1^(+-1),...,g_k^(+-1)}`.

*One coordinate at a time.* Since (2) fails for `F_k` and
`kappa_k=1/(k sqrt(2k))`, there is a unit `xi in Fix(L)^perp` with
`||U_f xi-xi||<kappa_k` for all `f in F_k`. Write `xi=(xi_omega)`. Then

```text
sum_omega sum_(f in F_k) ||U^omega_f xi_omega - xi_omega||^2
   < |F_k| kappa_k^2 <= k^(-2) sum_omega ||xi_omega||^2 ,
```

because `|F_k|<=2k` and `sum_omega ||xi_omega||^2=1`.

So some `omega_k` has `xi_(omega_k) != 0` and, after normalizing, a unit
`eta^k in Fix_(omega_k)(L)^perp` with `||U^(omega_k)_f eta^k - eta^k|| < 1/k`
for every `f in F_k`. By Step 0, `pi_(omega_k)(b) eta^k = 0`.

*Representatives.* Write `eta^k=[eta^k_n]_(omega_k)`. The set

```text
S_k = { n : ||eta^k_n||_2 = 1, ||T_n eta^k_n||<1/k,
            ||Ad V_n(f) eta^k_n - eta^k_n||_2 < 1/k for all f in F_k }
```

lies in `omega_k`. Here each nonzero `eta^k_n` is first divided by its norm,
which does not change the class, since `lim_(omega_k)||eta^k_n||=1`. As
`omega_k` is free, `S_k` is infinite.

*Diagonal.* Choose `n_1<n_2<...` with `n_k in S_k`, a free ultrafilter
`omega` containing `{n_k}`, and put `zeta_(n_k)=eta^k_(n_k)`, `zeta_n=0`
otherwise. Then `zeta=[zeta_n]_omega` is a unit vector of `H_omega`.
- For `f=g_j` and every `k>=j`,
  `||Ad V_(n_k)(f)zeta_(n_k)-zeta_(n_k)||<1/k`. So `U^omega_f zeta=zeta` for all
  `f in L`, that is, `zeta in Fix_omega(L)`, and `pi_omega(b)zeta=zeta`.
- But `||T_(n_k)zeta_(n_k)||<1/k`, so `pi_omega(b)zeta=0`.

This contradicts `zeta != 0`. So (2) holds.

## Step 2: (2) implies (3) implies (4) implies (1)

Assume (2) with `F`, `kappa`, and put `c=kappa^2/(2|F|)`. Since `F` is symmetric,
`pi(h_F)` is self-adjoint, and it commutes with `P_L`.
- On `Fix(L)` it is the identity.
- For `xi in Fix(L)^perp`:
  `<pi(h_F)xi,xi> = 1 - (1/(2|F|)) sum_F ||U_f xi-xi||^2 <= (1-c)||xi||^2`.
  So `sp(pi(h_F)|Fix(L)^perp) subset [-1,1-c]`, and by faithfulness
  `sp(h_F) subset [-1,1-c] union {1}`.
- `Fix(F) cap Fix(L)^perp=0`, and both summands reduce `U_f`. So `Fix(F)=Fix(L)`.
  This is (3).

Given (3), the indicator `chi_{1}` is continuous on `sp(h_F)`, so
`p=chi_{1}(h_F) in C*(sigma~(<F>))`. By Step 0, `pi(p)` is the projection onto
`ker(1-pi(h_F))=Fix(F)=Fix(L)`, that is, `pi(p)=P_L`. This is (4), and (4)
implies (1) trivially. `QED`

## Step 3: the consequences

- *Non-group sources.* By (1) implies (4), `P_L in pi(B)` already gives
  `P_L in pi(C*(sigma~(L)))`. For any `K` with `L<=K` this is contained in
  `pi(A_K)`. In particular, for the Jacobson column `N` of
  `root-column-fixed-projection-is-not-in-root-pair-cstar`, whose theorem
  excludes `P_N` from `pi(A_K)`, it follows at once that `P_N notin pi(B)`
  under the hypotheses (K1)-(K3) there.
- *Locally finite `L`.* The group `L_0=<F>` is finite. So `P_L=P_(L_0)` is the
  average `(1/|L_0|) sum_(l in L_0) sigma~(l)`, since `sigma~|L_0` is a
  genuine unitary representation of a finite group. Conversely,
  `Fix(L)=Fix(L_0)` for a finite `L_0` gives `P_L in B` by the same formula.

*What the argument uses.* It uses only that `B` is a bounded-sequence corona
and `H_B` includes every free ultrafilter, which is how the diagonal escapes
the dependence of `omega_k` on `k`. It uses no property of `G`, `L` or the
model.
