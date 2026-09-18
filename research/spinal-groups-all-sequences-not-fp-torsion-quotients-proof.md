---
rg: 2
id: spinal-groups-all-sequences-not-fp-torsion-quotients-proof
kind: route
title: Run the section-cocycle filtration along the shifted systems, one kernel filtration per shift, with a joint induction on length
target: spinal-groups-all-sequences-not-fp-torsion-quotients
requires: []
---

Notation as in `spinal-groups-all-sequences-not-fp-torsion-quotients`. This
is the proof of `self-similar-spinal-groups-not-fp-torsion-quotients-proof`
with one filtration per shift of the system. We give every step.
Automorphisms act on the left, and `(gh)|_x = g|_{h(x)} h|_x`.

## Step 0. One free group for all shifts

`S = (A\1) u (B\1)`, `F = F(S)`, and `s-bar` is the letter of `s` (`1-bar` is
empty). `pi_k: F -> J_k` sends an `A`-letter to its rooted automorphism and
`b-bar` to `b^(k)`. Put `N_k = ker pi_k`. `kappa: F -> A` keeps `A`-letters and
deletes `B`-letters, `F_1 = ker kappa`, and `g(x) := kappa(g)(x)`. Since `B^(k)`
fixes level 1, `pi_k(g)(x) = g(x)`. As `A` acts faithfully on `X`, `N_k <= F_1`.

`M_0` is the normal closure of the multiplication relators
`s-bar t-bar (st)-bar^-1` with `s, t` both in `A` or both in `B`. So
`F/M_0 = A * B`. `M_0 <= N_k` for every `k`, because `b -> b^(k)` is a
homomorphism. `l(g)` is the normal-form length of `g M_0` in `A * B`.

## Step 1. Shifted section cocycles

For `w = s_1^{e_1} ... s_n^{e_n}` and `x in X` put
`x_j = (s_{j+1}^{e_{j+1}} ... s_n^{e_n})(x)`. Set
`beta_k(b, x_0) = rho_{k+1}(b)-bar`, `beta_k(b, y) = omega_{k+1,y}(b)-bar`, and
`Phi^k_x(w) = prod_{j : s_j in B} beta_k(s_j, x_j)^{e_j}`.

(a) *Well defined on `F`.* Cancelling pairs contribute nothing (`A`-letters)
or a cancelling pair at one x-value (`B`-letters, since `kappa(s) = 1`).

(b) *Cocycle.* `Phi^k_x(uv) = Phi^k_{v(x)}(u) Phi^k_x(v)`. So `Phi^k_x` is a
homomorphism on `F_1`.

(c) *Lifting.* `pi_{k+1}(Phi^k_x(w)) = pi_k(w)|_x`. By the product rule it
suffices to check letters. `a|_x = 1` for `a in A`. `(b^(k))|_{x_0} =
(rho_{k+1}(b))^(k+1) = pi_{k+1}(rho_{k+1}(b)-bar)`, and `(b^(k))|_y =
omega_{k+1,y}(b) = pi_{k+1}(omega_{k+1,y}(b)-bar)`, because `A`-letters evaluate
to the same rooted automorphism under every `pi`. Inverses: `b^(k)` fixes
level 1, so `(b^(k))^-1|_x = ((b^(k))|_x)^-1`.

(d) *Length.* `|Phi^k_x(w)| <=` the number of `B`-letters of `w`.

(e) *Surjectivity.* `Phi^k_{x_0}(F_1) M_0 = F`. For `b in B`,
`Phi^k_{x_0}(rho_{k+1}^-1(b)-bar) = b-bar`. For `y != x_0` pick `c in A` with
`c(x_0) = y`. Then `c-bar^-1 b-bar c-bar in F_1` and its image is
`omega_{k+1,y}(b)-bar`. By (S2) these letters generate `F` modulo `M_0`.

## Step 2. The shifted operators

For `M` normal in `F`:
`Theta_k(M) = { w in F_1 : Phi^k_x(w) in M for all x }`.

(i) *Normal subgroup.* It is a subgroup by (b). For `g in F` and `w in F_1`,
(b) gives `Phi^k_x(g w g^-1) = p Phi^k_{g^-1 x}(w) p^-1` with
`p = Phi^k_{g^-1 x}(g)`, because `w(g^-1 x) = g^-1 x` and
`Phi^k_{g^-1 x}(g) Phi^k_x(g^-1) = 1`.

(ii) *Monotone*, and `Theta_k(M) <= (Phi^k_{x_0})^-1(M) n F_1`.

(iii) `M_0 <= Theta_k(M_0)`. `A`-relators are in `F_1` and have empty images.
A `B`-relator `b-bar b'-bar (bb')-bar^-1` is in `F_1` with every x-value equal
to `x`. Its image is `beta_k(b,x) beta_k(b',x) beta_k(bb',x)^-1`, a multiplication
relator of `B` (as `rho_{k+1}` is a homomorphism) or of `A` (as `omega_{k+1,y}`
is one). By (i) this suffices.

(iv) `Theta_k(N_{k+1}) <= N_k`. If `w in F_1` and all `pi_{k+1}(Phi^k_x(w)) =
pi_k(w)|_x` are trivial, then `pi_k(w)` fixes level 1 with trivial sections.

**Definition.** `M^(k)_0 = M_0` and `M^(k)_{j+1} = Theta_k(M^(k+1)_j)`, for all
`k, j >= 0`. So `M^(k)_j = Theta_k Theta_{k+1} ... Theta_{k+j-1}(M_0)`, which
involves only `(rho_n, omega_n)` for `k < n <= k+j`. The theorem's `M_j` is
`M^(0)_j`.

*Increasing.* By (iii), `M^(k)_0 <= M^(k)_1` for all `k`. If
`M^(k+1)_{j-1} <= M^(k+1)_j`, then (ii) gives `M^(k)_j <= M^(k)_{j+1}`. Induct on `j`.

*Bounded.* `M^(k)_0 <= N_k` for all `k`. If `M^(k+1)_j <= N_{k+1}`, then (ii)
and (iv) give `M^(k)_{j+1} <= N_k`.

## Step 3. `U_j M^(k)_j = N_k` for every `k`

By strong induction on `L`, we show: for all `k`, every `w in N_k` with
`l(w) = L` lies in some `M^(k)_j`. Let `w'` be the normal-form word of `w`.

- `L = 0`: `w in M_0`.
- `L = 1`: `w'` is one letter. An `A`-letter is a nontrivial permutation, and a
  `B`-letter is nontrivial in `J_k` by (S1). So `w not in N_k`, and this case does
  not occur.
- `L >= 2`: `w' in N_k <= F_1`. By (c) and `pi_k(w') = 1`, `Phi^k_x(w') in N_{k+1}`.
  By (d) and alternation of normal forms, `l(Phi^k_x(w')) <= ceil(L/2) < L`.
  By induction, applied at shift `k+1`, `Phi^k_x(w') in M^(k+1)_{j_x}`. With
  `j = max_x j_x`, `w' in Theta_k(M^(k+1)_j) = M^(k)_{j+1}`, so
  `w in w' M_0 <= M^(k)_{j+1}`.

## Step 4. Infinite order and free subgroups at every stage

Claim: for all `k, j`, `F/M^(k)_j` has an element of infinite order, and a
non-abelian free subgroup unless `|A| = |B| = 2`. For `j = 0` this holds for
`A * B`: `A != 1` by transitivity, and `B != 1` by (S2) (a trivial `B` would
give trivial `omega`s, which cannot generate `A != 1`).

Step `j -> j+1` at shift `k`. By (ii), `Phi^k_{x_0}` induces a homomorphism
`psi: F_1 / M^(k)_{j+1} -> F / M^(k+1)_j`, and by (e) its image contains every
coset `g M^(k+1)_j` (use `M_0 <= M^(k+1)_j`). If `g` has infinite order modulo
`M^(k+1)_j`, pick `h in F_1` with `psi(h) = g`; then `h` has infinite order modulo
`M^(k)_{j+1}`. If `u, v` freely generate a free subgroup modulo `M^(k+1)_j`,
pick `h_u, h_v` with `psi(h_u) = u` and `psi(h_v) = v`. Then `<h_u, h_v>` maps onto
a free group of rank 2 with the generators going to a basis, so it is free
of rank 2.

## Step 5. Consequences

*Finitely presented covers.* Let `P = F(Y)/<<R>>` be finitely presented and
`p: P -> J_0` onto. Choose `lambda: F(Y) -> F` with `pi_0(lambda(y)) = p(y)`,
and `mu(s) in F(Y)` with `p(mu(s)) = pi_0(s-bar)`. The finite set
`lambda(R) u { s-bar^-1 lambda(mu(s)) }` lies in `N_0`, hence in some `M^(0)_j` by
Step 3 and Step 2 (increasing). So `lambda` induces a surjection
`P -> F/M^(0)_j`. By Step 4, `P` has an element of infinite order and, unless
`|A| = |B| = 2`, a non-abelian free subgroup (lift a basis). These are items 1 and 2.

*Marked limit.* `M^(0)_j` increases to `N_0`, so `F/M^(0)_j -> J_0` in the space
of marked groups. That is item 3. []

## Checks

- *Constant system.* `Theta_k` does not depend on `k`, `M^(k)_j = M_j` of
  `self-similar-spinal-groups-not-fp-torsion-quotients-proof`, and the proof
  reduces to it.
- *Where (S1) is used.* Only in the case `L = 1`, and at every shift `k`,
  because the induction in Step 3 passes from shift `k` to shift `k+1`. For
  eventually constant `omega` in the `G_omega` family some letter dies at a
  late shift, the base `A * B` is wrong there, and the argument does not apply.
- *Grigorchuk `G_omega`.* `omega_{n,0}` is a homomorphism `V_4 -> C_2` and
  `rho_n = id`. So `(b^(k))|_1 = b^(k+1)` and `(b^(k))|_0 = omega_{k+1,0}(b)`,
  which is Grigorchuk's recursion `b_omega = (u_{omega_1}(b), b_{sigma omega})`,
  with the spine at `x_0 = 1`.
- *Computation.* `experiments/spinal-section-cocycle-2026-09-17/check_omega.py`
  checks (c) and (d) for random `G_omega` on random words to depth 8
  (`results_omega.txt`), and fails when the shift `k+1` in (c) is replaced by `k`.
