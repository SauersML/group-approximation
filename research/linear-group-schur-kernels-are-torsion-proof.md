---
rg: 2
id: linear-group-schur-kernels-are-torsion-proof
kind: route
title: Dadarlat's nonzero winding contradicts the vanishing winding on the Schur kernel
target: linear-group-schur-kernels-are-torsion
requires:
  - schur-kernels-are-invisible-to-matricial-windings
  - dadarlat-linear-groups-have-nonzero-h2-windings
---

**Presentation.** Take `S = Gamma` as a set, `F = F(S)`, and
`q : F -> Gamma` the canonical map `q(a) = a-bar`. Let `R = ker q` and
`R_0 = R`. This is a free resolution as in Dadarlat's display (9), and a
presentation as in `schur-kernels-are-invisible-to-matricial-windings`. The
Theorem there allows infinite `S` and `R_0`.

Suppose, for a contradiction, that `x in K_2(Gamma, w)` is non-torsion.
Write `h = prod_{i=1}^g [a_i, b_i]` with `a_i, b_i in F`, `h in R`. This is
a Hopf word for `x`.

**Step 1 (vanishing).** By the Theorem of
`schur-kernels-are-invisible-to-matricial-windings`, there are a finite
`P subset R` and `delta > 0` such that `kappa(rho, h) = 0` for every `d` and
every `rho : S -> U(d)` with `delta_P(rho) < delta`.

**Step 2 (detection).** By `dadarlat-linear-groups-have-nonzero-h2-windings`,
there is a unital asymptotic homomorphism `pi_n : Gamma -> U(k_n)` with
`kappa(W_n) != 0` for all large `n`, where
`W_n = prod_i [pi_n(a_i-bar), pi_n(b_i-bar)]` and `||W_n - 1|| < 2`.

**Step 3 (comparison).** Put `rho_n = pi_n|_S`, extended multiplicatively to
`F`. For a word `a = s_1^{e_1} ... s_k^{e_k}`, we have `pi_n(1) = 1` and
`||pi_n(s^{-1}) pi_n(s) - 1|| -> 0`, so `pi_n(s^{-1}) -> pi_n(s)^*` in norm.
Induction on `k` with asymptotic multiplicativity gives

    ||rho_n(a) - pi_n(a-bar)|| -> 0     for each fixed a in F.     (C)

*Defects.* For `r in P` we have `r-bar = 1`. By (C),
`||rho_n(r) - 1|| -> 0`, so `delta_P(rho_n) < delta` for large `n`, and
Step 1 gives `kappa(rho_n, h) = 0`.

*Deformation.* Put `A_i^0 = pi_n(a_i-bar)` and `A_i^1 = rho_n(a_i)`. Set
`A_i(u) = A_i^0 exp(u log((A_i^0)^* A_i^1))` for `u in [0,1]`, and define
`B_i(u)` in the same way. This is well defined for large `n` by (C). Then
`||A_i(u) - A_i^0|| <= (pi/2) ||A_i^1 - A_i^0||`, and the same bound holds
for `B_i`. Put `W(u) = prod_i [A_i(u), B_i(u)]`. It is continuous in `u`
and unitary with `det W(u) = 1`, and

    ||W(u) - 1|| <= ||W_n - 1|| + 4 g (pi/2) max_i max(||A_i^1 - A_i^0||, ||B_i^1 - B_i^0||).

Here `||W_n - 1|| -> 0` by the comparison step of the imported claim, and
the second term tends to `0` by (C). So for large `n`, `W(u)` stays in
`{||W - 1|| < 2}` for all `u`. There `kappa` is continuous and integer-valued,
so `kappa(W(0)) = kappa(W(1))`. That is, `kappa(W_n) = kappa(rho_n, h)`.

The left side is nonzero by Step 2 and the right side is zero by the
Defects paragraph. This is a contradiction, so `K_2(Gamma, w)` consists of
torsion. ∎

**Rig.** The same comparison shows that a non-torsion class is not rigid.
Together with "torsion is rigid" from the imported claim, this gives
`Rig(Gamma) = Tors H_2(Gamma; Z)`.
