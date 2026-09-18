---
rg: 2
id: kazhdan-certified-tables-not-order-realizable-proof
kind: route
title: The Ozawa identity is pushed forward along any realization of the ball, and (T) kills local indicability
target: kazhdan-certified-tables-not-order-realizable
requires: [orderable-nonsofic-iff-order-realizable-forbidden-table]
---

Notation as in [[kazhdan-certified-tables-not-order-realizable]].  Let `f : F -> H` embed `T`, where
`F contains B_R(Gamma)`.

**Step 1: words are evaluated consistently.**  `1 in B_R` and `1 * 1 = 1` is a defined product, so
`f(1)^2 = f(1)` and `f(1) = 1`.  Let `w = s_1 ... s_k` be a word over `S` with `k <= R`.  Every prefix of `w` lies in
`B_R(Gamma)`, and each step `(prefix) * s_(j+1)` is a defined product of the table.  By induction on `k`,

```text
f(s_1) f(s_2) ... f(s_k) = f(value of w in Gamma).                                  (E)
```

In particular `f(s^-1) = f(s)^-1`, so `f(S)` is symmetric, and `f(s) != 1` for `s in S`, since `f` is injective.

**Step 2: the identity transports.**  Let `Phi_S` be the free group on `S` and `phi : R[Phi_S] -> R[H]` the algebra map
with `s |-> f(s)`.  Choose for each element of the support of each `xi_i` a word of length `<= R/2`, and lift
`xi_i` to `tilde xi_i in R[Phi_S]`.  Put

```text
E = tilde Delta^2 - lambda tilde Delta - sum_i tilde xi_i^* tilde xi_i   in R[Phi_S].
```

Every word in the support of `E` has length `<= R` (the lengths are `<= 2`, `<= 1`, and `<= R`).  The image of `E` in
`R[Gamma]` is `0`: for every `g in Gamma`, the coefficients of the words of `E` with value `g` add up to `0`.  By (E),
`phi` sends each such word to `f(g)`, so the coefficient of `f(g)` in `phi(E)` is a sum of those zero sums, and
`phi(E) = 0`.  Since `phi` preserves the involution (`w^-1 |-> f(w)^-1` by (E)), we get

```text
Delta_H^2 - lambda Delta_H = sum_i eta_i^* eta_i   in R[<f(S)>],   Delta_H = |S| - sum_S f(s),   eta_i = phi(tilde xi_i).
```

`f` is injective on `S`, so `Delta_H` is the Laplacian of the symmetric generating set `f(S)` of `Lambda = <f(S)>`.

**Step 3: (T).**  This is the easy direction of Ozawa's criterion.  Let `pi` be a unitary representation of `Lambda`
with no nonzero invariant vector.  Then `pi(Delta_H)` is a positive operator with trivial kernel, since
`<pi(Delta_H) v, v> = (1/2) sum_S ||pi(f(s)) v - v||^2`.  The identity gives
`pi(Delta_H)(pi(Delta_H) - lambda) >= 0`, so the spectrum of `pi(Delta_H)` lies in `{0} u [lambda, infinity)`.  An isolated point `0` of the spectrum would be
an eigenvalue, and the kernel is trivial, so the spectrum lies in `[lambda, infinity)`.  So
`<pi(Delta_H) v, v> >= lambda ||v||^2`, and for every unit vector some `s` has `||pi(f(s)) v - v||^2 >= 2 lambda/|S|`.
So `(f(S), sqrt(2 lambda/|S|))` is a Kazhdan pair, and `Lambda` has (T).  It is nontrivial by Step 1.  Item 1 is
proved.

**Step 4: consequences.**
- *LI.*  If `H` is locally indicable, the nontrivial finitely generated subgroup `Lambda` maps onto `Z`.  But `Z`
  is amenable and infinite, so it lacks (T), and quotients of Kazhdan groups are Kazhdan.  This is a contradiction.
- *BO.*  Bi-orderable groups are locally indicable: a bi-order is Conradian.
- *Finite refutation.*  By Claim A and Step 3 of `orderable-nonsofic-iff-order-realizable-forbidden-table-proof`,
  `Theta_LI(T)` is unsatisfiable, and some finite subset of it is unsatisfiable.
- *LO.*  A left-orderable group is torsion-free, so the nontrivial group `Lambda` is infinite.  It is left-orderable
  as a subgroup and Kazhdan by Step 3.  ∎

**Calibration.**
- *A known Kazhdan case.*  Take `Gamma = SL_3(Z)` with its elementary generators.  Explicit certificates for
  `SL_3(Z)` were computed by Netzer--Thom and by Fujiwara--Kabaya, and no finite-index subgroup of `SL_3(Z)` is
  left-orderable (Witte Morris).  The theorem predicts only
  that the certified table is not realizable in an LI group.  That is consistent: by
  [[orderable-nonsofic-iff-order-realizable-forbidden-table]] its failure to be LI-realizable has a finite clause
  refutation, as it must.
- *A non-Kazhdan case the method must not touch.*  `F_2 x F_2` is locally indicable, so by Step 4 it has no
  nontrivial Kazhdan subgroup, and the easy direction of Ozawa's criterion then shows that none of its tables is
  Kazhdan-certified.  So the theorem refutes no table of an actual LI group, and it proves nothing false.
