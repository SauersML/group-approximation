---
rg: 2
id: sl4z-thin-gap-from-matricial-stability
kind: route
title: Correct corona lifts to genuine representations and apply the finite-dimensional thin gap
target: sl4z-corona-reps-have-thin-relative-spectral-gap
requires: [sl4z-matricially-stable, sln-z-thin-quasiregular-not-weakly-contained-in-fd]
artifacts:
  - research/artifacts/sl4z-thin-corona-gap-reduction-2026-09-16.md
---

The artifact, Lemma 5.3 and Theorem 6.1, gives the full proof.

1. **Lift.**  Let `pi : C*(SL_4(Z)) -> Q_k` be unital.  Lift each `pi(u_g)` to a unitary
   `phi_n(g) in U(k_n)`.  Pointwise defect tends to `0`.
2. **Correct.**  `sl4z-matricially-stable` gives homomorphisms `rho_n` with
   `||phi_n(g) - rho_n(g)|| -> 0` for each `g`.  The *-homomorphisms `pi` and
   `q o (rho_n)_n` agree on every `u_g`, hence on `C*(SL_4(Z))`.
3. **Read off the norm.**  `||pi(x)|| = limsup_n ||rho_n(x)||`.  Each term is at most
   `1 - epsilon` by item 1 of `sln-z-thin-quasiregular-not-weakly-contained-in-fd`.  So
   `||pi(x)|| <= 1 - epsilon < 1`.
