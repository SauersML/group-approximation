---
rg: 2
id: amenable-hnn-seams-break-bernoulli-degree-one-expansion-proof
kind: route
title: Constant character on the base, marker eigenfunction on the stable letter, spectral gap for the distance bound
target: amenable-hnn-seams-break-bernoulli-degree-one-expansion
requires: []
artifacts:
  - research/artifacts/bernoulli-degree-one-expansion-amenable-seam-2026-09-13.md
---

Artifact Sections 2–5.

1. **Lemma M, markers.** The Bernoulli shift of `Z` or `Z^2` has `delta`-approximate eigenfunctions
   `eta : Y -> Z/2` for every character.
   - For `Z^2`: put a marker on row `j` when the count of `y(i, j) < 1/2` over `i in [0, N)` is at least `r`, and let
     `eta` be the parity of the last marker at or below 0.
   - Shifting along the row changes each count by at most 1, so the error is at most `q'/q`. Shifting across rows
     errs only at a marker, so the error is at most `q`.
   - The CLT and the local bound `P(Bin(N,1/2) = k) = O(N^-1/2)` make both small.
   - Restricting coordinates to `C` transfers `eta` to `X`.
2. **Relators.** Put `c = chi` on `S_0` and `c(t, .) = eta` for the character `chi o theta - chi|_C`.
   - `R_0` relators give `chi(r) = 0`.
   - For `t c_k t^-1 theta(c_k)^-1`, the relator sum at `x` equals `eta(c_k u) - eta(u) - rho(c_k)` with
     `u = t^-1 theta(c_k)^-1 x`. So the defect is at most `delta`.
3. **Lemma S, spectral gap.** `L^2_0(X)` restricted to `A_0` lies in a multiple of `lambda_(A_0)`, since stabilizers
   of finite supports are finite, and twisting by a character keeps it there. Hence a `tau`-approximate eigenfunction
   `F : X -> Z/2` with `tau != 0` and error `delta'` on `S_0` forces `delta' >= kappa/(kappa + 4|S_0|)`.
   - Split `psi o F` into its mean and its `L^2_0` part.
   - The Kesten inequality bounds the `L^2_0` part; a generator with `tau = 1` bounds the mean.
4. **Distance.** An exact `z` within `delta'` of `c` is `delta F + chi'` by superrigidity, and `F` is then a
   `(chi - chi'|_(A_0))`-approximate eigenfunction. Since `chi` does not extend, `chi - chi'|_(A_0) != 0`, and Lemma S
   gives `delta' >= theta_0`.

**Standard inputs, recalled and not re-read:** Hulanicki–Kesten (existence of `kappa` for nonamenable `A_0`), the
central limit theorem and the local binomial bound.
