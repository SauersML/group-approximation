---
rg: 2
id: fpbs-tree-normal-relative-threshold-is-inverse-cogrowth-proof
kind: route
title: Non-backtracking recursion, Pringsheim at both radii, and a branching process of cyclically reduced blocks
target: fpbs-tree-normal-relative-threshold-is-inverse-cogrowth
requires: []
artifacts:
  - research/artifacts/fpbs-tree-relative-cogrowth-2026-09-16.md
---

This is a complete direct proof. It uses only standard facts:
- Pringsheim's theorem for power series with nonnegative coefficients;
- the identity theorem and the holomorphic inverse function theorem;
- the survival criterion for Galton–Watson processes;
- approximation of events by cylinder events.

Full details are in Sections 2–5 of the artifact. The notation is that of the
claim.

**1. Two-point function (artifact Lemma 3.1).** `T` is a tree, so
`P_p(o <-> h) = p^|h|`, and `chi^N_p = sum_n f_n(N) p^n`.

**2. Formal identity (Lemmas 2.1–2.2).** Let `A` be the adjacency matrix of the
label multigraph on `Q`, and `A_n(x,y)` the number of reduced words of length
`n` from `x` to `y`.
- Extending a reduced word by one letter gives `A_1 A = A_2 + (q+1) I` and
  `A_n A = A_(n+1) + q A_(n-1)` for `n >= 2`.
- So `B(s) = sum_n A_n s^n` satisfies `B(s)((1 + q s^2) I - s A) = (1 - s^2) I`.
  Hence `B = phi(s) sum_m z(s)^m A^m` as formal power series.
- The `(e,e)` entry is `F_N(s) = phi(s) Gamma(z(s))` with
  `Gamma(z) = sum_m (q+1)^m p_m z^m`, whose radius is `z_Q = 1/((q+1) rho_Q)`.
- Absolute convergence for small `|s|` makes this an identity of functions near
  `0`.

**3. Radius and endpoint (Lemma 2.3).** `rho_Q > rho_T` gives `s_N < 1/sqrt q`
and `z'(s_N) > 0`.
- *`R_N >= s_N`.* If `R_N < s_N`, then `phi · Gamma ∘ z` is holomorphic on a
  convex neighbourhood of `[0, R_N]`. By the identity theorem it continues
  `F_N` past `R_N`, which contradicts Pringsheim's theorem for `F_N`.
- *The identity on `[0, s_N]`.* The identity then holds on `[0, s_N)`, and at
  `s_N` by monotone convergence of both nonnegative series.
- *`R_N <= s_N`.* If `R_N > s_N`, the local inverse of `z` at `s_N` turns
  `F_N/phi` into a holomorphic continuation of `Gamma` past `z_Q`. It agrees
  with `Gamma` on a real segment to the left of `z_Q`, and this contradicts
  Pringsheim's theorem for `Gamma`.

This gives item 1, and item 3's formula, since `(q+1) z_Q = 1/rho_Q`.

**4. Threshold (Lemmas 4.1–4.2, Proposition 4.3).**
- *Below `s_N`.* If `chi^N_p < infinity`, then a.s. `|K_h ∩ N| < infinity` for
  every `h in N`, by invariance under left multiplication by `N`. So there is no
  `N`-infinite cluster.
- *Cyclically reduced words.* Write each `h ≠ e` in `N` uniquely as
  `u w u^(-1)` with `w in N` cyclically reduced, using normality. This gives
  `F_N - 1 = C_N (1 - s^2)/(1 - q s^2)`, so the cyclically reduced elements of
  `N` also have exponential rate `1/R_N`.
- *A branching process above `s_N`.* For `p > s_N`, choose `m` and a letter `x`
  such that the set `E` of cyclically reduced `w in N` of length `m` beginning
  with `x` has `|E| p^m > 1`. Words in `E` concatenate without cancellation.
  Open geodesic segments `g -> gw`, `w in E`, from distinct `g` at the same
  level are edge-disjoint. So the reached block concatenations form a
  Galton–Watson process with mean `|E| p^m > 1`, and `K_o` meets `N` infinitely
  often with positive probability.
- *Zero-one law.* The event is `N`-invariant, and translations by elements of
  `N` of large length decorrelate cylinder events. So the probability is `1`.

This gives item 2.

**5. Items 4 and 5 (Section 5).**
- *Item 4.* `z` is strictly increasing on `[0, 1/sqrt q]`, and
  `z(1/q) = 1/(q+1)`. So `s_N > 1/q` iff `z_Q > 1/(q+1)`, iff `rho_Q < 1`.
- *Item 5.* `(q+1) z(1/q) = 1` and `phi(1/q) = (q-1)/q`.

QED.

Consistency checks, not part of the proof:
`experiments/fpbs-tree-relative-cogrowth-2026-09-16/`. The coefficient identity
agrees exactly with brute-force enumeration for `[F_3,F_3]` (`n <= 22`) and
`<<a_3>>` (`n <= 14`), and item 5 is confirmed numerically in the second case.
