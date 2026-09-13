---
rg: 2
id: thompson-f-has-no-contractible-rips-complex-proof
kind: route
title: F is torsion-free of infinite cohomological dimension, so it has no contractible Rips complex
target: thompson-f-has-no-contractible-rips-complex
requires:
  - contractible-rips-complex-gives-finite-classifying-space
---

`F` is the group of orientation-preserving piecewise-linear homeomorphisms of
`[0,1]` with finitely many breakpoints, all at dyadic rationals, and all slopes
powers of 2 (Cannon–Floyd–Parry, *Introductory notes on Richard Thompson's
groups*, Enseign. Math. 42 (1996)).

1. **`F` is torsion-free.** Let `f ≠ 1` and pick `t` with `f(t) ≠ t`, say
   `f(t) > t`. Since `f` is increasing, `f^k(t) > f^(k-1)(t) > ... > t` for all
   `k >= 1`, so no power of `f` is the identity.
2. **Elements with small support.** Let `x0` be the element that is `t/2` on
   `[0,1/2]`, `t - 1/4` on `[1/2,3/4]` and `2t - 1` on `[3/4,1]`. For a standard
   dyadic interval `I = [p/2^k, (p+1)/2^k]`, let `a_I(t) = p/2^k + t/2^k` and
   let `f_I` equal `a_I ∘ x0 ∘ a_I^-1` on `I` and the identity off `I`. Its
   breakpoints are dyadic and its slopes are powers of 2, so `f_I ∈ F`, and
   `f_I ≠ 1` with support in `I`.
3. **`Z^n <= F` for every `n`.** Choose `n` standard dyadic intervals
   `I_1, ..., I_n` with pairwise disjoint interiors and put `f_j = f_{I_j}`. The
   `f_j` commute because their supports have disjoint interiors. If
   `∏ f_j^(k_j) = 1`, restricting to the interior of `I_j` gives `f_j^(k_j) = 1`,
   so `k_j = 0` by step 1. So `(k_1, ..., k_n) ↦ ∏ f_j^(k_j)` embeds `Z^n` in `F`.
4. **`cd F = ∞`.** `cd Z^n = n`, since the torus `T^n` is a closed aspherical
   `n`-manifold with `H^n(Z^n; Z) = Z`. Cohomological dimension does not increase
   when passing to a subgroup (Brown, *Cohomology of Groups*, Chapter VIII).
   Hence `cd F >= n` for all `n`.
5. **Conclusion.** If `P_r(F,S)` were contractible for some finite generating
   set `S` and some `r`, then `contractible-rips-complex-gives-finite-classifying-space`
   would give `cd F <= |B_S(r)| - 1 < ∞`, contradicting step 4.
