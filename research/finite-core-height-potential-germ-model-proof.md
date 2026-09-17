---
rg: 2
id: finite-core-height-potential-germ-model-proof
kind: route
title: Counting on height-graded germ models with non-injective restriction maps gives full witness value
target: finite-core-height-potential-forbids-bernoulli-deficit
requires:
  - bernoulli-rokhlin-deficit-has-a-finitary-witness
artifacts:
  - research/artifacts/height-graded-germ-models-2026-09-17.md
  - experiments/germ-models-2026-09-17/check_germ_model.py
---

This route combines Lemma 1 and Theorem A of the artifact (Sections 1 and 2).

**Step 1: functional count.**
- *Setup.* Let `X` be finite with arbitrary maps `T_f, S_e`. Call `w` good when
  `1 -> w`, `e -> S_e w`, `fe -> S_e T_f w` is a well-defined injective map `Q -> X`.
  Put `x` iid uniform on `A^k` over `X` and `c(w) = psi((x(S_e w))_e)`.
- *Chain.* `k|X| log q = H(x) <= sum_w H(c(w)) + sum_w H(x(w) | (c(T_f w))_f)`.
- *Good points.* At a good `w` the local variables have the joint law of `(psi(x|_E), x(1), y_F)` in
  `G`: they are the same functions of iid values at points that coincide as in `Q`. So their terms sum
  to `k Phi`.
- *Bad points.* Bound their terms by `log|R| + k log q`.
- *Result.* `log q <= Phi + beta(log|R|/k + log q)`.

**Step 2: germ model.**
- *Parameters.* Let `K = <E ∪ F>` with word length for `E ∪ F`, let `D` be the maximum length of an
  element of the finite core `K_Z`, and put `lambda = 1 + D` and `R_r = K_Z B(r)`.
- *Region inclusions.*
  - Zero letters satisfy `z R_r = R_r`.
  - A letter `u` of height `t >= 1` satisfies `u R_(r - lambda t) ⊂ R_r`, because
    `|u kappa g| <= 1 + D + r - lambda`.
- *Points.* Levels are `X_r = N^(R_r) × [M]^r` for `0 <= r <= L = lambda max ht`, together with one
  junk point.
- *Maps.* `T_f` and `S_e` send `(r, c, j)` to `(r - lambda t, c(u ·)|_(R_(r - lambda t)), j truncated)`.
  They send a point to junk when the level would go negative.

**Step 3: chart at the top level.**
- *Coincidences.* `S_e T_f w` is the germ of `w` at the element `fe` with drop `lambda ht(fe)`. Since
  `ht` is a function on `Q`, equal elements give equal points, and `fe = 1` gives `w`.
- *Separation.* Distinct elements of equal height differ at the site `1` of their germs with
  probability `1 - 1/N`. Elements of different heights lie in different levels.
- *Bad fraction.* It is at most `|Q|^2/N` on `X_L`. Lower levels and junk make up at most `3/M` of `X`,
  since each level gains a factor `M`.

**Step 4: limit.** Let `M, N -> infinity`. Then `beta -> 0`, and Step 1 gives `Phi >= log q`.

The route uses no imports: only elementary Shannon inequalities and finite counting. The
`requires` entry supplies the definition of `Phi` and of the pattern.

**Check.** `experiments/germ-models-2026-09-17/check_germ_model.py` builds the model over `Z/2 * Z`
with `E = F = {1, z, s}` (two read pairs, core `{1, z}`). It checks the coincidence identity
`S_e T_f = germ(fe)` on 1200 sampled top-level points, and the chart-injective fraction is at least
the union bound.
