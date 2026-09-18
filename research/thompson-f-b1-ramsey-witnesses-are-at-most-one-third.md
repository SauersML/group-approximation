---
rg: 2
id: thompson-f-b1-ramsey-witnesses-are-at-most-one-third
kind: claim
title: In Thompson's F the Ramsey profile of the unit ball is 1/2 on radii 3 to 6 and 1/3 on radii 7 to 10, so no set is a unit-ball Ramsey witness of strength above 1/3, while in F_2 the value 1/2 persists at every radius
distinct_from:
  moore-ramsey-criterion-for-amenability: that is the general criterion and imports no numbers; this computes the exact precision profile of Moore's Ramsey sets for the unit ball of F on radii 3 to 10.
  thompson-f-ramsey-function-iterates-reach-towers: that transfers Følner lower bounds to the Ramsey function asymptotically; this is an exact small-radius census and bounds nothing asymptotically.
  thompson-f-ramsey-amplification-needs-unbounded-tower-overhead: that is the asymptotic AMP question; this gives its first exact data point (m = 1, precision 1/2 to 1/3) and decides nothing about it.
  thompson-f-is-not-amenable: that is the root; this kills only the unit-ball witnesses of strength above 1/3 as proofs of it.
artifacts:
  - experiments/ramsey-picture-sat-2026-09-17/groups.py
  - experiments/ramsey-picture-sat-2026-09-17/ramsey_sat.py
  - experiments/ramsey-picture-sat-2026-09-17/cegar.py
  - experiments/ramsey-picture-sat-2026-09-17/certify_upper.py
  - experiments/ramsey-picture-sat-2026-09-17/lower_bound.py
  - experiments/ramsey-picture-sat-2026-09-17/third_barrier.py
  - experiments/ramsey-picture-sat-2026-09-17/certify_barrier.py
  - experiments/ramsey-picture-sat-2026-09-17/barrier_core.py
  - experiments/ramsey-picture-sat-2026-09-17/certify_core.py
  - experiments/ramsey-picture-sat-2026-09-17/barrier_lp.py
  - experiments/ramsey-picture-sat-2026-09-17/summarize.py
---

**Setting.** `F = ⟨x_0, x_1⟩` acts on `[0,1]` by the usual piecewise-linear maps, with product = composition.
`F_2 = ⟨a, b⟩` is free. In each group `A = B_1 = {e, s^{±1}}` is the unit ball of the standard generators and
`B_n` is the ball of radius `n`. For `E ⊆ B_n` and `g ∈ I_n = {g : Ag ⊆ B_n}`, the *picture* is
`X_E(g) = {a ∈ A : ag ∈ E}`. The *Ramsey profile* is

`ρ_G(n) = min{ε : B_n is ε-Ramsey with respect to B_1}`,

with Moore's definition (quoted in `moore-ramsey-criterion-for-amenability`, non-strict `≤ ε`).
`ρ_G(n)` is nonincreasing in `n` by monotonicity in `B`.

**Claim.**
1. **F.** `ρ_F(n) = 1/2` for `3 ≤ n ≤ 6`, and `ρ_F(n) = 1/3` for `7 ≤ n ≤ 10`.
2. **F_2.** `ρ_{F_2}(n) = 1/2` for every `n ≥ 3`.
3. **Consequence.** For every `E ⊆ F` and all probability vectors `α, β` on `B_1`,
   `inf_{g ∈ F} (α − β)(X_E(g)) ≤ 1/3`. In `F_2` the value `1/2` is attained by `E` = the reduced words that
   begin with `b^{±1}`, `α` = uniform on `{b, b^{-1}}` and `β` = uniform on `{a, a^{-1}}`.
4. **The extremal direction dies at radius 11.** Put `w = (1/3)(x_0^{-1} − x_0) + (2/3)(x_1 − x_1^{-1})`.
   - For `n ≤ 10` there is `E ⊆ B_n` with `w(X_E(g)) ≥ 1/3` for all `g ∈ I_n`. This is the witness for `ρ_F(n) ≥ 1/3`.
   - For `n = 11` there is none. An irreducible obstruction uses 18 elements `g` of lengths 4, 6, 8 and 10
     (71 elements `ag` in all). This is a finite configuration of `F`, DRAT-checked on its own.
5. **Functions survive where sets die.** There is `f : B_11 → [0,1]` with `Σ_a w_a f(ag) ≥ c_11` for every
   `g ∈ I_11`, where `c_11 = 3787234/11125011 > 0.3404 > 1/3`.
   - Hence `R̃_{F,S}(1, ε) ≥ 12` for every `ε ≤ c_11`, and in particular `R̃_{F,S}(1, 1/3) ≥ 12`. This is
     Towsner's function version, quoted in the criterion node.
   - By contrast, no set `E ⊆ B_11` achieves even `1/3` in the direction `w` (item 4).

**In Towsner's notation.** `R_{G,S}(m, ε)` is quoted in the criterion node. With `ρ_F(2) ≥ 2/3` (route, Step 4)
the census gives the following values.
- `R_{F,S}(1) = R_{F,S}(1, 1/2) = 3`, and `R_{F_2,S}(1) = 3` as well.
- `R_{F,S}(1, ε) = 7` for `1/3 ≤ ε < 1/2`.
- `R_{F,S}(1, ε) ≥ 11` for `ε < 1/3`.

The proof is the direct route `thompson-f-b1-ramsey-witnesses-at-most-one-third-proof`. It is an exact census:
DRAT-checked SAT for the upper bounds, and explicit sets `E` with rational dual certificates checked in
`Fraction` arithmetic for the lower bounds.

**What it kills.** Consider any proof that `F` is non-amenable by a *unit-ball Ramsey witness*: a set `E ⊆ F`
and `α, β ∈ P(B_1)` with `(α − β)(X_E(g)) ≥ c > 0` for all `g`. Such a witness suffices, since an invariant mean
gives `Σ_a (α−β)_a m(a^{-1}E) = 0`. Every such proof has `c ≤ 1/3`.
- *Invariant:* `ρ_F(7)`.
- *Dying step:* restricting the witness to `B_7`. For `g ∈ I_7` the picture of `E ∩ B_7` equals that of `E`.
- *Contrast:* this is the free-group ping-pong witness of strength 1/2. It is exactly what `F` lacks from radius 7 on.
  `F` and `F_2` have the same balls up to radius 4, since the shortest relator of `F` has length 10.

**What it does not decide.** Amenability of `F` forces `ρ_F(n) → 0`, and a global witness of any strength
`c > 0` would prove non-amenability (compactness). The census shows the drop `1/2 → 1/3` at radius 7. It also shows the death at radius 11 of the
1/3 direction `w` that the solver returned at radii 7 and 10 (as `w`, or as `−w` via `E ↦ E^c`). It does not show
that `w` is the only 1/3 direction, it does not determine `ρ_F(11)`, and it says nothing about the limit.
