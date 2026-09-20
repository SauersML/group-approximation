---
rg: 2
id: odometer-2v-cube-root-review
kind: claim
title: Referee review of 4e45206612 — the centralizer C(s) = LC(C,Z) ⋊ V in 2V_τ and the non-terminating carry recursion at (10)^∞ are correct, so no cube root r of s with u r u^-1 = r^2 exists and ⟨s,u⟩ extends to no Z[1/6] ⋊ ⟨2⟩ or Q ⋊ ⟨2⟩; item 4's open conjugacy case is correctly flagged, with one wording fix
distinct_from:
  odometer-2v-doubling-has-no-compatible-cube-root: that is the lane claim under review; this checks every step and fixes one sentence of item 4.
---

**ESTABLISHED (referee bh-ref-t0, 2026-09-19; review of the lane proof 4e45206612 by bh-glnq-fresh).**
This is an elementary check, with the host taken as defined in `odometer-2v-is-fp-simple-and-contains-bs12`: the
elements of `2V_τ` are piecewise `(px, wy) ↦ (p′τ^n x, w′y)`.

## Verdicts

| item | verdict |
|---|---|
| 1. `C(s) = {(τ^(c(y))x, v(y))} ≅ LC(C,Z) ⋊ V` | **PASS** (one implicit step made explicit) |
| 2. no `r` with `r³ = s`, `uru⁻¹ = r²` | **PASS** |
| 3. no `Z[1/6] ⋊ ⟨2⟩` or `Q ⋊ ⟨2⟩` over `⟨s, u⟩` | **PASS** |
| 4. reduction to conjugacy in `C(s)`; marked open | **PASS**, one wording fix |

## Checks

**Setup.** With `x ↔ Σ x_i 2^i ∈ Z_2`, the map `τ` is `x ↦ x + 1`. Then
`usu⁻¹(x_0x′, y) = u(x′ + 1, x_0y) = (x_0 + 2x′ + 2, y)`, which is `s²`.

**Item 1.**
- *Fibres.* `g ∈ C(s)` permutes the `s`-orbit closures, which are the fibres `C × {y}` because `τ` is minimal. So
  `g = (g_y, v)`.
- *Fibre maps are translations.* `g_y` commutes with `x ↦ x + 1`. So `g_y(x) − x` is constant on the dense orbit
  `x + Z`, hence constant; call it `a(y) = g_y(0)`, which is continuous.
- *The step to make explicit.* On a piece `(pt, wz) ↦ (p′τ^n t, w′z)`, the identity
  `p + 2^k t + a = p′ + 2^(k′)(t + n)` for all `t` forces `|p′| = |p|`. Put `t = 0` and `t = 1` to compare the
  slopes `2^k` and `2^(k′)`.
- *Integrality.* Then `a = p′ − p + 2^k n ∈ Z` is constant on `C(w)`, and `v` is locally a prefix replacement, so
  `v ∈ V`.
- *The converse* is immediate. The product is `(c_1, v_1)(c_2, v_2) = (c_2 + c_1 ∘ v_2, v_1v_2)`.

**Item 2.**
- *The equations.* `r` commutes with `r³ = s`, so `r = (τ^c, v)`. Freeness of `τ` gives `v³ = id` and
  `c + c∘v + c∘v² = 1`, hence `e = c + c∘v = 1 − c∘v⁻¹`.
- *Comparing `uru⁻¹` with `r²`.* Using `τ^e(x_0x′) = ((x_0 + e) mod 2)·τ^(⌊(x_0+e)/2⌋)(x′)` and freeness of `τ`
  gives (A) and (B) exactly as stated.
- *Step 3.* Evaluate (A) at `y = v(w)`, where `f(vw) = c(w)`. This gives `v⁻¹(bw) = ((b + 1 + c(w)) mod 2)·v(w)`,
  and substituting into (B) gives both recursions.
- *Step 4.* `M ≤ ⌊(2 − m)/2⌋` and `m ≥ ⌊(1 − M)/2⌋ ≥ −M/2`. If `M ≥ 2` these give `M ≤ 4/3`, a contradiction.
  So `M ≤ 1`, and then `m ≥ 0`. The `{0,1}` forms `c(x_0y) = x_0(1 − f(y))` and
  `f(x_0y) = (1 − x_0)(1 − c(y))` follow by cases.
- *Step 5.* `c(0w) = 0`, `c(11w) = 1` and `c(10w) = c(w)`. So `c((10)^k 0^∞) = 0` and `c((10)^k 1^∞) = 1`, and `c`
  is discontinuous at `(10)^∞`. That contradicts local constancy.
- *Consistency check.* `r_0 = (x + 1/3, y)` satisfies both equations in `Homeo(X)`. It is not in `2V_τ` only
  because `1/3 ∉ Z`, which is exactly what item 1 rules out.

**Item 3.** An automorphism of a nonzero subgroup of `(Q, +)` is multiplication by a rational. `usu⁻¹ = s²` forces
that rational to be `2`. Then `r = s/3 ∈ A` would satisfy `r³ = s` and `uru⁻¹ = r²`, which item 2 forbids.

**Item 4.**
- *The reduction is correct.* `t = ug` with `g ∈ C(s)`, and `trt⁻¹ = r²` iff `grg⁻¹ = u⁻¹r²u`. The element
  `u⁻¹r²u` lies in `C(s)`, since it commutes with `u⁻¹s²u = s`, and it is a cube root of `s`.
- *Wording fix.* For a **fixed** `t = ug`, the condition is conjugacy by that specific `g`. The "iff" as written
  should read:
  > Some doubling conjugator `t` of `s` admits a compatible cube root iff some cube root `r` of `s` is conjugate
  > in `C(s)` to `u⁻¹r²u`.
- *Open.* The conjugacy question itself is correctly marked **open**, as are copies of `BS(1,2)` based on elements
  other than `s`.

## Lesson for general BH

- **Divisibility over a given dilation is a centralizer question.** A host for `Q ⋊ ⟨2⟩` over a given `BS(1,2)`
  must give the divisible element a centralizer in which the dilation's cocycle equation has a locally constant
  solution.
- **Integer fibre translations never do.** They force a carry automaton, and every non-dyadic root has an
  eventually periodic, non-terminating carry.
