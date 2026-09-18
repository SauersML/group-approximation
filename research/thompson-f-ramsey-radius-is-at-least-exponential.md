---
rg: 2
id: thompson-f-ramsey-radius-is-at-least-exponential
kind: claim
title: In Thompson's F every 1/2-Ramsey ball for B_m has radius at least 2^(m/4-6), because one coloring by the breakpoint cocycle at 1/2 forces every balancing measure to place breakpoints on a quarter of the exponentially large Schreier ball of 1/2
distinct_from:
  thompson-f-ramsey-function-iterates-reach-towers: that shows, via Følner towers and only infinitely often, that R is not bounded by exp_q((log_q m)^d) for all large m; this gives an explicit bound R(m) ≥ 2^(m/4-6) for every m. It is proved from one coloring, without Følner sets, Towsner's inequality or amenability, and it also kills subexponential rates off that ladder such as 2^(m/log m).
  thompson-f-b1-ramsey-witnesses-are-at-most-one-third: that is an exact census of the unit ball at radii 3 to 11; this is an asymptotic lower bound on R(m) for all m, and says nothing at m = 1.
  thompson-f-ramsey-radius-double-gap-below-reiter-radius: that is RGAP₂, which asks R to be non-elementarily small compared with CR; this is a lower bound on R, and it neither proves nor refutes RGAP₂.
  thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap: that relates R to the coarse Reiter radius CR; this bounds R alone from below by a direct coloring.
  moore-ramsey-criterion-for-amenability: that is the imported definition and criterion; this is an unconditional quantitative consequence of the definition for F.
artifacts:
  - experiments/ramsey-lamp-forcing-2026-09-17/lamp_forcing.py
  - experiments/ramsey-lamp-forcing-2026-09-17/lamp_forcing.json
---

**ESTABLISHED** by `thompson-f-ramsey-radius-is-at-least-exponential-proof`. It is a direct proof from the
definitions quoted verbatim in `moore-ramsey-criterion-for-amenability`, plus elementary PL facts about the
generators, which were checked exactly by `experiments/ramsey-lamp-forcing-2026-09-17/lamp_forcing.py`. It has not
been independently reviewed.

**Setting.** F acts on `[0,1]` by increasing PL homeomorphisms, with product `gy = g∘y`, and `S = {x_0, x_1}` with the
standard generators. Balls `B_n` are taken in the word metric of `S ∪ S⁻¹`, as in
`thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`. Let `R(m) = R_{F,S}(m) ∈ [0, ∞]` be the least `n` such
that `B_n` is 1/2-Ramsey w.r.t. `B_m` (Moore, Section 3). The answer does not depend on whether F is written with
left or right actions: the isomorphism `y ↦ (y as an element of the opposite group)⁻¹` fixes every ball. Let
`P(r) = {h(1/2) : h ∈ B_r}` be the ball of radius `r` about `1/2` in the Schreier graph of the orbit `F·(1/2)`.

**Theorem.** For every `r ≥ 0`:
- (a) *Lamp forcing.* `R(2r+3) ≥ |P(r)|/12`.
- (b) *Exponential Schreier ball.* `|P(r)| ≥ 2^{⌊r/2⌋}`. The words `α = x_1` and `β = x_1x_0⁻¹` map `J = [1/2, 3/4)`
  onto the disjoint intervals `[1/2, 5/8)` and `[5/8, 3/4)`.
- (c) Hence `R(m) ≥ max(m, 2^{m/4 − 6})` for every `m ≥ 1`.

The Theorem is unconditional. If F is not amenable, `R(m) = ∞` for large `m` and (c) holds trivially.

**The coloring.** Write `ĉ_y(t) = log₂(y⁻¹)'(t+) − log₂(y⁻¹)'(t−)` for the breakpoint jump of `y⁻¹` at `t`. One set
does all the work for every `m`:

`E = { y ∈ B_n : ĉ_y(1/2) = 0 }` (the inverse has no breakpoint at `1/2`).

Suppose `ν` is a probability on `B_n` that balances `E` for `B_{2r+3}`. Then for each point `p ∈ P(r)` it satisfies
`P_ν(y⁻¹ has a breakpoint at p) ≥ 1/4`. The reason is that four elements of `B_{2r+3}` all move `1/2` to `p` and
shift the jump there by `0, 1, 2, 3` respectively. A word of length `n` has at most `3n` breakpoints, so
`3n ≥ |P(r)|/4`.

**Data** (`lamp_forcing.json`, exact). For `r = 0..12`, `|P(r)| = 1, 3, 6, 11, 19, 32, 53, 87, 142, 231, 375, 608, 985`.
The differences are Fibonacci numbers, so `|P(r)| = Fib(r+3) − 2` on this range and the growth rate is about `1.618`.
The proven bound `2^{⌊r/2⌋}` is weaker. The four-jump construction was verified at every `p ∈ P(12)` with
`|h_t| ≤ 2r+3`. The cocycle identity was checked at 17670 points, and `|Br(h)| ≤ 3|h|` on all 3957 elements of `B_7`.

**Why it matters.**
- *It kills Moore's "moderate rate" hope below exponential, pointwise.* Moore's Section 7 hoped that 1/2-Ramsey sets
  for F "might grow at a more moderate rate". The only previous kill was Corollary B of
  `thompson-f-ramsey-function-iterates-reach-towers`. It holds only infinitely often and only against the ladder
  `exp_q((log_q m)^d)`, all of whose members are subexponential. Here every subexponential bound on the Ramsey radius
  fails at *every* `m ≥ m_0`. That includes rates such as `2^{m/log m}` or `2^{√m}`, which are off the ladder.
  - *Invariant:* the breakpoint lamp count `|Br(y⁻¹) ∩ P(r)|`.
  - *Dying step:* every inductive or explicit construction of Ramsey balls at subexponential radius fails at the same
    step. A measure that balances `E` for `B_{2r+3}` must have a breakpoint at a quarter of the `≥ 2^{r/2}` points of
    `P(r)`, which needs words of length `≥ 2^{r/2}/12`.
- *It pins the elementary band.* An elementary `R_F`, the case left open by Proposition C of
  `thompson-f-ramsey-function-iterates-reach-towers` and needed for the route
  `thompson-f-amenable-via-costly-ramsey-amplification`, must lie between `2^{cm}` and some `exp_q`. In the
  sandwich `thompson-f-ramsey-amplification-is-the-ramsey-reiter-gap`, the inner compositions in RGAP₂ are therefore
  each at least exponential.
- *It shows where Ramsey hardness in F comes from.* The bound uses only that the orbit of `1/2` has an exponentially
  growing Schreier graph, together with a Z-valued cocycle (the breakpoint jump) whose value at a point can be shifted
  by bounded words that fix that point. In a lamplighter `Z/2 ≀ Z`, the analogous coloring (lamp at `0`) forces lamps
  only at the `O(r)` positions within distance `r`, so there it gives only a linear bound. F's exponential Schreier
  ball is what makes the difference.

**Method ceiling (remark, heuristic, not part of the established statement).** Forcing of this kind cannot pass
exponential. A coloring defined by cocycle values of `y⁻¹` at finitely many points `T` forces lamps only inside
`B_m·T`. So it forces at most `|B_m|·|T|` breakpoints and can conclude at most `R(m) ≥ |B_m|·|T|/3`, where
`|B_m| ≤ 4·3^{m−1}`. Enlarging the jump window
to `{0, …, K−1}` improves the constant `1/4` only to `1/2 − 1/K`. Iterating the forcing adds radii rather than
composing `R`. So this method cannot reach the towers in RGAP₂. See the route, Remark 3.
