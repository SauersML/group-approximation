---
rg: 2
id: q-x2-z-in-t-check-blows-up-the-doubling-fixed-point-proof
kind: route
title: Direct proof that every copy of Q x|_2 Z in T-check blows up the doubling fixed point
target: q-x2-z-in-t-check-blows-up-the-doubling-fixed-point
requires:
  - q-x2-z-in-t-check-has-a-doubling-semiconjugacy
---

Notation and normalization as in `q-x2-z-in-t-check-has-a-doubling-semiconjugacy`.
- `g in T-bar`, `t(x + 1) = t(x) + 2`, and `h` commutes with `τ_1`. Also `h∘t = δ∘h`
  and `h∘q = τ_(ρ(q))∘h`.
- `t` induces a degree-2 circle map `u` of `S^1 = R/Z`. `u` is PL, with finitely
  many breakpoints and slopes in `2^Z`.
- `h` induces a monotone degree-1 map `η` with `η∘u = D∘η`, where `D(θ) = 2θ`.
- For `s in Q`, `q_s in D` has `ρ(q_s) = s`. `q_s` maps the fibre `h^-1(0)` onto
  `h^-1(s)`, and `t` maps `h^-1(s)` onto `h^-1(2s)`.

**Items 2 and 3 from item 1.**
- Item 2 is the last sentence above.
- If `P` is nondegenerate, the `D`-orbit of an interior point `x` of `P` meets
  `int P` only in `x`, since `D` permutes the fibres freely. So it is not dense,
  and `D` is not minimal.

**Item 1: `t(P) = P`.** `h∘t^±1 = δ^±1∘h` maps `P` into `h^-1(0) = P` both ways.

Suppose now, for a contradiction, that `P = {p}` is a point.

**A. Rational fibres are points.** `h^-1(s) = q_s(P) = {x_s}`. As `s' -> s`,
`x_(s')` tends to a point of `h^-1(s)`, so `x_s` is a two-sided limit of `X := D·p`.

**B. Periodic points.** `t^k(x) = x + j` iff `2^k h(x) = h(x) + j`, iff
`h(x) = σ := j/(2^k - 1)`. So the periodic points of `u` are exactly the points
`x_σ mod 1` with `σ` of odd denominator. Each fibre over such a `σ` is a point.

**C. Multiplier rigidity.**
- `t` is repelling at `p`. For `y > p` near `p`, `h(t y) = 2h(y) > h(y)`. So its
  one-sided slopes there are `2^a` and `2^a'` with `a, a' >= 1`. Slope `1` would make
  `t` the identity on one side of `p`.
- Fix `σ = j/(2^k - 1)` and put `e = τ_-j q_j`. Then `h∘e = h`, so `e` fixes every
  point of `X`. `e` is PL, so by A it is the identity near `x_σ`.
- Near `p`: `t^k q_σ = q_(σ+j) t^k = τ_j e q_σ t^k = τ_j q_σ t^k`. Hence
  `τ_-j t^k = q_σ t^k q_σ^-1` near `x_σ`.
- `q_σ` is one-sided linear at `p`. So `u^k` has one-sided multipliers exactly
  `2^(ka)` (right) and `2^(ka')` (left) at every periodic point of period dividing `k`.
- A periodic orbit avoiding the finitely many breakpoints has equal one-sided
  multipliers, so `a = a'`.

**D. Every invariant measure has exponent `a`.**
- A nondegenerate fibre (gap) lies over an irrational `σ` by A. `u^m` maps it
  injectively onto the gap over `2^m σ`. These gaps are pairwise disjoint, so a gap
  is wandering and has measure `0` for every `u`-invariant probability.
- Double every point of the grand orbit of the breakpoints. This gives a compact
  circle-like space `S^` on which `u` lifts to a continuous `u^`, and
  `φ^ = log_2` (one-sided slope) is continuous.
- An ergodic `u^`-invariant measure is either a one-sided periodic orbit, with
  `∫φ^ = a` by C, or non-atomic.
- In the non-atomic case it projects to a non-atomic ergodic `ν` on `S^1` that gives
  no mass to gaps or breakpoints, and `η_*ν` is a non-atomic `D`-invariant measure.
- `D`-periodic measures `ν_j` are weak* dense among `D`-invariant measures,
  because `D` is the full one-sided 2-shift, which has specification.
- Take `ν_j -> η_*ν` and let `ν~_j` be their unique `u`-periodic pullbacks (B).
- For continuous `f`, the function `F := f∘η^-1` is defined at point fibres and is
  continuous off the countable set of gap points, which is `η_*ν`-null. So
  `∫f dν~_j = ∫F dν_j -> ∫F dη_*ν = ∫f dν`, i.e. `ν~_j -> ν`.
- `φ` is bounded and continuous off a `ν`-null finite set, so
  `∫φ dν = lim ∫φ dν~_j = a`.
- Since every invariant measure gives the continuous `φ^` the same integral `a`,
  `N^-1 S_N φ^ -> a` uniformly on `S^` (standard; e.g. Walters, *An Introduction to
  Ergodic Theory*). So for large `N`, every one-sided slope of `u^N` lies in
  `[2^(N(a - 1/2)), 2^(N(a + 1/2))]`.

**E. `a = 1`.** `∫_0^1 (t^N)'(x) dx = t^N(1) - t^N(0) = 2^N`, while
`(t^N)' >= 2^(N(a - ε))` a.e. for large `N`. So `a <= 1`, and `a = 1`.

**F. `h` is a homeomorphism.** A gap `I` would satisfy
`|u^(mN)(I)| >= 2^(mN/2) |I| -> ∞`, since `u^(mN)` is injective on it. So there are
no gaps, `h` is injective, and `η` is a conjugacy from `u` to `D`.

**G. The invariant density.**
- `u^N` is a uniformly expanding, topologically exact PL circle covering. By
  Lasota--Yorke it has a unique absolutely continuous invariant probability
  `ν = ρ dx`, with `ρ` of bounded variation and `inf ρ > 0` (see e.g. Boyarsky--Góra, *Laws
  of Chaos*). `ν` is `u`-invariant.
- Rokhlin's formula for absolutely continuous invariant measures of piecewise
  expanding maps (Ledrappier 1981; Hofbauer--Keller 1982) gives
  `h_ν(u) = ∫ log|u'| dν = a log 2 = log 2`, using D and E.
- This is the topological entropy, and `u` (conjugate to `D`) has a unique measure of
  maximal entropy `μ(A) = Leb(η(A))`. So `μ = ν = ρ dx`.

**H. Contradiction.**
- By F, `q_s = h^-1 τ_s h` commutes with `τ_1`, so its circle map `r_s` lies in `T`,
  and `η r_s η^-1 = R_s`. So `μ` is `r_s`-invariant, and `ρ = (ρ∘r_s)·r_s'` a.e. with
  `r_s' in 2^Z`.
- Hence `log_2 ρ mod 1` is invariant under the group `{r_s}`. That group is
  conjugate by `η` to `Q/Z` acting by rotations, and is ergodic for `μ ~ Leb`. So
  `ρ in 2^(c+Z)` a.e.
- Being bounded above and below, `ρ` takes finitely many values. As a BV function,
  it then agrees a.e. with a step function with finitely many jumps.
- Then `η(x) = ∫_p^x ρ` is affine with positive slope on some open interval, and so
  is `h`. This contradicts item 4 of
  `q-x2-z-in-t-check-has-a-doubling-semiconjugacy`.

So `P` is a nondegenerate interval.
