---
rg: 2
id: covering-towers-iff-effective-minimal-free-subshifts-proof
kind: route
title: Window-inside-a-patch lemma, downward induction for nonemptiness, containment for minimality, decidable forbidden balls, uniform asymmetry by compactness, subgroup-return periodicity
target: covering-towers-iff-effective-minimal-free-subshifts
requires: []
---

**Route. COMPLETE.** This is a hand proof with no imports. Notation is as in the
target: `d(x,z) = |xz^{-1}|`, `(λ.z)(μ) = z(μλ)`, `w_R(z,h)(μ) = z(μh)`.

## Basic identities

- **(I1)** `w_R(λ.z, h) = w_R(z, hλ)`, because `(λ.z)(μh) = z(μhλ)`.
- **(I2)** If `h = xg`, then `w_R(z,h) = w_R(g.z, x)`, because
  `z(μxg) = (g.z)(μx)`.
- **(I3)** A condition "some `h ∈ B(r)g` has `w_R(z,h) ∈ L`" on `z` at `g` is
  the same condition on `g.z` at `1`, by (I2). It depends only on `z` restricted
  to `B(R + r)g`.

## Lemma 1 (every margin ball lies inside a patch window)

Let `z ∈ Y`, where `Y = {z : ∀n ∀g ∃h ∈ B(R_n − m_n)g, w_{R_n}(z,h) ∈ L_n}`. Then
for every `n` and `g` there are `q ∈ L_n` and `c` with `|c| ≤ R_n − m_n` such
that `z(μg) = q(μc)` for all `μ ∈ B(m_n)`.

*Proof.*
- Take `h ∈ B(R_n − m_n)g` with `q = w_{R_n}(z,h) ∈ L_n`, and set
  `c = gh^{-1}`, so `|c| ≤ R_n − m_n`.
- For `|μ| ≤ m_n` we have `|μc| ≤ R_n`.
- Hence `z(μg) = z((μc)h) = q(μc)`. ∎

## Theorem, direction 2 ⇒ 1

Fix a margin covering tower and let `Y` be as in Lemma 1.

**Step 1: `Y` is a subshift.**
- *Shift-invariant.* Let `z ∈ Y`, `λ ∈ G` and `g ∈ G`. Apply the condition for
  `z` at `gλ` to get `h' ∈ B(R_n − m_n)gλ` with `w_{R_n}(z,h') ∈ L_n`. Put
  `h = h'λ^{-1} ∈ B(R_n − m_n)g`. By (I1), `w_{R_n}(λ.z, h) = w_{R_n}(z,h')`.
- *Closed.* Each condition at `(n,g)` is a finite union of cylinders, by (I3).

**Step 2: effectively closed, with a decidable forbidden set.** Let `F_n` be
the set of patterns `u : B(2R_n − m_n) → A` such that no `h ∈ B(R_n − m_n)` has
`(μ ↦ u(μh)) ∈ L_n` on `B(R_n)`.
- `F_n` is a finite, uniformly computable list: balls are computable, `L_n` is
  computable, and `|μh| ≤ 2R_n − m_n`.
- By (I3), `z ∈ Y` iff for all `n` and `g` the pattern `(g.z)|B(2R_n − m_n)` is
  not in `F_n`.
- So `Y` is the set of configurations avoiding every pattern in `∪_n F_n`, and
  membership in that set is decidable.

**Step 3: nonempty (downward induction).**

*Claim.* Fix `N`, choose `q_N ∈ L_N`, and let `z_N` be any configuration with
`z_N|B(R_N) = q_N`. Then for every `n ≤ N` and every `g ∈ B(R_N − m_N)` there is
`h_n` with `d(g,h_n) ≤ R_n − m_n` and `w_{R_n}(z_N,h_n) ∈ L_n`.

*Proof of the claim.*
- Base case: `h_N = 1` works.
- Step: given `h_k` for `k ≥ 1`, put `p_k = w_{R_k}(z_N,h_k) ∈ L_k` and
  `g' = g h_k^{-1}`, so `|g'| ≤ R_k − m_k`.
- Apply (C) to `p_k` and `g'`. This gives `h` with `d(g',h) ≤ R_{k−1} − m_{k−1}`,
  `|h| ≤ R_k − R_{k−1}` and `w_{R_{k−1}}(p_k,h) ∈ L_{k−1}`.
- Put `h_{k−1} = h h_k`. Then
  `d(g, h_{k−1}) = |g h_k^{-1} h^{-1}| = d(g',h) ≤ R_{k−1} − m_{k−1}`.
- For `|μ| ≤ R_{k−1}` we have `|μh| ≤ R_k`, so
  `z_N(μ h h_k) = w_{R_k}(z_N,h_k)(μh) = p_k(μh)`.
- Hence `w_{R_{k−1}}(z_N,h_{k−1}) = w_{R_{k−1}}(p_k,h) ∈ L_{k−1}`. ∎

*Conclusion.*
- Let `z` be a limit point of `(z_N)`, which exists because `A^G` is compact.
- Fix `(n,g)`. For all large `N`, `g ∈ B(R_N − m_N)` because `R_N − m_N → ∞`, so
  `z_N` satisfies the closed condition at `(n,g)`.
- Hence `z` satisfies it too, and `z ∈ Y`.

**Step 4: minimal, with a computable recurrence radius.**
- Let `z, z' ∈ Y` and `r ≥ 0`. Choose `n` with `m_n ≥ r`.
- *The pattern sits inside a tower patch.* By Lemma 1 at `g = 1`, the pattern
  `p = z|B(r)` satisfies `p(μ) = q(μc)` for some `q ∈ L_n` and
  `|c| ≤ R_n − m_n`.
- *The patch returns near every site of `z'`.* Fix `g`. The condition for `z'`
  at `(n+1, g)` gives `h' ∈ B(R_{n+1} − m_{n+1})g` with
  `q' = w_{R_{n+1}}(z',h') ∈ L_{n+1}`. By (K) there is `c' ∈ B(R_{n+1} − R_n)`
  with `q'(νc') = q(ν)` for `ν ∈ B(R_n)`.
- *So `p` occurs in `z'` within a uniform radius.* For `|μ| ≤ r`:
  `z'(μ c c' h') = q'(μ c c') = q(μc) = p(μ)`. So `p` occurs in `z'` at
  `λ = c c' h'`, and
  `d(g,λ) ≤ (R_n − m_n) + (R_{n+1} − R_n) + (R_{n+1} − m_{n+1})`.
- *Consequences.* The bound is computable and independent of `g`, `z` and `z'`.
- Every finite pattern of `z` therefore occurs in `z'`, so `z` lies in the orbit
  closure of `z'`.
- Hence every orbit is dense and `Y` is minimal.

**Step 5: free.**
- Let `z ∈ Y` and `s ≠ 1`. Choose `n` with `m_n ≥ R(s) + |s|`.
- By Lemma 1 at `g = 1` there are `q ∈ L_n` and `|c| ≤ R_n − m_n` with
  `z(ν) = q(νc)` for `|ν| ≤ m_n`.
- Since `|c| ≤ R_n − R(s) − |s|`, (A) gives `μ ∈ B(R(s))` with
  `q(μc) ≠ q(μsc)`.
- Both `μ` and `μs` lie in `B(m_n)`, so `z(μ) ≠ z(μs) = (s.z)(μ)`.
- Hence `s.z ≠ z`. ∎

## Theorem, direction 1 ⇒ 2

Let `Y ⊆ A^G` be nonempty, effectively closed, minimal and free, and let
`F_1, F_2, ...` enumerate its forbidden patterns. Write `Y_k` for the
configurations avoiding `F_1, ..., F_k`, and `L(Y)` for the patterns on balls
that occur in points of `Y`. Every pattern in `L(Y)` extends to a point of `Y`.

**Step 6: `L(Y)` is decidable.** Let `p` be a pattern on `B(r)`.
- *Non-occurrence is r.e.*
  - `[p] ∩ Y = ∅` iff `[p] ∩ Y_k = ∅` for some `k`, by compactness.
  - That holds iff there is `t` such that every pattern on `B(t)` extending `p`
    contains, fully inside `B(t)`, a translate of some `F_j` with `j ≤ k`.
    This is again compactness, and the check is finite by the solvable word
    problem.
- *Occurrence is r.e.* Suppose `p ∈ L(Y)`.
  - By minimality every `z ∈ Y` contains `p` somewhere. The open sets
    "`p` occurs within `B(t)`" increase with `t` and cover `Y`, so some `t`
    covers `Y`.
  - The closed set where `p` does not occur within `B(t)` misses `Y`, so it
    misses some `Y_k`. Hence there is `t'` such that every pattern on `B(t')`
    avoiding `F_1, ..., F_k` inside `B(t')` contains `p` within `B(t)`.
  - Conversely, such a certificate together with `Y ≠ ∅` shows `p ∈ L(Y)`.
  - So search over `(t, k, t')`.

**Step 7: computable recurrence and asymmetry radii.**
- Let `f(r)` be the least `t` such that every `q ∈ L(Y)` on `B(r+t)` contains
  every `p ∈ L(Y)` on `B(r)` at some `c ∈ B(t)`.
  - The test is decidable by Step 6.
  - `t` passes iff every `z ∈ Y` contains every such `p` within `B(t)`, since
    `L(Y)`-patterns extend to points.
  - Such a `t` exists by the covering argument of Step 6, applied to the finitely
    many `p`.
- Let `R(s)` be the least `R` such that every `q ∈ L(Y)` on `B(R + |s|)` has
  some `μ ∈ B(R)` with `q(μ) ≠ q(μs)`.
  - It exists because the open sets `{z : ∃μ ∈ B(R), z(μ) ≠ z(μs)}` increase
    and cover `Y`, by freeness (`s.z ≠ z`) and compactness.
  - It is computable by search.

**Step 8: the tower.**
- *Parameters.* Put `R_0 = 2` and `m_0 = 1`. Then set
  `m_{n+1} = R_n + f(R_n)` and `R_{n+1} = 2(R_n + f(R_n))`.
  - So `m_n ≤ R_n ≤ R_{n+1}`, and `m_n → ∞`.
  - `R_{n+1} − m_{n+1} = R_n + f(R_n) → ∞`.
  - `m_{n+1} ≥ R_n`.
- *Families.* `L_n = L(Y) ∩ A^{B(R_n)}` is finite, nonempty and uniformly
  computable.
- *(C).* Let `q ∈ L_{n+1}` and `|g| ≤ R_{n+1} − m_{n+1}`.
  - Then `|g| ≤ R_{n+1} − R_n`.
  - Take `h = g`, so `d(g,h) = 0`.
  - `w_{R_n}(q,g)` is a sub-pattern of a `Y`-pattern, so it lies in `L_n`.
- *(K).* Let `q = z|B(R_{n+1})` with `z ∈ Y`, and `p ∈ L_n`.
  - `p` occurs in `z` at some `|c| ≤ f(R_n) ≤ R_{n+1} − R_n`.
  - The window lies inside `B(R_{n+1})`.
- *(A).* Let `q = z|B(R_n)` and `|c| ≤ R_n − R(s) − |s|`.
  - Apply Step 7 to `c.z ∈ Y`. This gives `μ ∈ B(R(s))` with `z(μc) ≠ z(μsc)`.
  - Both points lie in `B(R_n)`, so `q(μc) ≠ q(μsc)`.

This proves the Theorem. ∎

## Corollary (overlap-recurrent points)

Let `L_n = {P_n}` with `P_n = y|B(R_n)`, and assume (OC) and (A). Then
`Y_OC = Y`.
- Steps 1, 2 and 5 and Lemma 1 do not use (C) or (K). So `Y_OC` is an
  effectively closed free subshift with a decidable forbidden set.
- *`y ∈ Y_OC`.* This is (OC).
- *`Y_OC` is the orbit closure `X` of `y`.*
  - `X ⊆ Y_OC`, because `Y_OC` is closed and invariant.
  - Conversely let `z ∈ Y_OC` and `r ≥ 0`. Choose `m_n ≥ r`. Lemma 1 gives
    `z(μ) = P_n(μc) = y(μc)` for `|μ| ≤ r`, so every finite pattern of `z`
    occurs in `y`, and `z ∈ X`.
- *Minimal.*
  - Every pattern of `y` on a ball `B(r)λ` is a sub-pattern of `P_n` once
    `R_n ≥ r + |λ|`.
  - `P_n` occurs within `R_n − m_n` of every site of every `z ∈ Y_OC`.
  - Hence `y` lies in the orbit closure of every `z ∈ Y_OC`. ∎

## Supplement (internal covering implies (OC))

Let `P_{n+1}|B(R_n) = P_n` and assume (IC_n) for all `n`. Put `y = ∪_n P_n`.
- *Setup.* Fix `n` and `g`, and choose `N > n` with `|g| ≤ R_N − m_N`.
- *Induction.* Run the downward induction of Step 3 with `z_N = y`, `p_k = P_k`,
  and (IC_{k−1}) in place of (C).
  - Start with `h_N = 1`.
  - Given `h_k` with `d(g,h_k) ≤ R_k − m_k` and `w_{R_k}(y,h_k) = P_k`, put
    `g' = g h_k^{-1} ∈ B(R_k − m_k)`.
  - (IC_{k−1}) gives `h` with `d(g',h) ≤ R_{k−1} − m_{k−1}`,
    `|h| ≤ R_k − R_{k−1}` and `w_{R_{k−1}}(P_k,h) = P_{k−1}`.
  - Then `h_{k−1} = h h_k` satisfies `d(g,h_{k−1}) ≤ R_{k−1} − m_{k−1}` and
    `y(μ h h_k) = P_k(μh) = P_{k−1}(μ)`.
- *Conclusion.* So `h_n` witnesses (OC) at `(n,g)`.
- *Link to the Theorem.* `{P_n}` with (IC) is itself a margin covering tower:
  (C) is (IC), and (K) holds with `c = 1`. ∎

## Lemma T (subgroup returns force periodicity)

Let `H ≤ G` and `R ≥ 0` with `B(R)H = G`, and suppose `w_R(y,h) = w_R(y,1) = P`
for every `h ∈ H`. Then `h.y = y` for all `h ∈ H`.

*Proof.*
- Let `g ∈ G` and `h ∈ H`, and write `g = μ h_0` with `|μ| ≤ R` and `h_0 ∈ H`.
- Then `(h.y)(g) = y(μ h_0 h) = w_R(y, h_0 h)(μ) = P(μ)`.
- Also `y(g) = w_R(y,h_0)(μ) = P(μ)`. ∎

*Consequence for designs.*
- If a free design makes the return set of `P_n` contain a subgroup `H_n`, then
  `B(R_n)H_n ≠ G`. This holds in particular if every coset of `H_n` meets every
  `(R_n − m_n)`-ball.
- So the density required by (OC) and by (C) with `|L_n| = 1` can never come
  from subgroup returns. Some of the returns must lie off every such subgroup.
- This applies to Toeplitz-type points over residually finite groups, where
  `P_n` returns along a finite-index `H_n`. There the (OC) margin must come from
  returns outside `H_n`.
