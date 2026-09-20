---
rg: 2
id: quantum-pattern-vanishing-needs-a-d-ball-proof
kind: route
title: Extend the pattern to the whole D-ball and sum with Q1; for the calibration use a column of Z x Z/5 that is too long for any 1-ball
target: quantum-pattern-vanishing-needs-a-d-ball
requires: []
---

**Item 1.**
- Any two points of `B_D(p)` are at distance at most `2D`. By Q2, every `E_a(f)` with `f ∈ B_D(p)`
  commutes with every `E_b(f')` with `f' ∈ B_D(p)`.
- Put `F' = B_D(p) ∖ F`. By Q1, `1 = ∏_(f' ∈ F') Σ_b E_b(f')`. Multiplying this against the product
  over `F` and expanding gives

  ```text
  ∏_(f∈F) E_(β(f))(f)  =  Σ_γ ∏_(g ∈ B_D(p)) E_((β∪γ)(g))(g),
  ```

  where `γ` runs over the patterns on `F'`. The factors commute, so their order does not matter.
- Every `β ∪ γ` restricts to `β`, and `β` does not occur, so `β ∪ γ` does not occur either. Translate
  `B_D(p) = p·B_D`: the pattern `α(f) = (β ∪ γ)(pf)` on `B_D` does not occur in `X`, because `X` is
  shift-invariant. So each summand vanishes by Q3.

**Item 2.**
- `X` is shift-invariant and closed, and it is of finite type. Its forbidden patterns are "two `1`s in
  one column" and "column all `0`".
- The ball `B_1((n,m))` is `{(n,m), (n±1,m), (n,m±1)}`. Its all-zero window occurs in `X`: put the
  `1`s of columns `n` and `n±1` in row `m+2`, and any `1` in every other column.
- So the scalar family `E_0 = 1`, `E_1 = 0` satisfies Q1 and Q2, and it satisfies Q3 vacuously on the
  all-zero windows. It is a `1`-quantum family.
- The column `{0} × Z/5` has diameter `2`, since `(0,0)` to `(0,2)` has length `2`. Its all-zero
  pattern is forbidden, but the product of its factors is `1 ≠ 0`.
- No `1`-ball contains the column: a `1`-ball meets a column in at most three sites.

**Item 3.** We read each application of (L0) in `locally-finite-splittings-rigid-compactification-proof`.
- In (L1), the rule pairs are `(h, hb)` with `b` a generator, and `(h, h c t_ε)` with `c` in a finite
  transversal. Both lie in `B_r(h)`, where `r` is the rule radius, and `D ≥ r` is assumed.
- (L2) uses the same pairs as rule (X).
- In Section 4, the pattern is on `h·B^A_D`, with `B^A_D` the `A`-word ball. It lies in `B^Λ_D(h)`,
  because `A`'s generators are among `Λ`'s.

So item 1 applies each time.
