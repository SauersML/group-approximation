---
rg: 2
id: top-determined-register-rings-cannot-divide-the-unit-proof
kind: route
title: Solve harmonic functionals level by level through left inverses of the finitely many possible top blocks
target: top-determined-register-rings-cannot-divide-the-unit
requires:
  - dilation-letters-cannot-divide-the-unit-class
---

**Part 1.**
- Harmonic functionals are `Hom(K_0(R), Q)`, by (P), as in `dilation-letters-cannot-divide-the-unit-class-proof`.
- The level-`j` coefficients of an equation come from the multiplicities of letters. There are finitely many
  letters, and the pattern of sources whose top is `j` is eventually periodic in `j`, through the residues of the
  dilation letters. So only finitely many matrices occur as `M_j` up to repeated rows.
- Each occurring matrix is injective. Fix a left inverse `L` with rational entries for each, and let `D` be a
  common denominator of all these left inverses.
- For large `j`, the equations with top `j` give `M_j h⃗(j) = (integer combinations of values at levels < j and
  of tail values)`. So `h⃗(j) = L(...)`.
- By induction on `j`, every value is a `Z[1/D]`-combination of the finitely many initial values: those at levels
  below the threshold, and the tail values.
- The remaining equations, where a top is determined twice, only constrain those finitely many initial values.
- So `Hom(K_0(R), Q)` has finite dimension, and its elements with integral initial values take values in
  `Z[1/D']`, where `D'` also absorbs the denominators of a rational basis of the initial-value space.
- If `[1]` has infinite order, some harmonic `h` has `h([1]) ≠ 0` (`Q` is injective). Scale it to integral
  initial values and apply part 1 of `dilation-letters-cannot-divide-the-unit-class`. ∎

**Part 2 (one type).** Let `a` be the number of loops.
- If `a ≠ 1`, the equation at level `k` has top `k`, or the level of an upward letter, and a nonzero coefficient
  there: `1 − a`, or the multiplicity of the highest upward letter.
- If `a = 1`, the level-`k` unknown cancels. The top is then the highest target of the remaining letters, with a
  positive coefficient.
- Every large `j` is a top. Either a shift letter reaches `j` from `j + s`, or a dilation letter of the smallest
  base reaches it from `p_min j + r`, which is then the highest target.
- So each `M_j` is a nonzero column, hence injective. ∎
