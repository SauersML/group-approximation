---
rg: 2
id: kms-vertex-words-zero-height-moments-proof
kind: route
title: Collect the word into normal form, sum by parts to turn the area and cubic coordinates into height moments, and read the kernel of a Vandermonde matrix
target: kms-vertex-words-close-iff-weights-have-zero-height-moments
requires: []
artifacts:
  - experiments/kms-surface-girth-general/check_moment_lemma.py
  - experiments/kms-surface-girth-general/check-moment-lemma.log
---

Notation as in the target. All exponents are read in `F_p`; `p` is odd, so `2` is invertible and
`C(e,2) = e(e−1)/2` is well defined mod `p` (`C(e+p,2) − C(e,2) = p(e + (p−1)/2)`).

## Step 0. Normal forms

This recalls Step 0(a),(b) of `kms-girth-surfaces-give-surface-subgroups-proof`, with the argument written out.

- In `U_4` put `u = [x,y]` and `v = [u,y]`. The relators give `[u,x] = [v,x] = [v,y] = 1`, `y^{−1}xy = xu` and
  `y^{−1}uy = uv`. By induction on `e ≥ 0`, `y^{−e} u y^e = u v^e` and `y^{−e} x y^e = x u^e v^{C(e,2)}`
  (`y^{−1}(x u^e v^{C(e,2)})y = xu · (uv)^e · v^{C(e,2)} = x u^{e+1} v^{C(e+1,2)}`).
- Hence, with `x`, `u`, `v` pairwise commuting and `v` central,

  ```text
  y^β x^γ u^μ v^ν · x^e = y^β x^{γ+e} u^μ v^ν,
  y^β x^γ u^μ v^ν · y^e = y^{β+e} x^γ u^{μ + eγ} v^{ν + γ C(e,2) + e μ}.
  ```

  So every element is `y^β x^γ u^μ v^ν`, and `x^p = 1` conjugated by `y` gives `u^p = 1`, then `v^p = 1`; so
  `|U_4| ≤ p^4`.
- Let `φ` be the automorphism `x ↦ xu`, `u ↦ uv`, `v ↦ v` of `(Z/p)^3 = <x,u,v>`. Then `φ^n(x) = x u^n v^{C(n,2)}`
  and `φ^n(u) = u v^n`, so `φ^p = id` because `p | C(p,2)`. In `(Z/p)^3 ⋊_φ Z/p`, the elements `X = x` and a
  generator `Y` acting by `φ` satisfy the relators of `U_4`, with `[X,Y] = u` and `[[X,Y],Y] = v`, and generate a
  group of order `p^4`. So `|U_4| = p^4`, and the normal form `y^β x^γ u^μ v^ν` (exponents in `F_p`) is unique.
- In `U_3` the same argument with `v = 1` gives `y^β x^α u^μ · y^e = y^{β+e} x^α u^{μ+eα}`, `|U_3| = p^3` and unique
  normal forms `y^β x^α u^μ`.

## Step 1. Collecting the word

Put `A_s = a_1 + ⋯ + a_s` and `μ_s = A_1 b_1 + ⋯ + A_s b_s`. Multiplying letter by letter from the identity with
the rules of Step 0, the normal form of `w` has

```text
β = Σ_s b_s,   γ = A_m,   μ = μ_m = Σ_s A_s b_s,   ν = Σ_s ( A_s C(b_s,2) + b_s μ_{s−1} )   (U_4 only).
```

So `w = 1` exactly when `Σ b_s = 0`, `Σ a_r = 0`, `μ = 0` and, for `U_4`, `ν = 0`.

## Step 2. Summation by parts

Assume `Σ a_r = Σ b_s = 0`, so `A_m = 0` and `Σ_{s ≥ r} b_s = −H_r`.

- *Area.* `A_{min(s,t)} = Σ_{r ≤ min(s,t)} a_r` gives `Σ_s A_s b_s = Σ_r a_r Σ_{s ≥ r} b_s = −Σ_r a_r H_r`. So
  `μ = −Σ_r a_r H_r`.
- *Cubic coordinate.* `2ν = Σ_s A_s b_s^2 − Σ_s A_s b_s + 2 Σ_{t < s} A_t b_t b_s = Σ_{s,t} A_{min(s,t)} b_s b_t − μ`.
  Expanding `A_{min(s,t)}` as before, `Σ_{s,t} A_{min(s,t)} b_s b_t = Σ_r a_r (Σ_{s ≥ r} b_s)^2 = Σ_r a_r H_r^2`.
  So `2ν = Σ_r a_r H_r^2 + Σ_r a_r H_r`.

With `Σ a_r = 0`, the pair `(μ, ν)` vanishes exactly when `Σ a_r H_r = 0` and `Σ a_r H_r^2 = 0`, because `2` is
invertible. With Step 1 this is item 1 of the target.

## Step 3. The kernel

Item 1 says `a ∈ F_p^m` lies in the kernel of the `(m−1) × m` matrix `V = (H_r^d)`, `0 ≤ d ≤ m−2`.

- *Distinct heights.* `V` has rank `m − 1`. The vector `(1 / ∏_{s ≠ r}(H_r − H_s))_r` is in its kernel: for
  `d ≤ m − 2`, `Σ_r H_r^d / ∏_{s≠r}(H_r − H_s)` is the leading coefficient of the Lagrange interpolant of `t^d` at
  the `m` heights, and that interpolant is `t^d` itself, of degree `< m − 1`. So the kernel is the line it spans.
  For `m = 3`, multiplying by `−(H_1 − H_2)(H_2 − H_3)(H_3 − H_1)` gives `(H_2 − H_3, H_3 − H_1, H_1 − H_2)`. Every
  coordinate is nonzero.
- *Nonzero increments force the shapes.* `b_r ≠ 0` for every `r` (with `b_m = H_1 − H_m`) means cyclically
  consecutive heights differ. For `m = 3` all three heights are therefore distinct.
- *`m = 4` with a repeated height.* Then `H_1 = H_3` or `H_2 = H_4`.
  - If exactly one holds, there are three distinct heights. Grouping the coefficients of equal heights, the grouped
    vector lies in the kernel of an invertible `3 × 3` Vandermonde matrix, so it is zero. The two ungrouped
    coefficients are then `0`, contradicting `a_r ≠ 0`.
  - If both hold, the grouped vector `(a_1 + a_3, a_2 + a_4)` lies in the kernel of the invertible `2 × 2`
    Vandermonde matrix of the rows `d = 0, 1`, so `a_3 = −a_1` and `a_4 = −a_2`; the row `d = 2` then holds too.
  This is item 2.

## Step 4. Counts

- `U_3`: choose distinct nonzero `H_2 ≠ H_3` (`(p−1)(p−2)` ways; then `b = (H_2, H_3 − H_2, −H_3)` is nonzero) and
  `λ ≠ 0`: `(p−1)^2 (p−2)`.
- `U_4`, generic: `H_2, H_3, H_4` nonzero and pairwise distinct (`(p−1)(p−2)(p−3)` ways) and `λ ≠ 0`.
- `U_4`, alternating: `H_2 = d ≠ 0`, `H_3 = 0`, `H_4 = d`, so `b = (d, −d, d, −d)`, and `a_1, a_2 ≠ 0`: `(p−1)^3`.

The two `U_4` classes are disjoint, which gives item 3.

## Check

`check_moment_lemma.py` (MSI) enumerates all words with nonzero exponents and zero exponent sums for
`p = 3, 5, 7, 11, 13` (`U_3`) and `p = 5, 7, 11, 13` (`U_4`). For each it compares the collection law of Step 1,
the moment criterion and the classification, and it compares the number of trivial words with the formulas of
Step 4. `check-moment-lemma.log` records the results.
