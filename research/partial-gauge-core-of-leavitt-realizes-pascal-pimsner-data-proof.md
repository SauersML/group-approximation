---
rg: 2
id: partial-gauge-core-of-leavitt-realizes-pascal-pimsner-data-proof
kind: route
title: Count the letters 2 in the Leavitt core to get the Pascal diagram, read the frame s_1 on vertices, and restrict the infinite-word module to the words with no 2
target: partial-gauge-core-of-leavitt-realizes-pascal-pimsner-data
requires:
  - isometric-shift-frames-over-uhf-bases-fail-the-k-budget
  - torsion-k1-modulo-central-scalars-kills-scalar-symbols
---

**Item 1.**
- The `s_μ t_ν` with `|μ| = |ν| = n` and `k` letters `2` in each are matrix units of a copy of `M_(binom(n,k))(Q)`,
  since `t_ν s_(μ') = δ_(ν μ')` for `|ν| = |μ'|`. Different `k` are orthogonal.
- `s_μ t_ν = s_μ (s_1 t_1 + s_2 t_2) t_ν` gives the Pascal inclusion.
- `K_0` of the colimit of semisimple algebras is the colimit of the `K_0`. The polynomials `t^k (1−t)^(n−k)`,
  `0 <= k <= n`, form a `Z`-basis of the polynomials of degree `<= n`, since each has lowest term `t^k`. They satisfy
  the Pascal rule `t^k(1−t)^(n−k) = t^k(1−t)^(n+1−k) + t^(k+1)(1−t)^(n−k)`. So the colimit is `Z[t]`. ∎

**Items 2–3.**
- `deg_2 s_1 = deg_2 t_1 = 0`, and `t_1 s_1 = 1`.
- `φ(b) = s_1 b t_1` is multiplicative because `t_1 s_1 = 1`.
- On a vertex idempotent `s_μ t_μ`, `φ` gives `s_(1μ) t_(1μ)`, with the same number of `2`s and length `n+1`. So
  `K_0(φ)` is multiplication by `1 − t` on the basis, hence everywhere.
- `×t` is injective on `Z[t]`, and `Z[t]/(t) ≅ Z` by evaluation at `0`, which sends `1 ↦ 1`. ∎

**Item 4.**
- *The module.* `t_i s_j e_w = δ_ij e_w`. Also `Σ_i s_i t_i e_w = e_w`, because `w` begins with exactly one letter.
- *Counting 2s.* On basis vectors, `s_1` and `t_1` do not change the number of `2`s, `s_2` adds one, and `t_2`
  removes one or gives `0`. So a monomial of `deg_2`-degree `0` preserves the number of `2`s, and the only
  eventually-`1` word with no `2` is `1^∞`.
- *The character.* Restricting to the invariant line gives a unital ring map `χ`. Then `s_2 t_2 ∈ ker χ` and
  `s_2 t_2 != 0` in `L`. ∎

**Item 5.** Assume `(P)` for `R ⊗ Q̄` over `B ⊗ Q̄`.
- `K_0(B ⊗ Q̄) = Z[t]`, `K_1 = Q̄^x ⊗ Z[t]`, `K_2 = 0` (ultramatricial over `Q̄`, and `K_2(Q̄) = 0` by
  `torsion-k1-modulo-central-scalars-kills-scalar-symbols`).
- With `1 − A = ×t`:
  - `K_0 ⊇ Z`, with `[1] ↦ 1`;
  - `K_1 = coker(×t on Q̄^x ⊗ Z[t]) ⊕ 0 = Q̄^x`, the scalars;
  - `K_2 = 0 ⊕ ker(×t on Q̄^x ⊗ Z[t]) = 0`. ∎
