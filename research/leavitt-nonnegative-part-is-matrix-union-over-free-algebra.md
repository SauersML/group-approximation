---
rg: 2
id: leavitt-nonnegative-part-is-matrix-union-over-free-algebra
kind: claim
title: The nonnegative part of L_k(1,2) is a union of matrix rings over the free algebra, so its commuting pairs live in matrix rings over the free field
distinct_from:
  leavitt-isometry-centralizers-are-monogenic: that uses the free subalgebra k<s_0,s_1> to compute centralizers of monomial isometries; this identifies the whole nonnegative graded part as a direct limit of matrix rings over that free algebra.
  laurent-tensors-reduce-leavitt-rank-to-function-fields: that changes the coefficient field; this changes the host from L to its nonnegative part and then to matrices over the free field.
  leavitt-algebras-contain-no-two-variable-polynomial-ring: that is the open rank statement; this is a structural reduction of the part of it that lies in one degree half.
artifacts:
  - experiments/leavitt-nonnegative-part-2026-09-19/check_matrix_union.py
---

**ESTABLISHED** by `leavitt-nonnegative-part-is-matrix-union-over-free-algebra-proof` (unreviewed).

**Setup.**
- Let `k` be any field and `L = L_k(1,2)`. The generators satisfy `t_i s_j = δ_ij` and `s_0 t_0 + s_1 t_1 = 1`.
- Grade `L` by `deg s_i = 1`, `deg t_i = -1`, and put `L_(>=0) = ⊕_(n >= 0) L_n`.
- Let `P = k<x_0, x_1>` be the free algebra and `D = k(<x_0, x_1>)` the free skew field.
- For a word `y` let `∂_y : P → P` be the left quotient: `∂_y(x_w) = x_(w')` if `w = y w'`, and `0` otherwise.

**Statement.**
1. **Matrix blocks.** For each `N`, the map `Φ_N : M_(2^N)(P) → L` given by
   `(p_uv) ↦ Σ_(|u|=|v|=N) s_u p_uv(s) t_v` is an injective unital homomorphism. Call its image `E_N`.
2. **Union.** `E_N ⊆ E_(N+1)`, and `L_(>=0) = ∪_N E_N`. Under `Φ` the inclusion is entrywise
   `ψ : P → M_2(P)`, with `ψ(p)_(y,x) = ∂_y(p x_x)` for letters `x, y`. So `ψ(x_0) = [[x_0, x_1], [0, 0]]` and
   `ψ(x_1) = [[0, 0], [x_0, x_1]]`.
3. **Minimal-rank reduction.**
   - Let `C ⊆ M_n(D)` be a nonzero commutative `k`-subalgebra without zero divisors. It need not contain the
     identity matrix.
   - Let `r` be the least `D`-rank of a nonzero element of `C`.
   - Then `M_r(D)` has a subfield `F`, containing `k · 1`, with `F ≅ Frac(C)` as `k`-algebras.
4. **Rank one is classical.** Every commutative subfield of `D` containing `k` has transcendence degree at most 1.
   This is imported from Cohn and Schofield, via the verbatim quotation in the proof route.

**Consequences.**
- (a) Suppose `a, b ∈ L_(>=0)` commute and are algebraically independent.
  - Then for some `N` and some `r` with `2 <= r <= 2^N`, the matrix ring `M_r(D)` contains a commutative subfield
    of transcendence degree at least 2 over `k`.
  - The minimal `D`-rank of a nonzero element of `k[a, b] ⊆ M_(2^N)(D)` is then at least 2.
- (b) The same holds for `L_(<=0)`, by the involution `s_i ↔ t_i`.
- (c) If commutative subfields of `M_r(D)` have transcendence degree at most 1 for all `r`
  (`matrices-over-free-fields-have-no-trdeg-two-subfields`), then every commuting pair in `L_(>=0) ∪ L_(<=0)`
  is algebraically dependent.
- (d) `L_(>=0)` is stably finite, since each `E_N` sits inside `M_(2^N)(D)`, while `L` is purely infinite.
  - So no unital homomorphism `L → L_(>=0)` exists.
  - Any reduction of the rank question from `L` to `L_(>=0)` must therefore act on commutative subalgebras, not
    on the whole algebra.
