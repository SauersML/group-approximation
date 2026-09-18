---
rg: 2
id: leavitt-tensor-unit-word-problem-reduces-to-base-proof
kind: route
title: Reduce Leavitt monomials, pad to a common right length, read off coefficients against Leavitt matrix units, and zero-test each in B
target: leavitt-tensor-unit-word-problem-reduces-to-base
requires:
  - complexity-bounded-host-classes-are-not-universal
---

Notation as in the target. For a word `α = α_1⋯α_p` over `{1,2}` put
`x_α = x_(α_1)⋯x_(α_p)` and `x_α^* = y_(α_p)⋯y_(α_1)`, with `x_∅ = x_∅^* = 1`.
Everything takes place in `A = B ⊗_(F_2) L`, where `b ⊗ 1` and `1 ⊗ w` commute.
Write `b` for `b ⊗ 1` and `w` for `1 ⊗ w`.

**Step 0. Facts about `L`.**
- (a) `L ≠ 0`. Let `V` have basis `e_0, e_1, ...`, and put
  `x_1 e_j = e_(2j)`, `x_2 e_j = e_(2j+1)`, `y_1 e_(2j) = e_j`, `y_1 e_(2j+1) = 0`,
  `y_2 e_(2j+1) = e_j`, `y_2 e_(2j) = 0`. Then `y_i x_j = δ_ij` and
  `x_1 y_1 + x_2 y_2 = id_V` on each basis vector, so `L` acts unitally on `V ≠ 0`.
  Hence `b -> b ⊗ 1` is injective, since `B ⊗ -` over a field is exact and `F_2 -> L`
  is injective.
- (b) **Grading.** The relations are homogeneous for `deg x_i = 1`, `deg y_i = -1`.
  So `L = ⊕_k L_k` and `A = ⊕_k B ⊗ L_k`, and an element of `A` is `0` iff each
  homogeneous component is `0`.
- (c) For `|β| = |γ|`, `x_β^* x_γ = δ_(βγ)`, by induction on the length from
  `y_i x_j = δ_ij`.
- (d) For every `r >= 0`, `Σ_(|γ| = r) x_γ x_γ^* = 1`. Induction on `r`, using
  `x_(γi) x_(γi)^* = x_γ (x_i y_i) x_γ^*` and `x_1 y_1 + x_2 y_2 = 1`.

**Step 1. Monomial reduction.** Every monomial `ν` in `x_i, y_i` equals in `L`
either `0` or `x_α x_β^*` with `|α| + |β| <= |ν|`. Apply `y_i x_j -> δ_ij`
while some `y` precedes some `x`; each application shortens the word or kills it.
This takes at most `|ν|` rewrites.

**Step 2. Padding.** For `n >= |β|`, step 0(d) with `r = n - |β|` gives
`x_α x_β^* = Σ_(|δ| = n - |β|) x_(αδ) x_(βδ)^*`, since `x_(βδ)^* = x_δ^* x_β^*`.

**Step 3. Coefficients are well defined.** Fix `k` and `n >= max(0, -k)`, and
suppose `Σ c_(αβ) x_α x_β^* = 0` in `A`, the sum over `|α| = n + k`, `|β| = n`,
with `c_(αβ) ∈ B`. For fixed `α_0, β_0` of these lengths multiply on the left by
`x_(α_0)^*` and on the right by `x_(β_0)`. By step 0(c), and because the `c`'s
commute with the Leavitt letters, this leaves `c_(α_0 β_0) ⊗ 1 = 0`. By step 0(a),
`c_(α_0 β_0) = 0`.

**Step 4. The algorithm.** Fix, for each `h_i^(±1)`, an expression
`Σ_(j <= c) μ_j ν_j` with `μ_j` a monomial in the `b`'s and `ν_j` a monomial in
the Leavitt letters, all of degree `<= D`. Such expressions exist because the
generators of `A` commute across the two factors. Let `u` be a word of length `l`
in the `h_i^(±1)`, and put `n = lD`.
1. Expand `u` into at most `c^l` terms `μ ν` with `|μ|, |ν| <= n`.
2. Reduce each `ν` by step 1 to `0` or `x_α x_β^*`, and pad it by step 2 to
   `|β| = n`. This gives at most `c^l 2^n` terms `μ x_α x_β^*` with `|β| = n` and
   `|α| <= 2n`.
3. Write `1 = Σ_(|γ| = n) x_γ x_γ^*` by step 0(d), and collect: for each pair
   `(α, β)` let `c_(αβ) ∈ B` be the sum of the `μ`'s attached to it, plus `1` if
   `α = β` (over `F_2`, subtracting `1` is adding it). Then
   `u - 1 = Σ c_(αβ) x_α x_β^*`.
4. By step 0(b) this vanishes iff each degree-`k` part vanishes, where
   `k = |α| - n`. Each such part has all `|β| = n`, so by step 3 it vanishes iff
   all its `c_(αβ)` are `0` in `B`. Hence `u = 1` in `H` iff every `c_(αβ)` passes
   the zero test of `B`.

**Cost.** There are at most `2^(2n+1) * 2^n` pairs `(α, β)`. Each `c_(αβ)` has
at most `c^l 2^n + 1` monomials of degree `<= n`, so size at most
`(c^l 2^n + 1)(n + 1) <= C 2^(C l)`. Steps 1-3 are bookkeeping on at most
`c^l 2^n` terms of size `O(n)`, in time `C 2^(C l)`. So the total time is at most
`C 2^(C l) (1 + F_B(C 2^(C l)))`, with `C` depending on `c`, `D` and the
number of `b`-generators. This is part 1.

**`GL_N`.** For a subgroup of `GL_N(B ⊗ L)`, carry the entries of the matrices.
A word of length `l` has entries that expand into at most `(Nc)^l` terms, and
`u = 1` iff each entry of `u - 1` passes steps 1-4. The bound keeps the same
form with `c` replaced by `Nc`.

**Part 2.** Let `B ∈ 𝓑`, and use the generating set for which the zero test runs
in time `C_B F(C_B n) + C_B`. Part 1 (with its `GL_N` form, constants now also depending on `N`) gives, on
words of length `l >= 1`, time at most
`C_H 2^(C_H l) (1 + C_B + C_B F(C_B C_H 2^(C_H l)))`. Take
`C >= C_H + log_2(C_B C_H) + 1`. Then `C_B C_H 2^(C_H l) <= 2^(C l) <= 2^(2 C l)`,
so monotonicity of `F` gives time at most
`C_H (1 + 2 C_B) 2^(2 C l) (1 + F(2^(2 C l))) = C_H (1 + 2 C_B) T(C l)`.
Words of length `0` cost a constant. So every finitely generated subgroup of
every `GL_N(B ⊗ L)`, `N >= 1`, `B ∈ 𝓑`, has an algorithm within `C' T(C' l) + C' l + C'` for
a constant `C'` depending on the subgroup. `T` is recursive because `F` is. The
class `K` of these subgroups therefore meets the hypothesis of
`complexity-bounded-host-classes-are-not-universal`, which gives a
two-generated group with solvable word problem embedding in no member of `K`. If
it embedded in some `GL_N(B ⊗ L)`, its image would be a finitely generated
subgroup, a member of `K`. `∎`
