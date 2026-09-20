---
rg: 2
id: polynomial-rank-hochschild-bound-via-diagonal-koszul
kind: route
title: Base-change to k(y), resolve by the Koszul complex of a_i - y_i acting on the right, and compare with the Hochschild bound on global dimension
target: polynomial-rank-is-at-most-hochschild-dimension
requires: []
---

Let `a_1..a_n ∈ A` commute and be algebraically independent, so
`k[a_1..a_n] ≅ k[x_1..x_n]`. Put `K = k(y_1..y_n)`, `B = A ⊗_k K` and
`u_i = a_i - y_i ∈ B`. The `u_i` commute.

Write `A[y] = A ⊗_k k[y_1..y_n]` and `S = k[y] \ {0}`. `S` is central in `A[y]`
and `B = S^(-1) A[y]`.

## Lemma A: `l.gl.dim B >= n`

**Step 1 (substitution).** Fix `j`. Define the left `A`-linear map
`φ_j : A[y] -> A[y_j..y_n]`, `m y^α ↦ m a_1^(α_1)...a_(j-1)^(α_(j-1)) y_j^(α_j)...y_n^(α_n)`,
placing the `a`'s on the right.
- Because the `y`'s are central and the `a`'s commute, `φ_j(m t) = φ_j(m) φ_j(t)` for
  `t ∈ k[y]`, where `φ_j(t) = t(a_(<j), y_(>=j))`.
- `φ_j(m(a_i - y_i)) = 0` for `i < j`. Conversely `m y_i ≡ m a_i` modulo
  `A[y](a_i - y_i)`, so every element is congruent to one in `A[y_(>=j)]`, on which
  `φ_j` is the identity.
- So `ker φ_j = Σ_(i<j) A[y](a_i - y_i)`, and `A[y]/Σ_(i<j) A[y](a_i - y_i) ≅ M_j := A[y_(>=j)]`.

`S` is central, so localization is exact, and
`B / Σ_(i<j) B u_i ≅ S^(-1) M_j`. Here `t ∈ S` acts on `M_j` by right multiplication by
`φ_j(t)`, and `u_j` acts by right multiplication by `a_j - y_j`.

**Step 2 (right regularity).** Right multiplication by `u_j` is well defined on
`B/Σ_(i<j) B u_i`, since the `u`'s commute. It is injective there. Suppose
`(m/s) u_j = 0`. Then some `t ∈ S` gives `m (a_j - y_j) φ_j(t) = 0` in `M_j`.
- Put `m' = m φ_j(t)`. Since `a_j` commutes with `a_(<j)`, this says `m'(a_j - y_j) = 0`.
- Expand `m' = Σ_(e<=E) m'_e y_j^e` with `m'_e ∈ A[y_(>j)]`. The top coefficient of
  `m'(a_j - y_j)` is `-m'_E`, so `m'_E = 0`. By induction `m' = 0`.
- `m' = t·m`, so `m/s = 0`.

No regularity of `A` itself is used.

**Step 3 (the Koszul complex resolves).** The right multiplications by `u_1..u_n`
are commuting endomorphisms of the left module `B`, and by Step 2 they form a regular
sequence. So the Koszul complex `B ⊗ Λ^•(k^n)` is a free resolution of the left
module `N = B / Σ B u_i`, of length `n`. Applying `Hom_B(-, Q)` gives
`Ext^n_B(N, Q) = Q / Σ u_i Q`.

**Step 4 (non-vanishing at Q = B).** It remains to show `B ≠ Σ u_i B`.
- Symmetrically, with left substitution `ψ` (`y_i ↦ a_i` on the left for `i < n`),
  we get `B/Σ_(i<n) u_i B ≅ S^(-1) A[y_n]` as right modules.
- Suppose `1` lies in `u_n` times that module. Clearing denominators gives
  `g ∈ k[a_(<n)][y_n]` with `g ≠ 0` and `m ∈ A[y_n]` with `(a_n - y_n) m = g`.
  Here `g = ψ(t)` for some `t ∈ S`, and `g ≠ 0` because the `a`'s are independent.
- Write `m = Σ_(e<=D) m_e y_n^e` and `g = Σ g_e y_n^e`. Comparing coefficients gives
  `m_D = -g_(D+1)` and `m_(e-1) = a_n m_e - g_e`. So every `m_e ∈ k[a_1..a_n]`.
- Hence the identity holds in `k[a][y_n] ≅ k[x_1..x_n, y_n]`, a polynomial ring.
  Setting `y_n = x_n` kills the left side. But `g` does not involve `x_n`, so `g = 0`,
  a contradiction.

So `Ext^n_B(N, B) ≠ 0`, and `l.gl.dim B >= pd_B N >= n`.

**Sanity checks.**
- `A = k[x_1..x_n]`: equality, `n = hd`.
- `A = k(x_1, x_2)`: `gl.dim A = 0`, but `A ⊗ k(y_1, y_2)` has global dimension 2.
  So base change is needed, and the bound `hd = 2` is sharp.
- `A = k<x_1, x_2>`: `hd = 1`, matching Bergman's theorem that commutative
  subalgebras are monogenic.

## Lemma B: `l.gl.dim(A ⊗_k K) <= hd_k(A)` for every field `K ⊇ k`

This is Cartan--Eilenberg, Homological Algebra, Chapter IX, Section 7. It is proved
here in full.
- Let `P_• -> A` be a projective `A^e`-resolution of length `d = hd_k(A)`. Apply
  `- ⊗_k K`. The result is a projective resolution of `A_K = A ⊗_k K` over
  `A^e ⊗_k K = (A_K) ⊗_K (A_K)^op`, still of length `d`.
- Each term is projective as a right `A_K`-module, and so is `A_K`. So the augmented
  resolution splits as a complex of right `A_K`-modules. It therefore stays exact after
  `- ⊗_(A_K) M` for any left `A_K`-module `M`.
- `(A_K ⊗_K A_K) ⊗_(A_K) M = A_K ⊗_K M` is a free left module, and summands stay
  projective.
- So every `M` has projective dimension at most `d`.

## Conclusion

`n <= l.gl.dim(A ⊗_k k(y_1..y_n)) <= hd_k(A)`.

For a non-unital embedding `φ: k[x_1..x_n] -> A`, suppose `c·1 + q(φ(x)) = 0`, where
`q` has no constant term. Multiply by `1 - e`, where `e = φ(1)`: this gives
`c(1 - e) = 0`. So either `c = 0` and then `q = 0` by injectivity, or `e = 1`. Either
way the `φ(x_i)` are algebraically independent in `A`.
