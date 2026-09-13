---
rg: 2
id: pl-rearrangement-two-transitive-orbit-action-proof
kind: route
title: Interval matching, rotations, slope germs and a contracting conjugator give the 2-transitive orbit action of V(A,P)
target: pl-rearrangement-groups-have-two-transitive-orbit-actions
requires:
  - two-transitive-action-reduces-type-a-to-two-clauses
  - type-a-action-gives-boone-higman-for-subgroups
---

Notation as in the target. Since `q' > 0`, (R) gives `0 < q < 1`.

`V(A,P)` is a group: images of pieces are half-open intervals with endpoints in
`A`, inverses of pieces are `x ↦ p^{-1} x − p^{-1} c` with `p^{-1} ∈ P` and
`p^{-1} c ∈ A`, and a composite is affine on the refinement of one partition by
the preimages of the other's breakpoints, which lie in `A`.

**Lemma 1 (matching).** For `u, v ∈ A` and positive `a, b ∈ A` there is an
increasing bijection `f: [u, u+a) → [v, v+b)` with finitely many pieces
`x ↦ px + c`, `p ∈ P`, `c ∈ A`, and breakpoints in `A`.

*Proof.* By (S), `a = p_1 + ... + p_m` and `b = p'_1 + ... + p'_n` with all terms
in `P`. Replacing a term `p` by `pq + pq'` (both in `P` by (R)) raises the number
of terms by one, so assume `m = n`. Put `x_i = u + p_1 + ... + p_i` and
`y_i = v + p'_1 + ... + p'_i`, in `A`, and map `[x_{i-1}, x_i)` onto
`[y_{i-1}, y_i)` by `x ↦ y_{i-1} + (p'_i/p_i)(x − x_{i-1})`. The slope lies in
`P`, and the constant lies in `A` because `P ⊆ A`. ∎

**Faithful.** If `g` fixes `O` pointwise, each piece `[x_{i-1}, x_i)` contains the
infinitely many points `x_{i-1} + (x_i − x_{i-1}) q^k` (`k ≥ 1`) of `O`. An affine
map fixing two points is the identity, so `g = 1`.

**Transitive.** For `c ∈ O` the rotation `r_c(x) = x + c` on `[0, 1−c)` and
`x + c − 1` on `[1−c, 1)` lies in `V(A,P)` and sends `0` to `c`.

**2-transitive.** For `x, y ∈ O∖{0}`, Lemma 1 on `[0,x) → [0,y)` and
`[x,1) → [y,1)` (positive lengths `x, y, 1−x, 1−y ∈ A`) gives `g` with `g(0) = 0`
and `g(x) = y`. So `Stab(0)` is transitive on `O∖{0}`; with the rotations,
`V(A,P)` is transitive on ordered pairs of distinct points.

**Slope germs.** If `g(0) = 0`, the first piece has `c_1 = 0`, so `g(x) = γ(g)x`
near `0` with `γ(g) ∈ P`. Composition near `0` shows `γ: Stab(0) → P` is a
homomorphism. It is onto: for `p ∈ P` take `s = q^k` with `s < 1` and `ps < 1`,
and let `h_p` be `x ↦ px` on `[0,s)` followed by Lemma 1 on `[s,1) → [ps,1)`.

**The kernel of γ.** Put `s_0 = q' = 1 − q ∈ O` and
`L = {g ∈ V(A,P) : g = id on [0, s_0)}`. The map `ψ(x) = (x − s_0)/q` is an
affine bijection `[s_0,1) → [0,1)` with slope `q^{-1} ∈ P` and constant in `A`
(`q` is a unit of `A`), so `g ↦ ψ g ψ^{-1}` is an isomorphism `L → V(A,P)`.

Let `h` be `x ↦ x/q` on `[0, q s_0)` followed by Lemma 1 on `[q s_0, 1) → [s_0, 1)`
(positive lengths `1 − q s_0` and `q`). Then `h ∈ Stab(0)` is increasing,
`h(x) = x/q` for `x < q s_0`, and `h(x) ≥ s_0` for `x ≥ q s_0`.

If `γ(g) = 1`, then `g` is the identity on some `[0, ε)`, `ε > 0`. While
`h^m(ε) < q s_0` we have `h^{m+1}(ε) = h^m(ε)/q`, so some `h^m(ε) ≥ q s_0`, and
then `ε_M = h^M(ε) ≥ s_0` for `M = m + 1`. As `h^M` is increasing and fixes `0`,
`h^M([0,ε)) = [0, ε_M) ⊇ [0, s_0)`, and `h^M g h^{-M}` is the identity there. So
`h^M g h^{-M} ∈ L` and `g ∈ <h, L>`.

**Finite generation.** Let `p_1, ..., p_k` generate `P`. For `g ∈ Stab(0)` write
`γ(g) = Π p_j^{e_j}` and `w = Π h_{p_j}^{e_j}`; as `P` is abelian, `γ(g w^{-1}) = 1`.
Hence `Stab(0) = <h_{p_1}, ..., h_{p_k}, h, L>` with `L ≅ V(A,P)`. Point
stabilizers are conjugate, so all are finitely generated when `V(A,P)` is.

**Type (A).** The action is faithful and 2-transitive with `|O| ≥ 2`, so by
`two-transitive-action-reduces-type-a-to-two-clauses` it is of type (A) exactly
when `V(A,P)` is finitely presented and `Stab(0)` is finitely generated. Finite
presentation implies finite generation, which gives finitely generated
stabilizers by the above. The subgroup consequences are Zaremsky's Corollary B,
`type-a-action-gives-boone-higman-for-subgroups`, and PBH is by definition
membership in a group admitting a type (A) action. ∎

## Hypotheses for the three instances

- `Z[1/2]`, `<2>`: `2` is a unit; `m/2^k = m · 2^{-k}`; `1 = 1/2 + 1/2`.
- `Z[1/6]`, `<2,3>`: `2, 3` are units; `m/6^k` is `m` copies of `6^{-k} ∈ P`;
  `1 = 1/2 + 1/2`.
- `Z[τ]`, `τ = (√5 − 1)/2`, `<τ>`: `τ(1 + τ) = τ² + τ = 1`, so `τ` is a unit and
  `1 = τ + τ²`. For (S), let `a = m + nτ > 0` with `m, n ∈ Z` and `φ = 1/τ = 1 + τ`.
  Then `(m + nτ)φ = (m + n) + mτ`, so by induction `aφ^N = m_N + n_N τ` with
  `m_N = F_{N+1} m + F_N n` and `n_N = F_N m + F_{N-1} n` (`F_{-1} = 1`, `F_0 = 0`).
  Binet's identity `F_{N+1} − φ F_N = ψ^N`, `ψ = −τ`, gives
  `m_N = F_N φ a + ψ^N m` and `n_N = F_{N-1} φ a + ψ^{N-1} m`, using `φa = φm + n`.
  Since `F_N → ∞` and `|ψ| < 1`, both are positive for large `N`, and
  `a = m_N τ^N + n_N τ^{N+1}` is a sum of `m_N + n_N` elements of `P`.
