# EX review, groups: part 10. Atiyah base change under the determinant conjecture

Lane `ex-verify-groups`, 2026-09-13, ~01:45 CDT. Index: `ex-review-groups-2026-09-12.md`.
Reviewed for `ex-atiyah-base-change-td2`, which builds on these nodes. Lane `ex-atiyah-torsion-free`,
landings 2353ca2aca, 3838d36e60, d226d237e1.

Both theorems are conditional, and the hypotheses are named: `G` torsion-free, Strong Atiyah over `Q̄`,
Lück's determinant conjecture. The root `strong-atiyah-torsion-free` stays open, and so does
`determinant-conjecture-gives-full-atiyah-base-change`.

## 10.1 `determinant-conjecture-gives-one-variable-atiyah-base-change`. PASS (resultant plus Minkowski)

Re-derived from `research/artifacts/atiyah-one-variable-base-change-2026-09-12.md`, Sections 1–5.

**(R1) Higman linearization.** The identity was checked:
`[[1,-b],[0,1]][[a,b],[-c,1]][[1,0],[c,1]] = [[a+bc, 0],[0,1]]`. With `b = xI` and `c = B(x)`, the degree in `x`
drops. Elementary matrices over `Q̄[G][x]` specialize to invertibles, so the excess is unchanged.

**(R2) Square and full.** Let `W` project onto `n - r` pivot coordinates of the generic kernel, and let `Y`
complete the generic image.
- `M = [[L,Y],[W,0]]` is injective over `D(x)`: `Lv + Yu = 0` forces `u = 0` and `v ∈ ker L ∩ ker W = 0`.
- At `z_0`: `dim(ker L(z_0) ∩ ker W) >= (n-r+κ) + r - n = κ`, by additivity of von Neumann dimension.

**(R3) Integral coefficients.** Restriction of scalars along `O_F` is similar, by a `Q̄`-scalar matrix, to
`⊕_σ M^σ`. Conjugate excesses are `>= 0` by the Jacobson normal form over `D[x]`. Algebraic jumps are finite:
at central `ξ ∈ Q̄`, `f_i(ξ) ∈ D` is `0` or invertible, and a central root gives the central factor `x - ξ`.

**(RES).**
- The companion pencil `E = diag(1..1,a)`, with `F` superdiagonal plus last row `-c_i`, gives
  `det(xE - F) = p`, and `E^-1 F = VΛV^-1`.
- `(I ⊗ V^-1 E^-1) X (I ⊗ V) = ⊕_j M(α_j)` for `X = M_0 ⊗ E + M_1 ⊗ F ∈ M_(Nd)(Z[G])`.
- Multiplicativity for injective square operators and scalar invertibles (Lück Theorem 3.14, import), with
  `|det(V^-1E^-1) det V| = 1/|a|`, gives `Δ(X) = |a|^N Π_j Δ(M(α_j))`.

**(UB).**
- **Min-max.** On `ker M(z_0)`, `||M(α)v|| <= |α - z_0| ||M_1|| ||v||`. A dimension-`κ_0` submodule meets
  `ran χ_(ε,∞)` trivially, so `ν_(M(α))` has mass `>= κ_0` on `[0, ε]`.
- **Norm.** `||M(α)|| <= 2 c_M max(1,|α|)`.
- **Split.** Whichever of `ε` and the norm bound is larger, the bound
  `κ_0 log ε + (N-κ_0) log B` dominates `∫ log s dν`.
- `C_0 >= 1`, since a nonzero integral `M_1` has norm `>= 1`.

**(POLY).**
- `1 <= Δ(X) <= |a|^N C_0^d (|p(z_0)|/|a|)^(κ_0) (M(p)/|a|)^(N-κ_0) = C_0^d |p(z_0)|^(κ_0) M(p)^(N-κ_0)`.
- So `|p(z_0)| >= C_0^(-n/κ_0) M(p)^(-β)`, with `β = (N-κ_0)/κ_0` independent of `n`.

**Box principle.**
- **Real `z_0`.** Take the `(H+1)^(n+1)` coefficient vectors in `[0,H]^(n+1)`. Their values lie in an interval of
  length `(n+1) H max(1,|z_0|)^n`, which gives `|P_H(z_0)| <= c_1 H^(-n)`.
- **Complex `z_0`.** Squares give `H^(-(n-1)/2)`.
- **Factoring.**
  - `P_H = c Π p_i^(e_i)` with content `|c| >= 1`, so the inequality direction survives.
  - `Σ e_i <= n`, and by Landau `Π M(p_i)^(e_i) <= (n+1)^(1/2) H`.
  - The finitely many `m_i` satisfy `|m_i(z_0)| >= c_3 > 0`.
  - Hence `c_1 H^(-w) >= c_4^n (n+1)^(-β/2) H^(-β)` for all `H`, so `w <= β`.
- **Conclusion.** Take `n > β` (real) or `n > 2β+1` (complex). Then `κ_0 = 0` and `E_G = ∅`.

Items 1–3 then follow from `atiyah-base-change-holds-off-a-countable-set` (part 7 §7.4).

**Notes.**
- The FK properties are imported from Lück's book without re-reading (the node says so).
- Novelty: a bounded check, no web search. Keep it unreviewed for credit until `ex-novelty` looks.
- The superseded `determinant-conjecture-excludes-liouville-atiyah-exceptions` was not re-derived. The route
  uses it only for item 1, finiteness of algebraic jumps, which is re-derived above from the normal form.

## 10.2 `atiyah-base-change-in-transcendence-degree-one-under-det`. PASS

**Item 1.**
- **Setup.** Matrices involve finitely many coefficients, so reduce to `F = Q̄(C)` for a smooth affine curve `C`
  with a transcendental point.
- **Noether normalization.** It gives a finite `x : C -> A^1`, and `Q̄[C]` is free of rank `e` over the PID `Q̄[x]`.
  Restriction of scalars at unramified `z` is similar to `⊕_(x(P)=z) M(P)`.
- **Constant fibre sums.** By 10.1 the fibre sum `K` is constant off a finite algebraic `Z_0`.
- **Upper semicontinuity.** `k(P) = τ χ_(0)(|M(P)|)` is upper semicontinuous, by portmanteau for the closed set
  `{0}` under norm-continuous families.
- **Lower semicontinuity on `C°`.** `k(P') = K - Σ_(i>=2) k(P'_i) >= k(P) - (e-1)ε`, since unramified fibre
  points move continuously.
- **Conclusion.**
  - Algebraic points are dense and carry integers (Strong Atiyah over `Q̄`), so `k` is integer-valued, hence
    locally constant.
  - `C°` is connected, so `k` is constant on transcendental points.
  - This gives invariance.

**Items 2–3.** A transcendental eigenvalue of `C = U B^-1 V` over `D` is a kernel jump of
`[[B, V], [U, xI]]` at `z`. The generic kernel is `0`, because `xI - C` is invertible over `D(x)`, while it is
nonzero at `z`. So `z ∈ E_G = ∅`. Item 3 is the `1 x 1` case.

**What remains, correctly recorded.** Transcendence degree `>= 2`. The node's Attempts list five dead
approaches with the named dying step: the Kronecker distance product, Lelong or Siu algebraicity, iterated
resultants and transcendence measures, and so on. The next step needs Nesterenko–Philippon elimination.
