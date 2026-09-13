---
rg: 2
id: selfless-projection-traces-equal-k0-trace-image-proof
kind: route
title: Strict comparison moves the smaller half of a K_0 difference under the larger one and compresses the remainder into the unit
target: selfless-projection-traces-equal-k0-trace-image
requires:
  - robert-tracial-selfless-regularity
  - non-dihedral-free-products-are-completely-selfless
  - ozawa-php-groups-completely-selfless
  - zariski-dense-psl-subgroups-are-completely-selfless
  - vigdorovich-linear-selflessness
  - assembly-image-traces-are-integral-for-torsion-free-groups
  - unconditional-spectra-of-kk-witnesses-cross-the-gap
---

Extend `τ` to `A ⊗ K` as `τ ⊗ Tr`, written `τ_*` on projections of matrix algebras.

**Input.** By Robert's Theorem 3.1(ii) (`robert-tracial-selfless-regularity`, read verbatim from
arXiv:2309.14188v3), `A` has strict comparison by `τ` over `A ⊗ K`: for positive `a, b`,
`d_τ(a) < d_τ(b)` implies `a ≾ b` (Cuntz). For a projection `q`, `d_τ(q) = τ_*(q)`.

**Cuntz to Murray--von Neumann.** Let `p, q` be projections of `M_m(A)` with `p ≾ q`. Choose
`r ∈ M_N(A)`, `N >= m`, with `||r q r^* - p|| < 1/2`, and put `y = p r q`. Then
`||y y^* - p|| < 1/2`, so `y y^*` is invertible in `p M_N(A) p`. The element
`z = (y y^*)^(-1/2) y` satisfies `z z^* = p` and `z = z q`, so `p ~ z^* z <= q`. This is Step 2 of
`fractional-matrix-trace-gives-projection-in-g-star-z-proof`, repeated here.

**The lemma.** The inclusion `⊆` holds because `τ_*[e] = τ(e) ∈ [0,1]` for a projection
`e ∈ A`. For `⊇`, let `x ∈ K_0(A)` with `s = τ_*(x) ∈ [0,1]`.
- If `s = 0` or `s = 1`, take `e = 0` or `e = 1`.
- Otherwise `A` is unital, so `x = [p] - [q]` for projections `p, q ∈ M_N(A)`.
  - `τ_*(q) < τ_*(p)` because `s > 0`. Strict comparison gives `q ~ q' <= p`.
  - Then `r = p - q'` is a projection with `[r] = [p] - [q'] = [p] - [q] = x` and `τ_*(r) = s`.
  - Since `s < 1 = τ_*(1_1)`, where `1_1 = 1 ⊕ 0 ⊕ ... ⊕ 0`, strict comparison gives
    `r ~ e <= 1_1`. So `e` lies in the corner `A`.
  - `[e] = [r] = x` and `τ(e) = s`.

**The group instances.** Classes 1, 2 and 4 are the cited nodes as stated.
- Complete selflessness, where a node gives it, implies selflessness.
- Class 3 is `zariski-dense-psl-subgroups-are-completely-selfless`, whose body also proves that
  finite-index subgroups of `SL_3(Z)` are Zariski-dense in `SL_3(R) = PSL(3,R)`.

**Corollary.** Let `Γ` be torsion-free with `(C*_r Γ, τ)` selfless.
- *No witness gives integral traces.* If `C*_r(Γ)` has no projection other than `0` and `1`, the
  lemma leaves no `x ∈ K_0` with `τ_*(x) ∈ (0,1)`. Every `y ∈ K_0` has an integer translate
  `y - k[1]` with trace in `[0,1)`. So its trace is in `Z`.
- *Integral traces give no witness.* If `τ_*(K_0) ⊆ Z`, a projection `e ≠ 0, 1` would have
  `τ(e) ∈ (0,1)`, since `τ` is faithful.

**The `SL_3(Z)` instance.** A torsion-free finite-index `Γ <= SL_3(Z)` is in class 3. The two
integrality facts quoted in the claim are item 1 of
`unconditional-spectra-of-kk-witnesses-cross-the-gap` and
`assembly-image-traces-are-integral-for-torsion-free-groups`.

**The `C_2 * C_3` example.**
- `p = (1 + a)/2` and `q = (1 + b + b^2)/3` are projections of `C*_r(C_2 * C_3)`, of traces `1/2`
  and `1/3`.
- The lemma gives a projection `e` with `[e] = [p] - [q]` and `τ(e) = 1/6`.
- A projection of the form `|F|^(-1) sum_(f in F) f` has trace `1/|F|`. The finite subgroups of
  `C_2 * C_3` are conjugate into `C_2` or `C_3`, so such averages have trace `1`, `1/2` or `1/3`.
  So `e` is not a subgroup average.
