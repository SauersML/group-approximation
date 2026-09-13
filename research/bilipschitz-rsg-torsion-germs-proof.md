---
rg: 2
id: bilipschitz-rsg-torsion-germs-proof
kind: route
title: Bi-Lipschitz nuclear maps make every element bi-Lipschitz, canonical shifts have positive exponent at rational points, and commensurability in a virtually cyclic germ group transfers the vanishing periodic exponent to the germ
target: bilipschitz-finite-nucleus-rsg-proper-power-germs-are-torsion
requires:
  - bilipschitz-proper-power-conjugates-have-zero-periodic-exponents
---

Notation is as in the target. Exponents `μ^±` and `ν^±` are as in
`bilipschitz-proper-power-conjugates-have-zero-periodic-exponents`, for the
metric `d_w`.

**Item 1 (imports).** From BBMZ, arXiv:2309.06224v3, as pinned verbatim on main.
- **RSG definition (line 637 of `hyperbolic_boone_higman.tex`):** "for every
  pair of cones `C_α, C_β ⊊ E` with `t(α)=t(β)`, there exists `g∈G` that maps
  `C_α` to `C_β` by the canonical similarity". This is quoted in
  `research/artifacts/bh-rational-similarity-hosts-2026-09-12.md` §3, with the
  local-action convention `f(α·ω) = f̄(α)·f|_α(ω)`, where `C_(f̄(α))` is the
  smallest cone containing `f(C_α)`.
- **`prop:CyclicStabilizers`:** "Let $G\leq \R_{\Gamma,E}$ be an RSG with a
  finite nucleus, and let $\omega\in E$ be a rational point. Then the group of
  germs\/ $[G]_\omega$ is virtually infinite cyclic." This is quoted in Item 1
  of `rsg-proper-power-germ-torsion-via-cyclic-germ-groups`.
- Neither was re-read in this lane; the MSI search for the TeX timed out.

**Item 2 (every element is bi-Lipschitz).** Let `g ∈ G`.
- **Deep pairs.**
  - All but finitely many local actions of `g` lie in `Nuc_G`. So there is `D`
    with `g|_α ∈ Nuc_G` whenever `|α| ≥ D`.
  - Let `C` be the largest bi-Lipschitz constant over the finite set `Nuc_G`.
  - Let `x ∧ y = α = α_0 γ` with `|α_0| = D`, `x = αξ`, `y = αξ'` and `ξ ∧ ξ'`
    empty, and put `n = g|_(α_0)`. Then
    `w(gx ∧ gy) - w(x ∧ y) = [w(ḡ(α)) - w(α)] + w(g|_α ξ ∧ g|_α ξ')`.
  - The last term lies in `[0, C]`, because `g|_α ∈ Nuc_G` and `ξ ∧ ξ'` is
    empty.
- **Bounded prefix lag.**
  - `ḡ(α) = ḡ(α_0)·β`, where `C_β` is the smallest cone containing `n(C_γ)`.
  - **Upper bound.** Let `γ*` be the longest common prefix of the points of
    `C_γ`, and choose `ω, ω' ∈ C_γ` with `ω ∧ ω' = γ*`. Suppose `γ*` had at least
    `|V(Γ)|` edges beyond `γ`. Those forced edges would repeat a vertex, so the
    continuation would be forced forever and `C_γ` would be a single point. No
    isolated points rules this out. So
    `w(β) ≤ w(nω ∧ nω') ≤ w(γ*) + C ≤ w(γ) + C + |V(Γ)|·max_e w(e)`.
  - **Lower bound.** Every pair in `n(C_γ)` shares a prefix of weight at least
    `w(γ) - C`. The shortest prefix of weight `≥ w(γ) - C` of one image point is
    then common to all of them, so `w(β) ≥ w(γ) - C`.
  - Hence `|w(ḡ(α)) - w(α)|` is bounded over all `α` with `|α| ≥ D`.
- **Shallow pairs.**
  - Only finitely many `α` have `|α| < D`.
  - For `x ∧ y = α` with next edges `s ≠ s'`, the points `gx` and `gy` lie in the
    disjoint compact sets `g(C_(αs))` and `g(C_(αs'))`. So `w(gx ∧ gy)` is
    bounded.
- So `ℓ_g` is bounded: `g` is `d_w`-bi-Lipschitz, and the target of the required
  claim applies to `G` acting on `(E, d_w)`.

**Item 3 (canonical shifts).** Write the rational point as `z = σ τ^∞`, with
`τ` a nonempty closed path at `t(σ)`. Lengthen `σ` so that `C_σ ⊊ E`.
- By Item 1 there is `c ∈ G` with `c(σξ) = στξ` for all `σξ ∈ C_σ`. Then
  `cz = z`, and `c^m(σξ) = στ^m ξ` for `m ≥ 0`.
- For `y = σξ ≠ z`, `z ∧ y = σ(τ^∞ ∧ ξ)` and
  `c^m z ∧ c^m y = στ^m (τ^∞ ∧ ξ)`. So `ℓ_(c^m)(z, y) = m w(τ)`, and
  `μ^±(c, z) = w(τ) > 0`.
- By Item 3 of the required proof, `μ^±(c^s, z) = s w(τ)` for every `s ∈ Z`.
- **Equal germs, equal exponents.** If two elements fixing `z` agree on a
  neighbourhood of `z`, their `m`-th powers agree on a smaller neighbourhood, so
  all `a_m` and `b_m` agree. In particular `[c]_z` has infinite order.

**Item 4 (commensurability).** Let `Λ` be virtually infinite cyclic, and let
`x, y ∈ Λ` both have infinite order. Then `x^A = y^B` for some nonzero `A, B`.
- As in Item 3 of `rsg-proper-power-germ-torsion-via-cyclic-germ-groups`, `Λ`
  has an infinite cyclic normal subgroup `<c_0>` of finite index.
- So `x^a = c_0^r` and `y^b = c_0^(r')` with `a, b ≥ 1` and `r, r' ≠ 0`. Hence
  `x^(a r') = y^(b r)`.

**Item 5 (conclusion).**
- Let `x = [g^p]_z` and `y = [c]_z`, in `[G]_z`, which is virtually infinite
  cyclic by Item 1.
- Suppose `x` has infinite order. By Item 4, `g^(pA)` and `c^B` agree near `z`,
  with `A, B ≠ 0`.
- By Item 3, the exponents of `c^B` at `z` are `B w(τ) ≠ 0`.
- The required claim gives `ν^±_z(g) = 0`. By Item 3 of its proof, every
  exponent of `g^(pA)` at `z` is then `0`. This is a contradiction.
- So `x` has finite order `N`, and `g^(pN)` is the identity on a neighbourhood
  of `z`.
