---
rg: 2
id: prufer-groups-do-not-embed-in-gl-infinity-q
kind: claim
title: No Prufer group Z(p^infinity) embeds in the finitary group GL_infinity(K) of a number field K, so GL_n(Qbar) lies in no such group
distinct_from:
  number-field-linear-groups-embed-in-gl-n-q: that embeds GL_n(K) in GL_nd(Q) for a number field K; this shows the algebraic closure Qbar cannot be reached that way, even with unbounded matrix size.
  gl-n-q-targets-are-cofinal-in-n: that moves between GL_n(Q), SL_n(Q) and PGL_n(Q); this is an obstruction to leaving number fields.
artifacts:
  - research/artifacts/gq-gq-transfer-consequences.md
---

**ESTABLISHED** by `prufer-groups-do-not-embed-in-gl-infinity-q-proof`
(elementary lane proof; not independently reviewed; no novelty claimed).

**Statement.** Let `K` be a number field and `GL_∞(K) = ⋃_N GL_N(K)`, with
`GL_N(K) -> GL_(N+1)(K)`, `g ↦ diag(g,1)`. For every prime `p` the Prüfer group
`Z(p^∞)` does not embed in `GL_∞(K)`. Since `μ_(p^∞) ≅ Z(p^∞)` lies in
`Qbar^x = GL_1(Qbar)`, for every `n >= 1` the group `GL_n(Qbar)` embeds in no
`GL_N(K)` and in no `GL_∞(K)` with `K` a number field.

**Proof.**
1. `GL_∞(K)` acts on `V = ⊕_(j>=1) K e_j`. An element of `GL_N(K)` fixes `e_j`
   for `j > N`, so `c(g) = dim_K (g − 1)V` is finite for every `g in GL_∞(K)`.
2. Suppose `ι: Z(p^∞) -> GL_∞(K)` is injective, and let `x` generate the
   subgroup of order `p`. For each `k` choose `u` of order `p^k` with
   `u^(p^(k−1)) = x`. Such a `u` exists: `p^(k−1)u` generates the order-`p`
   subgroup, so replace `u` by a suitable multiple prime to `p`.
3. Put `y = ι(u) in GL_M(K)` and `W = K^M`. Then `y|_W` has order `p^k` and is
   diagonalizable over `Qbar`, with eigenvalues `p^k`-th roots of unity. Its
   characteristic polynomial has coefficients in `K`. So the multiplicity of an
   eigenvalue is constant on each `Gal(Qbar/K)`-orbit, and an orbit of primitive
   `p^k`-th roots has at least `φ(p^k)/[K:Q]` elements.
4. Because `y` has order exactly `p^k`, some eigenvalue is a primitive `p^k`-th
   root of unity. On the span of those eigenvectors, which has dimension at least
   `p^(k−1)(p−1)/[K:Q]`, the element `ι(x) = y^(p^(k−1))` acts by nontrivial
   `p`-th roots of unity.
5. Hence `c(ι(x)) >= p^(k−1)(p−1)/[K:Q]` for every `k`, which contradicts step 1.
