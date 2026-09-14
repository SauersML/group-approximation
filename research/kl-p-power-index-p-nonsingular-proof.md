---
rg: 2
id: kl-p-power-index-p-nonsingular-proof
kind: route
title: Solve mod a central series, rewrite by a wreath-product cocycle, and invert the Fox derivative in F_p[Q]
target: kl-p-power-index-reduces-to-p-nonsingular-square-systems
requires: []
artifacts:
  - research/artifacts/hl-kl-torsion-pins-2026-09-13.md
---

Notation as in the target. `phi(s_1...s_j)` is written `q_j`-style when the base
coset is fixed.

**1. A root in `Q`, by induction on `|Q|`.** If `|Q| = 1` take `c = 1`. Otherwise
choose `Z <= Z(Q)` of order `p`.
- By induction on `Q/Z`, with coefficients reduced mod `Z`, there is `c in Q`
  with `w-(c) in Z`.
- For `z in Z`, centrality gives `w-(cz) = w-(c) z^m`, because each letter
  `t^(±1)` contributes `z^(±1)`.
- Since `p` does not divide `m`, `z -> z^m` is a bijection of `Z`. Choose `z`
  with `z^m = w-(c)^(-1)`.

**2. The Schreier basis.** Let `Y = {y_q}` be free letters and
`W = (H * F(Y))^Q ⋊ Q`, with product
`(f, a)(f', a') = (q -> f(q) f'(qa), aa')`.
- For `g in G` put `tau_g(q) = g_q g g_(q gH)^(-1)`. It lies in `H`, since its
  image in `Q` is `q (gH) (q gH)^(-1) = 1`. The cocycle rule
  `tau_(gg')(q) = tau_g(q) tau_(g')(q gH)` telescopes, so `g -> (tau_g, gH)` is a
  homomorphism `G -> W`.
- Send `t -> (q -> y_q, c)`. The universal property of `G * <t>` gives a
  homomorphism `Theta(x) = (tau_x, phi(x))`, and inverses satisfy
  `tau_(x^(-1))(a) = tau_x(a phi(x)^(-1))^(-1)`.
- On `M` the second coordinate is `1` and multiplication is pointwise, so
  `lambda(x) = tau_x(1)` is a homomorphism `M -> H * F(Y)`.

Let `psi : H * F(Y) -> M` be the inclusion on `H` and `y_q -> g_q t g_(qc)^(-1)`.
- *`psi` is injective.* `lambda psi (h) = g_1 h g_1^(-1) = h`. Also
  `lambda psi (y_q) = tau_(g_q)(1) tau_t(q) tau_(g_(qc)^(-1))(qc)`, where
  `tau_(g_q)(1) = g_q g_q^(-1) = 1` and
  `tau_(g_(qc)^(-1))(qc) = tau_(g_(qc))(1)^(-1) = 1`, so it equals `y_q`. Hence
  `lambda psi = id`.
- *`psi` is surjective.* For `x = s_1 ... s_l in M` put `q_i = phi(s_1...s_i)`,
  so `q_0 = q_l = 1`. Then `x = prod_i g_(q_(i-1)) s_i g_(q_i)^(-1)`. Each factor
  is in `H` if `s_i in G`, equals `y_(q_(i-1))` if `s_i = t`, and equals
  `y_(q_i)^(-1)` if `s_i = t^(-1)`, because then `q_i c = q_(i-1)`.

So `M = psi(H * F(Y))` and `lambda = psi^(-1)`.

**3. The square system.**
- Every `x in G * <t>` is `mu g_q` with `q = phi(x)` and `mu in M`. Since
  `phi(w) = w-(c) = 1`, every conjugate of `w` is an `M`-conjugate of some
  `g_q w g_q^(-1) in M`. Hence `<<w>> = <<g_q w g_q^(-1) : q in Q>>_M`.
- Put `rho_q = lambda(g_q w g_q^(-1))`. Its first factor `tau_(g_q)(1)` and its
  last factor `tau_(g_q^(-1))(q) = tau_(g_q)(1)^(-1)` are both `1`, so
  `rho_q = tau_w(q) = prod_j tau_(s_j)(q phi(s_1...s_(j-1)))`.
- Letters of `G` contribute elements of `H`. `s_j = t` contributes
  `y_(q phi(s_1...s_(j-1)))`. `s_j = t^(-1)` contributes
  `tau_t(q phi(s_1...s_(j-1)) c^(-1))^(-1) = y_(q phi(s_1...s_j))^(-1)`.
- So the exponent of `y_q'` in `rho_q` is `alpha(q^(-1) q')`, with `alpha` as in
  the target.

`E` is the matrix of `v -> v alpha` on `Z[Q]` in the basis `Q`, since
`e_q alpha = sum_x alpha(x) e_(qx)`. For invertibility mod `p`:
- The augmentation of `alpha` is `#{s_j = t} - #{s_j = t^(-1)} = m`.
- The augmentation ideal `I` of `F_p[Q]` is nilpotent. For a finite nonzero
  `F_p[Q]`-module `U`, `Q`-orbits have `p`-power size, so
  `|U^Q| ≡ |U| ≡ 0 (mod p)`. Since `0 in U^Q`, there is a nonzero fixed vector.
  So every simple module is trivial, `I` kills every composition factor of
  `F_p[Q]`, and `I^n = 0`.
- With `alpha ≡ m + beta`, `beta in I`, the inverse is
  `m^(-1) sum_(i<n) (-m^(-1) beta)^i`.
- Right multiplication by a unit is bijective, so the rows of `E` are
  independent over `F_p`, and the system is `p`-nonsingular in the sense pinned
  in the artifact.

**4. Equivalence.**
- Since `phi(w) = 1`, `phi` descends to `K = (G * <t>)/<<w>> -> Q`. The composite
  `G -> K -> Q` is the quotient map, so `ker(G -> K) <= H`.
- `H <= M`, and the image of `M` in `K` is `N = M/<<w>> ≅ (H * F(Y))/<<rho_q>>`.
- If `G -> K` is injective, so is `H -> N`. Conversely, if `H -> N` is injective
  the kernel lies in `H` and meets `H` trivially.
- By the pinned equivalence (arXiv:2309.09096 l.126--133), `H -> N` is injective
  iff the system `{rho_q = 1}` in unknowns `Y` is solvable over `H`.
