---
rg: 2
id: linear-proper-domain-duality-is-stable-finiteness-proof
kind: route
title: Post-surjectivity at zero makes a matrix onto on finite supports, and an idempotent image carries the one-sided inverse
target: linear-proper-domain-duality-is-stable-finiteness
requires: []
---

Notation as in the target. All matrices are `k × k` over `R = F[G]`. For a configuration `x ∈ A^G` and a matrix
`M`, `xM` is defined by the finite sum in the target. Three facts are used throughout.
- `x ↦ xM` commutes with the shift. The value `(xM)(g)` depends only on `x` restricted to `g·S^{-1}`, where `S` is
  the union of the supports of the entries of `M`.
- `(xM)N = x(MN)`, and `u ↦ uM` maps `R^k` into `R^k`.
- A configuration is asymptotic to `0` exactly when it lies in `R^k`. For a subshift `X`, write
  `X_fin = X ∩ R^k`.

**Step 0 (linear automata are restrictions of convolutions).** Let `Λ : X → A^G` be a linear automaton on a
linear subshift `X`.
- `Λ` has a finite memory set `S`. The value `x ↦ Λ(x)(e)` is continuous, hence locally constant, on the compact
  space `X`. So it depends only on `x|_S` for some finite `S`, by the Step 0 of
  `absorptions-give-post-surjective-strict-pairs-proof`.
- So `Λ(x)(e) = μ(x|_S)`, where `μ` is a map on the space `P = {x|_S : x ∈ X}`. That space is an
  `F`-subspace of `A^S`, and `μ` is `F`-linear on it because `Λ` is linear.
- Extend `μ` to an `F`-linear map `A^S → A` by choosing a complement of `P`.
- The extended map is `p ↦ Σ_{s ∈ S} p(s) C_s` for some `C_s ∈ Mat_k(F)`. Put `M = Σ_s C_s s^{-1}`, with the
  sign convention of the formula in the target.
- Then `xM` and `Λ(x)` agree at `e` for every `x ∈ X`, and both are equivariant, so `Λ(x) = xM` on `X`.

**Step 1 ((1) ⇒ (2)).** Assume `R` is stably finite. Let `X ⊆ A^G` be a linear subshift, and let
`Λ : X → A^G` be a post-surjective linear automaton. We show `X = A^G`.
- By Step 0, `Λ(x) = xM` for a matrix `M`.
- **`M` is onto on finite supports.** Take `0 ∈ X` and any `v ∈ R^k`. Then `v ~ 0 = Λ(0)`. Post-surjectivity
  gives `x' ∈ X` with `x' ~ 0` and `x'M = v`. So `x' ∈ X_fin`, and `X_fin M ⊇ R^k`. In particular
  `u ↦ uM` is a surjection of left `R`-modules `R^k → R^k`.
- **It splits.** `R^k` is free, so choose preimages of the basis vectors. Their rows form a matrix `N` with
  `NM = I`.
- **Stable finiteness.** It gives `MN = I`. So `u ↦ uM` is injective on `R^k`: if `uM = 0` then
  `u = uMN = 0`.
- **`X_fin` is everything.** Let `w ∈ R^k`. Then `wM ∈ R^k ⊆ X_fin M`, so `wM = vM` for some `v ∈ X_fin`.
  Injectivity gives `w = v ∈ X_fin`. So `X_fin = R^k`.
- **`X` is the full shift.** `R^k` is dense in `A^G`, and `X` is closed, so `X = A^G`.

So no proper linear subshift carries a post-surjective linear automaton onto `A^G`. Only post-surjectivity at
the single point `0` was used.

**Step 2 ((2) ⇒ (3)).** Under (2), the hypotheses of (3) are never met. A strongly post-surjective map is
post-surjective, so (3) holds vacuously.

**Step 3 ((3) ⇒ (1)), by contrapositive.** Suppose `NM = I` but `MN ≠ I`, for `k × k` matrices over `R`. Put
`E = MN`. Then `E² = M(NM)N = E`, and `E ≠ I`.

**(a) The domain.** Put `X = {x ∈ A^G : x(I − E) = 0}`.
- **Linear SFT.** `X` is closed, shift-invariant and linear. It is of finite type, because membership is the
  vanishing of a convolution with finite support.
- **`X` is the image of `E`.** If `x = yE` then `x(I − E) = yE − yE² = 0`. Conversely, if `x ∈ X` then
  `x = xE`. So `X = (A^G)E`, and `X_fin = R^k E`.
- **Proper.** Some entry of `I − E` is nonzero, say in row `i`. The basis row `u = e_i` (supported at `e`)
  has `u(I − E) ≠ 0`, so `u ∉ X`.
- **Strongly irreducible.** Let `S` be the union of the supports of the entries of `E`. Take `x_1, x_2 ∈ X`
  and finite `Ω_1, Ω_2 ⊆ G` with `Ω_1 S^{-1} ∩ Ω_2 S^{-1} = ∅`.
  - Write `x_j = y_j E`. Then `x_j|_{Ω_j}` depends only on `y_j|_{Ω_j S^{-1}}`.
  - Let `y` agree with `y_j` on `Ω_j S^{-1}`, for `j = 1, 2`, and be `0` elsewhere.
  - Then `yE ∈ X`, and it agrees with `x_j` on `Ω_j`.
  - The separation condition holds as soon as `Ω_2 ∩ Ω_1 S^{-1} S = ∅`. So `X` is strongly irreducible with
    gap set `S^{-1}S`.

**(b) The automaton.** Put `Λ(x) = xM²` on `X`. It is a linear automaton `X → A^G`.

**(c) Strong post-surjectivity with lifts in `X`.** Let `x ∈ X` and `z ~ Λ(x)`. Put `d = z − Λ(x) ∈ R^k` and
`x' = x + dN²`.
- **`x'` lies in `X`.** `dN² E = dN(NM)N = dN²`, so `dN² ∈ X_fin`, and `x' ∈ X`.
- **It is a lift.** `Λ(x') = xM² + dN(NM)M = xM² + dNM = xM² + d = z`.
- **Its support is bounded.** Let `T` be the union of the supports of the entries of `N`. Then `x'` differs
  from `x` only on `supp(d)·T²`. So `Φ = T²` works. Here `Δ(Λ(x), z) = supp(d)`.

**(d) Not pre-injective.** Some `w ∈ R^k` has `v = w(I − MN) ≠ 0`, because `MN ≠ I`. Put `u = vN`.
- **`vM = 0`.** `vM = wM − wM(NM) = 0`.
- **`u` lies in `X`.** `u = vN ∈ R^k N = R^k(NM)N = R^k NE ⊆ R^k E = X_fin`.
- **`u ≠ 0`.** `uM = vNM = v ≠ 0`.
- **Same image as `0`.** `Λ(u) = uM² = vM = 0 = Λ(0)`.

So `0` and `u` are distinct asymptotic points of `X` with the same image. The data `(X, Λ)` violate (3), with
the same `k`.

**Conclusion.** (1) ⇒ (2) is Step 1, (2) ⇒ (3) is Step 2, and not-(1) ⇒ not-(3) is Step 3. ∎

**Remark (sanity checks).**
- **Amenable groups.** For amenable `G`, `F[G]` is stably finite, so (2) holds. This agrees with the entropy
  argument in `proper-sft-domains-admit-no-dual-failures`.
- **Full shift.** On the full shift itself, `x ↦ xM` with `NM = I ≠ MN` is the Capobianco–Kari–Taati linear
  dual failure. Step 3 is that failure moved onto the proper idempotent image, with the map `M²` in place of
  `M`.
