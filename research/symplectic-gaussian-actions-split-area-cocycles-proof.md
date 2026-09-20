---
rg: 2
id: symplectic-gaussian-actions-split-area-cocycles-proof
kind: route
title: "Feldman-Hajek makes restricted symplectic affine maps nonsingular on the Gaussian space; the Paley-Wiener functional of rho(g)^* J c(g) has coboundary the area cocycle; translations are strongly continuous, so small scalings keep almost invariant vectors"
target: symplectic-gaussian-actions-split-area-cocycles
requires:
  - central-extension-haagerup-from-measurable-euler-splitting
---

Notation as in the target. `(e_i)_{i ≥ 1}` is an orthonormal basis of `H`, `w_i = ⟨w, e_i⟩`.
For bounded `S` on `H`, `S^*` is the adjoint for `⟨,⟩`.

## Imports

- (I1) Feldman–Hájek theorem, as stated in Bogachev, *Gaussian Measures*, AMS Math. Surveys and
  Monographs 62 (1998), Theorem 2.7.2. The Hilbert-space form, quoted from its Wikipedia
  statement: for Gaussian measures `μ, ν` on a Hilbert space `X`, equivalence holds iff "μ and ν
  have the same Cameron–Martin space H = C_μ^(1/2)(X) = C_ν^(1/2)(X)", "the difference in their
  means lies in this common Cameron–Martin space, i.e. m_μ − m_ν ∈ H", and "the operator
  (C_μ^(−1/2)C_ν^(1/2))(C_μ^(−1/2)C_ν^(1/2))* − I is a Hilbert–Schmidt operator on H̄."
  Otherwise they are mutually singular.
- (I2) Standard: an `L²`-bounded martingale converges a.s. and in `L²`, and so does a
  Hilbert-space-valued one. The two-sided Laplace transform of `h ∈ L¹(R^n)` with
  `∫|h| e^{⟨s,y⟩} dy < ∞` for all `s` is entire, and it vanishes identically only if `h = 0`.
- (I3) `central-extension-haagerup-from-measurable-euler-splitting` (graph, ESTABLISHED), with
  the cocycle convention `β(gh, x) = β(g, hx) + β(h, x)` and Koopman convention
  `(κ(q)ξ)(x) = RN_q(x)^{1/2} ξ(q^{-1}x)`.

## Step 0. The model and Paley–Wiener functionals

`X = R^N`, `γ = ⊗ N(0,1)`, coordinates `x_i`. For `w ∈ H` let `C_w` be the set where
`Σ_i w_i x_i` converges, and `ℓ_w(x)` its sum there (`0` off `C_w`). The partial sums form an
`L²`-bounded martingale, so (I2) gives `γ(C_w) = 1`, `ℓ_w ∈ L²` with law `N(0, ‖w‖²)`, and
`ℓ_{w + w'} = ℓ_w + ℓ_{w'}` a.e. For `v ∈ H` (as a sequence `(v_i) ∈ ℓ²`), `Σ w_i v_i` converges
absolutely, so `C_w + v = C_w` and `ℓ_w(x + v) = ℓ_w(x) + ⟨w, v⟩` on `C_w`.

*Orthogonal invariance.* If `S` is orthogonal, the law of `(ℓ_{S^* e_j})_j` is centered Gaussian
with covariance `⟨S^*e_j, S^*e_k⟩ = δ_{jk}`, so it is `γ`.

*Translations.* For `v ∈ H` put `τ_v(x) = x + v`. Choose an orthogonal `S` with `v = ‖v‖ S e_1`.
The coordinates `y_j = ℓ_{S e_j}` are again i.i.d. `N(0,1)`, `y_1 = ℓ_v/‖v‖`, and `τ_v` shifts `y_j`
by `⟨S e_j, v⟩ = ‖v‖ δ_{j1}`. The map `x ↦ y` is `(S^*)^` in the notation of Step 1, which is a
measure-preserving bijection mod null sets with inverse `Ŝ` (Step 1, Lemma). So
`d(τ_v)_*γ/dγ = exp(ℓ_v − ‖v‖²/2)` by the one-dimensional computation, and in particular
`(τ_v)_*γ ~ γ`. This is also (I1) with equal covariances.

## Step 1. Measurable linear extensions

Let `S` be bounded and invertible on `H` with `SS^* − 1` Hilbert–Schmidt. Define the Borel map
`Ŝ : X → X`, `(Ŝx)_j = ℓ_{S^* e_j}(x)`.

*Nonsingularity.* `Ŝ_*γ` is the centered Gaussian measure on `R^N` with covariance
`⟨S^*e_j, S^*e_k⟩ = ⟨e_j, SS^* e_k⟩`. Both `γ` and `Ŝ_*γ` live on the Hilbert space
`X_2 = {x : Σ 2^{-i} x_i² < ∞}`, since `E Σ_j 2^{-j}(Ŝx)_j² = Σ_j 2^{-j}‖S^*e_j‖² < ∞`. Transport
`X_2` to `ℓ²` by the unitary `(Ux)_i = 2^{-i/2} x_i`. Then `γ ↦ N(0, K)` and
`Ŝ_*γ ↦ N(0, K^{1/2} SS^* K^{1/2})`, with `K = diag(2^{-i})`, in matrix coordinates for `(e_i)`.
- The Cameron–Martin spaces are `K^{1/2}ℓ²` and the range of `(K^{1/2}SS^*K^{1/2})^{1/2}`, which
  equals the range of `K^{1/2}S`, which is `K^{1/2}ℓ²` because `S` is invertible.
- The means are both `0`.
- `C_μ^{-1/2}C_ν^{1/2}(C_μ^{-1/2}C_ν^{1/2})^* = C_μ^{-1/2}C_νC_μ^{-1/2} = SS^*`, so the third
  condition of (I1) is `SS^* − 1 ∈ HS`.

So `Ŝ_*γ ~ γ` by (I1).

**Lemma.** For `w ∈ H`: `ℓ_w ∘ Ŝ = ℓ_{S^*w}` `γ`-a.e.

*Proof.* Since `Ŝ_*γ ~ γ`, for a.e. `x` the point `Ŝx` lies in `C_w`, and
`ℓ_w(Ŝx) = lim_n Σ_{j≤n} w_j ℓ_{S^*e_j}(x)`. The `n`-th term equals `ℓ_{S^*P_n w}(x)` a.e. (finite
linearity, Step 0), with `P_n` the projection onto `span(e_1..e_n)`. Now
`‖ℓ_{S^*P_nw} − ℓ_{S^*w}‖_{L²} = ‖S^*(P_nw − w)‖ → 0`. An a.e. limit and an `L²` limit of the same
sequence agree a.e. ∎

**Consequences** (each a.e.):
- (a) `(S_1 S_2)^ = Ŝ_1 Ŝ_2`: apply the Lemma coordinatewise, `ℓ_{S_1^*e_j}(Ŝ_2 x) = ℓ_{S_2^*S_1^*e_j}(x)`.
- (b) `1̂ = id`, since `ℓ_{e_j}(x) = x_j` everywhere. So `Ŝ` has a.e. inverse `(S^{-1})^`. Note
  that `S^{-1}(S^{-1})^* − 1 = S^{-1}(1 − SS^*)(S^{-1})^*` is Hilbert–Schmidt.
- (c) `Ŝ(x + v) = Ŝx + Sv` for `v ∈ H`, since `ℓ_{S^*e_j}(x + v) = ℓ_{S^*e_j}(x) + ⟨e_j, Sv⟩`.

Hence `Ŝ` is a nonsingular Borel automorphism of `(X, γ)` mod null sets.

*Symplectic maps qualify.* If `ρ` is symplectic, `ω(ρx, ρy) = ω(x, y)` reads `⟨Jρx, ρy⟩ = ⟨Jx, y⟩`
(because `ω(a, b) = ω(Ja, Jb) = ⟨Ja, b⟩`), so `ρ^*Jρ = J` and `ρ^* = −Jρ^{-1}J`. Then
`ρρ^* − 1 = −ρJρ^{-1}J − 1 = (Jρ − ρJ)ρ^{-1}J`, which is Hilbert–Schmidt when `[ρ, J]` is.

## Step 2. The affine action (part 1)

Fix `t ∈ R`. Put `A_g = τ_{t c(g)} ∘ ρ(g)^`, a nonsingular Borel automorphism mod null sets
(Step 0 and Step 1). By (a)–(c), a.e.

    A_g A_h x = ρ(g)^(ρ(h)^x + t c(h)) + t c(g) = ρ(gh)^x + t(ρ(g)c(h) + c(g)) = A_{gh} x,

and `A_e = id` a.e. Let `N` be the union of the countably many exceptional null sets of these
identities and of the identities (4.1) below (`g, h ∈ Q`). Put
`X_t = {x : A_g x ∉ N for all g ∈ Q}`. Its complement `⋃_g A_g^{-1}N` is null by nonsingularity.
If `x ∈ X_t` then `x ∉ N` (take `g = e`), so `A_g A_h x = A_{gh}x` for all `g, h`. Hence
`A_g(A_h x) = A_{gh}x ∉ N`, that is `A_h x ∈ X_t`. So `A` is a genuine action of `Q` on `X_t` by
Borel bijections (`A_{g^{-1}}` inverts `A_g`) that preserve null sets. `(X_t, γ)` is standard.

## Step 3. The area functional

Let `w(g) = ρ(g)^* J c(g)` and `F(g, x) = t ℓ_{w(g)}(x)`. So `F(g, ·)` is the measurable extension
of `x ↦ t ω(c(g), ρ(g)x) = t⟨Jc(g), ρ(g)x⟩`.

*Vector identity.* `ρ(h)^* w(g) + w(h) − w(gh) = 0`. Indeed, using `c(gh) = c(g) + ρ(g)c(h)` and
`ρ(g)^* J ρ(g) = J` (Step 1):

    ρ(h)^*ρ(g)^*Jc(g) + ρ(h)^*Jc(h) − ρ(gh)^*Jc(g) − ρ(h)^*ρ(g)^*Jρ(g)c(h)
      = ρ(h)^*Jc(h) − ρ(h)^*Jc(h) = 0.

*Scalar identity.* `⟨w(g), c(h)⟩ = ⟨Jc(g), ρ(g)c(h)⟩ = ω(c(g), ρ(g)c(h)) = Ω(g, h)`.

## Step 4. The splitting (part 2)

(4.1) For all `g, h` and a.e. `x`:

    F(g, A_h x) + F(h, x) − F(gh, x) = t² Ω(g, h).

*Proof.* By Step 0 (translation rule, valid since `ρ(h)^x ∈ C_{w(g)}` a.e. by nonsingularity) and
the Lemma, `ℓ_{w(g)}(ρ(h)^x + t c(h)) = ℓ_{ρ(h)^*w(g)}(x) + t⟨w(g), c(h)⟩`. Add `ℓ_{w(h)}(x)`,
subtract `ℓ_{w(gh)}(x)`, and use a.e. linearity of `w ↦ ℓ_w` with the two identities of Step 3.
Multiply by `t`. ∎

By the choice of `N`, (4.1) holds at every point of `X_t` (apply it at `x ∉ N`).

Now let `t ≠ 0` and `B(g, x) = (F(g, x) − t²β₀(g))/(t²a)`. By (4.1) and `Ω = aε + dβ₀`,

    B(g, A_h x) + B(h, x) − B(gh, x) = ε(g, h)    for all x ∈ X_t.

Define `β(σ(g)z^k, x) = B(g, x) + k`. Every element of `E` is uniquely `σ(g)z^k`, and `E` acts
through `Q`. Since `z` is central, `σ(g)z^k · σ(h)z^l = σ(gh)z^{ε(g,h)+k+l}`, so

    β(σ(g)z^k σ(h)z^l, x) = B(gh, x) + ε(g,h) + k + l = B(g, A_h x) + k + B(h, x) + l
                          = β(σ(g)z^k, A_h x) + β(σ(h)z^l, x).

Finally `β(z, x) = B(e, x) + 1`. Here `c(e) = 0`, so `w(e) = 0` and `F(e, ·) = 0`. Also `β₀(e) = 0`:
evaluate `Ω = aε + dβ₀` at `(e, e)`, where `Ω(e,e) = 0` and `ε(e,e) = 0` for a normalized section.
So `β(z, ·) = 1`. `β` is Borel because each `ℓ_w` is. This proves part 2.

## Step 5. Small scalings keep almost invariant vectors (part 3)

For a nonsingular automorphism `A` of `(X, γ)` let `κ(A)f = (dA_*γ/dγ)^{1/2} f∘A^{-1}`. This is
unitary on `L²(γ)` and `κ(AB) = κ(A)κ(B)` (chain rule for Radon–Nikodym derivatives). Write
`κ_t(g) = κ(A^t_g)`, the Koopman representation of Step 2 (a null set does not change `L²`).
Then `κ_t(g) = κ(τ_{tc(g)}) κ_0(g)`.

*Strong continuity of translations.* Let `E_v = κ(τ_v)1 = exp(ℓ_v/2 − ‖v‖²/4)` (Step 0).
- `⟨κ(τ_v)1, 1⟩ = ∫ exp(ℓ_v/2 − ‖v‖²/4) dγ = e^{−‖v‖²/8}`, because `ℓ_v ~ N(0, ‖v‖²)`.
- Since `κ(τ_{v+w}) = κ(τ_w)κ(τ_v)`, we get `‖κ(τ_v)E_w − E_w‖² = 2 − 2e^{−‖v‖²/8} → 0` as `v → 0`.
- The span of `{E_w : w ∈ H}` is dense. Suppose `f ∈ L²(γ)` is orthogonal to all `E_w`. Let
  `f_n = E[f | x_1..x_n]`, a function on `R^n`. Taking `w ∈ span(e_1..e_n)` with coordinates
  `2s`, we get `∫ f_n(y) e^{⟨s, y⟩} φ_n(y) dy = 0` for all `s ∈ R^n`, where `φ_n` is the standard
  Gaussian density. The function `h = f_nφ_n` satisfies `∫|h|e^{⟨s,y⟩} < ∞` for all `s`, by
  Cauchy–Schwarz. By (I2), `h = 0`, so `f_n = 0`. By martingale convergence (I2), `f = lim f_n = 0`.
- Unitary operators converging strongly on a dense set converge strongly (uniform bound 1). So
  `κ(τ_v) → 1` strongly as `‖v‖ → 0`.

*The witness.* Let `ξ_n` be unit vectors with `‖κ_0(g)ξ_n − ξ_n‖ → 0` for all `g`, and let
`S_1 ⊆ S_2 ⊆ …` be finite sets exhausting `Q`. Pass to a subsequence so that
`‖κ_0(g)ξ_n − ξ_n‖ < 1/n` on `S_n`. By strong continuity, choose `t_n ∈ (0, 1/n)` with
`‖κ(τ_{t_n c(g)})κ_0(g)ξ_n − κ_0(g)ξ_n‖ < 1/n` for the finitely many `g ∈ S_n`. Then
`‖κ_{t_n}(g)ξ_n − ξ_n‖ < 2/n` on `S_n`.

Let `W = ⊔_n X_{t_n}`, with `γ` on each piece and the action `A^{t_n}` on piece `n`. It is a
standard σ-finite space with a nonsingular `Q`-action, and `L²(W) = ⊕_n L²(X_{t_n}, γ)` with
Koopman representation `⊕_n κ_{t_n}`. The vectors `ξ_n`, placed on piece `n`, are unit vectors
with `‖κ(g)ξ_n − ξ_n‖ < 2/n` for `g ∈ S_n`, so they are almost invariant. Let `β` be `β_{t_n}`
(Step 4) on piece `n`. It is measurable, satisfies the cocycle identity everywhere, and has
`β(z, ·) = 1`.

So hypotheses 2 and 3 of (I3) hold for the extension `E` of `Q`. If `Q` is Haagerup, hypothesis 1
holds, and `E` is Haagerup. ∎

## The unitary case

If `ρ(g)J = Jρ(g)` for all `g`, then `ρ(g)` is orthogonal (`ρ^* = −Jρ^{-1}J = ρ^{-1}`). So
`ρ(g)^_*γ = γ` (Step 0, orthogonal invariance), `κ_0(g)1 = 1`, and the constant sequence `ξ_n = 1`
is invariant. Part 3 applies with no further hypothesis.
