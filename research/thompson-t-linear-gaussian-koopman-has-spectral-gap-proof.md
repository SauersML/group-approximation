---
rg: 2
id: thompson-t-linear-gaussian-koopman-has-spectral-gap-proof
kind: route
title: "Exponential vectors embed kappa_0 restricted to an orthogonal subgroup into the Fock space, so the chaos part is tempered on PSL_2(Z) by the Bergman-kernel embedding of the weight-2 discrete series into L^2(G); a non-Moebius element moves the vacuum, and a jump in the limit displacement makes the parabolic cocycle unbounded"
target: thompson-t-linear-gaussian-koopman-has-spectral-gap
requires:
  - symplectic-gaussian-actions-split-area-cocycles
  - thompson-t-dirichlet-space-restricted-symplectic-model
  - thompson-t-is-isomorphic-to-ppsl2z
---

Notation as in the target. `e(s) = e^{2πis}`. `D` is the open unit disc and `dA` is Lebesgue area
measure. `G = Aut(D) ≅ PSL_2(R)` and `K = Stab_G(0)`.

## Imports

- (L1) `symplectic-gaussian-actions-split-area-cocycles-proof`, Steps 0, 1 and 5 (graph,
  ESTABLISHED):
  - `ℓ_w` has law `N(0, ‖w‖²)`;
  - `ℓ_w ∘ Ŝ = ℓ_{S^*w}` a.e.;
  - `S` orthogonal implies `Ŝ_*γ = γ`;
  - the exponentials span a dense subspace of `L²(γ)`;
  - `ρ^*Jρ = J` for symplectic `ρ`.
- (L2) `thompson-t-dirichlet-space-restricted-symplectic-model` and its proof
  (graph, ESTABLISHED):
  - the smoothed model;
  - `V_f` is bounded (J4);
  - `ω(a, b) = ⟨Ja, b⟩` and `(Jφ)^_n = −i sgn(n) φ̂_n`;
  - `⟨φ, ψ⟩ = 2π Σ |n| φ̂_n \bar{ψ̂_n}`.
- (L3) `thompson-t-is-isomorphic-to-ppsl2z` (graph, ESTABLISHED): the definition of
  `PPSL_2(Z)` and of breakpoints.
- (L4) Hulanicki–Reiter: a discrete group `Γ` is amenable iff `λ_Γ` has almost invariant
  vectors. See Bekka–de la Harpe–Valette, *Kazhdan's property (T)*, Appendix G (Theorem G.3.2);
  not re-read verbatim.
  - Sanov: the matrices `[[1,2],[0,1]]` and `[[1,0],[2,1]]` generate a free group of rank 2. It
    meets `{±1}` trivially, so `PSL_2(Z)` contains `F_2` and is nonamenable.
- (L5) Standard facts:
  - the `G`-invariant measures on `G/K ≅ D` are the multiples of `dA(a)/(1 − |a|²)²`, and Haar
    measure on `G` pushes forward to one of them under `M ↦ M(0)`;
  - the Bergman space `A²(D)` has reproducing kernel `K_a(ζ) = 1/(π(1 − āζ)²)`, that is
    `f(a) = ∫_D f \bar{K_a} dA` (Hedenmalm–Korenblum–Zhu, *Theory of Bergman spaces*, Ch. 1);
  - a discrete subgroup `Γ ≤ G` has a Borel fundamental domain `Δ` for left multiplication, so
    `L²(G) ≅ ℓ²(Γ) ⊗ L²(Δ)` with `λ_G|_Γ ≅ λ_Γ ⊗ 1`;
  - the Poisson extension of a continuous function on `∂D` is continuous on `\bar{D}`.

## Part I: Theorem A

### Step 1. Exponential vectors

For `w ∈ H` put `G_w = exp(ℓ_w − ‖w‖²/2)`. By (L1), `ℓ_u + ℓ_v = ℓ_{u+v}` has law
`N(0, ‖u + v‖²)`. So `⟨G_u, G_v⟩ = e^{‖u+v‖²/2 − ‖u‖²/2 − ‖v‖²/2} = e^{⟨u, v⟩}`.
`G_w = e^{‖w‖²/2} E_{2w}` with `E_v` as in (L1), so the `G_w` span a dense subspace.

Let `𝔉 = ⊕_{n ≥ 0} H_C^{⊗n}` be the full Fock space, `Ω` the vacuum (`n = 0`), and
`ε(w) = ⊕_n w^{⊗n}/√(n!)`. Then `⟨ε(u), ε(v)⟩ = Σ_n ⟨u, v⟩^n / n! = e^{⟨u, v⟩}`.
- The two families have the same Gram kernel. So `U(Σ a_i G_{w_i}) = Σ a_i ε(w_i)` is well defined
  and isometric on the dense span, and it extends to an isometry `U : L²(γ) → 𝔉` with
  `U1 = UG_0 = Ω`.
- Let `g ∈ Γ`, so `ρ(g)` is orthogonal. Then `ρ(g)^` preserves `γ` (L1) and has inverse
  `(ρ(g)^{-1})^`. By (L1), `κ₀(g)G_w = G_w ∘ (ρ(g)^{-1})^ = exp(ℓ_{(ρ(g)^{-1})^* w} − ‖w‖²/2) = G_{ρ(g)w}`.
- So `Uκ₀(g) = Γ(ρ_C(g))U` on the span, hence everywhere, where `Γ(u) = ⊕ u^{⊗n}`.
- `κ₀(g)` is unitary and fixes `1`, so it preserves `1^⊥`. Since `U` is isometric,
  `U(1^⊥) ⊥ Ω`.

Hence `κ₀|_Γ` restricted to `1^⊥` is equivalent to a subrepresentation of
`⊕_{n ≥ 1} ρ_C^{⊗n}|_Γ`.

### Step 2. Temperedness of the chaos part

Fell absorption: for any unitary representation `σ` of `Γ` on `K`,
`δ_γ ⊗ v ↦ δ_γ ⊗ σ(γ)^{-1}v` intertwines `λ_Γ ⊗ σ` with `λ_Γ ⊗ 1_K`. By hypothesis 1,
`ρ_C ⊆ λ_Γ ⊗ 1_{K_0}`. By induction, `ρ_C^{⊗n} ⊆ λ_Γ ⊗ 1_{K_n}` for every `n ≥ 1`, and so is the
sum over `n ≥ 1`. So `κ₀|_{1^⊥}` restricted to `Γ` is contained in `λ_Γ ⊗ 1_{K'}` for some
Hilbert space `K'`.

Suppose `λ_Γ ⊗ 1_{K'}` (that is, `ℓ²(Γ, K')`) had almost invariant unit vectors `ξ_n`. Then
`|ξ_n|(γ) = ‖ξ_n(γ)‖` are unit vectors in `ℓ²(Γ)`. They satisfy
`‖λ(g)|ξ_n| − |ξ_n|‖ ≤ ‖λ(g)ξ_n − ξ_n‖`, so `λ_Γ` would have almost invariant vectors,
contradicting (L4). So there are a finite `F ⊆ Γ` and `δ > 0` with

    max_{g ∈ F} ‖κ₀(g)v − v‖ ≥ δ‖v‖    for all v ⊥ 1.

### Step 3. The vacuum is moved

`κ₀(h)1 = (d(ρ(h)^)_*γ/dγ)^{1/2}`. If this equals `1`, then `(ρ(h)^)_*γ = γ`. Under
`(ρ(h)^)_*γ` the law of `ℓ_w` is the law of `ℓ_w ∘ ρ(h)^ = ℓ_{ρ(h)^*w}` under `γ` (L1), which is
`N(0, ‖ρ(h)^*w‖²)`. Equality of laws gives `‖ρ(h)^*w‖ = ‖w‖` for all `w`. An invertible isometry is
orthogonal, so `ρ(h)` would be orthogonal, contrary to hypothesis 2. Hence
`η := ‖κ₀(h)1 − 1‖ > 0`.

### Step 4. Conclusion

Let `ξ` be a unit vector, and write `ξ = c1 + v` with `v ⊥ 1`, so `|c| ≤ 1`. Suppose
`‖κ₀(g)ξ − ξ‖ < ε` for all `g ∈ F ∪ {h}`.
- `κ₀(g)1 = 1` for `g ∈ F`, so Step 2 gives `δ‖v‖ < ε`.
- Then `ε > ‖κ₀(h)ξ − ξ‖ ≥ |c|η − 2‖v‖ ≥ (1 − ε/δ)η − 2ε/δ`.

This fails once `ε ≤ ε_0 := ηδ/(δ + η + 2)`. So the claimed inequality holds with `ε = ε_0`. ∎

## Part II: Theorem B

### Step 5. The Cayley transform (B.1, first half)

`ψ₀(x) = arctan(x)/π`, so `e(ψ₀(x)) = e^{2i arctan x} = (1 + ix)/(1 − ix) = −(x − i)/(x + i)`. This is
the restriction to `RP^1` of the Möbius map `C(z) = −(z − i)/(z + i)`, which sends the upper half
plane onto `D`.

So `ζ = e(s)` identifies `R/Z` with `∂D`, and for `g ∈ PSL_2(Z)` the smoothed map is
`M_g = CgC^{-1} ∈ G`. In particular, the smoothed `Γ` is a discrete subgroup of `G`, because
`C PSL_2(R) C^{-1} = G` and `PSL_2(Z)` is discrete.

### Step 6. Möbius maps act unitarily (B.1, second half)

Write `H_C = H^{1/2}(R/Z; C)/C = D_+ ⊕ D_−`, with `D_±` the classes carrying positive and
negative frequencies. These are the `∓i` eigenspaces of `J`, and they are orthogonal.

For `φ = Σ_{n ≥ 1} a_n e(ns) ∈ D_+`, put `Φ(ζ) = Σ a_n ζ^n`. Then
`∫_D |Φ'|² dA = Σ_n n² |a_n|² π/n = π Σ n|a_n|²`. So `𝒟 : φ ↦ √2 Φ'` is unitary from `D_+` onto
`A²(D)`: onto because `a_n = b_{n−1}/n` inverts it for `f = Σ b_m ζ^m ∈ A²`.

Let `M ∈ G` and `π(M)f = (f ∘ M^{-1})·(M^{-1})'`. Then `π(M)` is unitary on `A²`, by the change of
variables `ζ = M(ξ)`, whose area Jacobian is `|M'|²`. Now take a polynomial `φ ∈ D_+`.
- `M^{-1}` is holomorphic on a neighbourhood of `\bar{D}`, and so is `Φ ∘ M^{-1}`.
- Its Taylor series converges uniformly on `∂D`. So the boundary function `φ ∘ M^{-1}` has no
  negative frequencies, and modulo constants it lies in `D_+`.
- `𝒟(φ ∘ M^{-1}) = √2 (Φ ∘ M^{-1})' = π(M)𝒟φ`.

So `V_{M^{-1}}` maps a dense subspace of `D_+` isometrically into `D_+`. It is bounded (L2), so it
maps `D_+` isometrically into `D_+`. The same holds for `M^{-1}`, so the map is unitary on `D_+`,
and `𝒟` intertwines it with `π(M)`. `V` commutes with complex conjugation, which exchanges
`D_+` and `D_−`, so `V_{M^{-1}}` is also unitary on `D_−`.

Hence for `g ∈ Γ`, `ρ(g) = V_{g^{-1}}` is unitary on `H_C`, orthogonal on `H`, and preserves both
eigenspaces of `J`, so it commutes with `J`. Moreover
`ρ_C|_Γ ≅ (π ∘ M)|_Γ ⊕ \overline{(π ∘ M)|_Γ}` (B.2, first half).

### Step 7. The weight-2 discrete series lies in `λ_G` (B.2, second half)

Let `M ∈ G` and `a = M(0)`. Then `M^{-1}(ζ) = e^{iθ}(ζ − a)/(1 − āζ)` for some `θ`, and

    π(M)1 = (M^{-1})' = e^{iθ}(1 − |a|²)/(1 − āζ)² = e^{iθ} π (1 − |a|²) K_a.

By (L5), `Wf(M) := ⟨f, π(M)1⟩ = e^{−iθ} π(1 − |a|²) f(a)`. Hence

    ∫_G |Wf|² dM = c π² ∫_D (1 − |a|²)² |f(a)|² dA(a)/(1 − |a|²)² = c π² ‖f‖²_{A²}

for the constant `c` of (L5). Moreover
`W(π(k)f)(M) = ⟨f, π(k^{-1}M)1⟩ = (λ_G(k)Wf)(M)`. So `(cπ²)^{-1/2} W` embeds `π` isometrically and
equivariantly into `λ_G`.

- Restricted to the discrete `Γ` (Step 5), `λ_G|_Γ ≅ λ_Γ ⊗ 1` (L5), so `π|_Γ` is contained in a
  multiple of `λ_Γ`.
- Complex conjugation on `ℓ²(Γ)` shows that `\bar{λ_Γ} ≅ λ_Γ`, so the conjugate is contained in
  one too.
- With Step 6, `ρ_C|_Γ` is contained in a multiple of `λ_Γ`. ∎ (B.2)

### Step 8. Orthogonal elements are Möbius (B.3)

Let `g ∈ PPSL_2(Z)`, with `h = ψ₀gψ₀^{-1}` its smoothed form, and suppose `ρ(g)` is orthogonal.
- `ρ(g)` is also symplectic. From `⟨Sx, Sy⟩ = ⟨x, y⟩`, `⟨a, b⟩ = ω(a, Jb)` and `ω(Sx, Sy) = ω(x, y)`
  we get `ω(Sx, (JS − SJ)y) = 0` for all `x, y`. As `S` is onto and `ω` is nondegenerate,
  `[ρ(g), J] = 0`.
- So `ρ(g^{-1}) = V_h` commutes with `J` and preserves `D_+`.
- `e ∈ D_+`, so `F := e ∘ h` has `F̂_n = 0` for `n < 0`. It is continuous, and `|F| = 1`.

Its Poisson extension `P[F] = Σ_{n ≥ 0} F̂_n ζ^n` is holomorphic on `D` and continuous on `\bar{D}`
(L5), with `|P[F]| = 1` on `∂D`.
- Its zeros lie in a compact subset of `D` and are isolated, hence finite. Let `B` be the finite
  Blaschke product over them.
- `P[F]/B` and `B/P[F]` are holomorphic and continuous on `\bar{D}`, with modulus `1` on `∂D`.
  By the maximum principle both are bounded by `1`, so `P[F]/B` is a unimodular constant.
- The winding number of `F` around `0` equals the degree of `h`, which is `1`. That of `B` is the
  number of its zeros. So `F(ζ) = λ(ζ − b)/(1 − b̄ζ)`, and `h` is the restriction of a disc
  automorphism.
- Then `g = C^{-1}(λB)C` on `RP^1` lies in `PSL_2(R)` (Step 5).
- `g` agrees with some `A ∈ PSL_2(Z)` on a nondegenerate arc (L3). Two elements of `PSL_2(R)`
  that agree at three points are equal, so `g = A ∈ PSL_2(Z)`.

*The element `g_0`.* The four pieces map the Farey arcs `[∞,0], [0,1], [1,2], [2,∞]` onto
`[∞,0], [0,1/2], [1/2,1], [1,∞]`, orientation-preservingly:
- `x/(x+1)` has matrix `[[1,0],[1,1]]`, and `1/(3 − x)` has matrix `[[0,1],[−1,3]]`, both of
  determinant 1;
- the values match at `0, 1, 2, ∞` (`0, 1/2, 1, ∞`).

So `g_0` is a homeomorphism in `PPSL_2(Z)`. If `g_0 ∈ PSL_2(R)`, then agreement with `x` on
`[∞, 0]` would force `g_0 = id`, but `x/(x+1) ≠ x` on `(0, 1)`. So `ρ(g_0)` is not orthogonal. ∎
(B.3)

### Step 9. B.4

By (L4), `Γ = PSL_2(Z)` is nonamenable. Steps 6–8 give the hypotheses of Theorem A with
`h = g_0`. ∎

### Step 10. The parabolic cocycle is unbounded (B.5)

*Douglas identity.* The kernel `sin^{-2}(π(x − y))` depends only on `x − y`. By Parseval and the
Fejér identity `∫_0^1 sin²(πnt)/sin²(πt) dt = |n|`,

    𝔇(φ) := ∬_{[0,1]²} |φ(x) − φ(y)|² / sin²(π(x − y)) dx dy = 4 Σ_n |n| |φ̂_n|² = (2/π) ‖φ‖².

`𝔇` is unchanged by adding constants.

*The cocycle.* `c(P^n) = u_{P^{-n}}`. In the coordinate `s = arctan(x)/π ∈ (−1/2, 1/2)`, the
point `∞` corresponds to `±1/2`. Take the lift of `P^{-n}` that fixes `1/2`. Then

    u_n(s) = arctan(tan(πs) − n)/π − s    for s ∈ (−1/2, 1/2),

which extends continuously and periodically with `u_n(±1/2) = 0`.

As `n → ∞`, `u_n(s) → u_∞(s) = −1/2 − s` for every `s ∈ (−1/2, 1/2)`. The limit tends to `−1` as
`s → 1/2⁻` and to `0` as `s → −1/2⁺`. Fix `δ < 1/4`.
- For `x ∈ (1/2 − δ, 1/2)` and `y ∈ (1/2, 1/2 + δ)` (read mod 1), we have
  `|u_∞(x) − u_∞(y)| ≥ 1 − 2δ` and `sin²(π(x − y)) ≤ π²(y − x)²`.
- So `𝔇(u_∞) ≥ ((1 − 2δ)²/π²) ∫_{1/2−δ}^{1/2} ∫_{1/2}^{1/2+δ} (y − x)^{-2} dy dx = ∞`, since the
  inner integral is at least `(1/2 − x)^{-1} − δ^{-1}`.

By Fatou's lemma applied to the integrands, `liminf_n 𝔇(u_n) ≥ 𝔇(u_∞) = ∞`. So
`‖c(P^n)‖² = (π/2) 𝔇(u_n) → ∞`.

A fixed point `v` of the affine action of `Γ` would give `c(g) = v − ρ(g)v`, with
`‖c(g)‖ ≤ 2‖v‖` on `Γ` (Step 6). So there is none. ∎ (B.5)
