---
rg: 2
id: thompson-f-finite-breakpoint-moment-not-liouville-proof
kind: route
title: Breakpoint lamps stabilize under a transient doubly stochastic dyadic walk and yield nonconstant harmonic functions
target: thompson-f-finite-breakpoint-moment-walks-are-not-liouville
requires: [thompson-f-dyadic-orbit-walks-are-transient]
---

Notation: `F` acts on `[0,1]` by increasing PL homeomorphisms with dyadic breakpoints and slopes in `2^Z`. `D` is
the set of dyadic rationals in `(0,1)`, and `F` acts transitively on `D`. The walk is `g_n = h_1 h_2 ⋯ h_n` with
`h_i` i.i.d. of law `µ`, and `µ`-harmonic means `u(g) = Σ_h µ(h) u(gh)`.

**Step 1 (breakpoint cocycle and affine action).** For `y ∈ D` put `β(g)(y) = log2 g'(y+) − log2 g'(y−) ∈ Z`.
It is nonzero exactly on `Br(g)`, so `β(g)` is finitely supported. The chain rule for increasing maps gives
`β(gh)(y) = β(g)(h y) + β(h)(y)`. Put `c(g) = β(g^{-1})` and `(g_lin φ)(z) = φ(g^{-1} z)` for `φ ∈ Z^D`. Then

`c(gh)(z) = β(h^{-1})(g^{-1}z) + β(g^{-1})(z)`, that is, `c(gh) = c(g) + g_lin c(h)`.

So `A_g φ = g_lin φ + c(g)` is a left action of `F` on `Z^D` (`A_g A_h = A_{gh}`). Also `|Br(h^{-1})| = |Br(h)|`,
because `Br(h^{-1}) = h(Br(h))`.

**Step 2 (flip count).** From Step 1, `c(g_n) = c(g_{n−1}) + (g_{n−1})_lin c(h_n)`, so for `z ∈ D`

`c(g_n)(z) − c(g_{n−1})(z) = β(h_n^{-1})(X_{n−1})`, where `X_n = g_n^{-1} z = h_n^{-1}(X_{n−1})` and `X_0 = z`.

Hence the lamp at `z` changes at time `n` only if `X_{n−1} ∈ Br(h_n^{-1})`. Here `X` is the Markov chain on `D`
with `P(x,y) = µ{h : h^{-1}x = y}`, and `h_n` is independent of `X_{n−1}`. With
`m(w) = µ{h : w ∈ Br(h^{-1})}` and Green function `G(z,w) = Σ_{n≥0} P^n(z,w)`,

`E #{n ≥ 1 : lamp at z changes at time n} ≤ Σ_{n≥1} P(X_{n−1} ∈ Br(h_n^{-1})) = Σ_w G(z,w) m(w)`.

**Step 3 (doubly stochastic Green bound).** `P` is doubly stochastic: `Σ_x P(x,y) = Σ_h µ(h) #{x : h^{-1}x = y} = 1`.
So `P*(x,y) = P(y,x)` is stochastic, `(P*)^n(w,z) = P^n(z,w)`, and `G(z,w) = G*(w,z)`. For any chain, `G*(w,z)` is
the hitting probability of `z` from `w` times `G*(z,z)`, hence `G*(w,z) ≤ G*(z,z) = G(z,z)`. Therefore

`Σ_w G(z,w) m(w) ≤ G(z,z) Σ_w m(w) = G(z,z) Σ_h µ(h)|Br(h^{-1})| = G(z,z) E_µ|Br(h)|`.

The chain `X` is the induced walk `x ↦ h'(x)` for `h' ~ µ̌`, and `sgr supp µ̌ = (sgr supp µ)^{-1} = F`. By
`thompson-f-dyadic-orbit-walks-are-transient` it is transient, so `G(z,z) < ∞` for every `z ∈ D`. Under condition 2,
almost surely every lamp changes only finitely often. Since `D` is countable, `C_∞ = lim_n c(g_n)` exists a.s.
coordinatewise in `Z^D`. Let `λ` be its law.

*Sharper form.* Assume only `Σ_w G(z0,w) m(w) < ∞` for one `z0`. Put `f(x) = P(lamp at x stabilizes)`. Writing
`g_n = h_1 g'_{n−1}` with `g'` the shifted walk, Step 1 gives `c(g_n)(x) = c(h_1)(x) + c(g'_{n−1})(h_1^{-1}x)`. So the
lamp at `x` stabilizes iff the shifted walk's lamp at `h_1^{-1}x` does, and `f = P f`. Now `f ≤ 1`, `f(z0) = 1`, and
`P` is irreducible on `D` (`sgr supp µ̌ = F` acts transitively). The maximum principle gives `f ≡ 1`, and the rest
of the proof is unchanged.

**Step 4 (stationarity and harmonic functions).** By the displayed identity in the sharper form,
`C_∞ = A_{h_1} C'_∞`, where `C'_∞` is the limit for the shifted walk. It is independent of `h_1` and has law `λ`. So
`λ = Σ_h µ(h) A_h λ` (push-forwards), that is, `λ` is `µ`-stationary. For `j ∈ Z`, `γ ∈ D` put

`u_{γ,j}(g) = (A_g λ)(φ(γ) = j) = λ{φ : (A_g φ)(γ) = j}`.

These are bounded by 1, and `Σ_h µ(h) u_{γ,j}(gh) = Σ_h µ(h) (A_g A_h λ)(φ(γ)=j) = (A_g λ)(φ(γ)=j) = u_{γ,j}(g)`.
So each `u_{γ,j}` is `µ`-harmonic.

**Step 5 (a nonconstant one).** Take `γ = 1/2` and let `k ∈ F` be the copy of `x0` supported on `[1/2, 1]`. Then
`k(1/2) = 1/2`, `k'(1/2−) = 1` and `k'(1/2+) ∈ {2, 1/2}`, so `d := c(k)(1/2) = β(k^{-1})(1/2) = ±1`. For every `φ`,
`(A_k φ)(1/2) = φ(k^{-1}(1/2)) + d = φ(1/2) + d`. Hence, with `p_j = λ(φ(1/2) = j)`, we get `u_{1/2,j}(k) = p_{j−d}`
and `u_{1/2,j}(e) = p_j`. If all `u_{1/2,j}` were constant, then `p_j = p_{j−d}` for all `j`, so `(p_j)` is
`|d|`-periodic on `Z`. Then `Σ_j p_j` is `0` or `∞`, not `1`, a contradiction. So some `u_{1/2,j}` is a nonconstant
bounded `µ`-harmonic function, and `(F, µ)` is not Liouville.

**Step 6 (corollary).** `Br(gh) ⊂ Br(h) ∪ h^{-1}Br(g)`, so `|Br|` is subadditive. The generators satisfy
`|Br(x0^{±1})| = 2` and `|Br(x1^{±1})| = 3`, so `|Br(g)| ≤ 3|g|_{x0,x1}`, and finite first moment implies condition 2.

**Where the argument stops.** Condition 2 enters only through `E #flips < ∞` in Steps 2–3. For a measure with
infinite Green-weighted breakpoint count, the lamps need not stabilize. By [Ers04b] (cited in 1602.02971 §7.A),
some amenable groups have no Liouville measure of finite entropy. So extending this kill to the finite-entropy
rung would still not decide amenability of `F`. The surviving Liouville candidates must spread breakpoints with
infinite expected count at every dyadic site.
