---
rg: 2
id: lifted-thompson-t-root-twist-cost-iff-euler-cup-product-proof
kind: route
title: Second-order telescoping of a zero-exponent word for z gives the square-root floor; Weyl operators on Fock space lift a Kahler cocycle with area class e_R to genuine twisted representations; an ultralimit of rescaled almost-invariant vectors recovers such a cocycle from any square-root-rate sequence
target: lifted-thompson-t-root-twist-cost-iff-euler-cup-product
requires:
  - lifted-thompson-t-perfect-centre-cubically-elliptic
  - lifted-thompson-t-relative-t-forces-dyadic-twist-gap
  - thompson-v-has-haagerup-property
artifacts:
  - experiments/twist-cost-2026-09-17/second_order_checks.py
  - experiments/twist-cost-2026-09-17/second_order_checks.out
---

Notation is that of the target. Inner products are linear in the second slot. `S_+ ⊆ S` contains
one element from each pair `{s, s^{-1}}`. `F = F(S_+)` is the free group, and `q : F → T̄` is the
surjection sending each letter to itself. Every element of `T̄` is uniquely `z^n σ(g)`.

**Imported standard facts.**
- (CND) For a unitary representation `π` and a vector `ξ`, the function `x ↦ ‖π(x)ξ − ξ‖²` is cnd.
  Nonnegative combinations and pointwise limits of cnd functions are cnd. If `ψ` is cnd with
  `ψ(1) = 0`, then `ψ(x) = ‖c(x)‖²` for a 1-cocycle `c`, so `√ψ(xy) ≤ √ψ(x) + √ψ(y)`. A countable
  group is Haagerup iff it carries a proper cnd function. (Bekka–de la Harpe–Valette, *Kazhdan's
  property (T)*, §C.2; Cherix et al., *Groups with the Haagerup property*, Ch. 1.)
- (U) Ultraproducts of Hilbert spaces and of unitary representations, as in
  `lifted-thompson-t-relative-t-forces-dyadic-twist-gap-proof`. Inner products of classes of
  bounded sequences are the `U`-limits of the inner products.
- (Fock) The symmetric Fock space `Γ(H)` with exponential vectors `ε(v)`, `⟨ε(u), ε(v)⟩ = e^{⟨u,v⟩}`.
  The `ε(v)` are linearly independent and total. `Ω = ε(0)`. (Parthasarathy, *An introduction to
  quantum stochastic calculus*, Ch. II §19–20.) The formulas used below are re-derived here.
- (Div) `R` is divisible, so a homomorphism from a subgroup of a free abelian group to `R` extends
  to the whole group.

From the requires:
- `T̄` is perfect (`lifted-thompson-t-perfect-centre-cubically-elliptic`).
- `c` and `S` are as in `lifted-thompson-t-relative-t-forces-dyadic-twist-gap`.
- Thompson's `T` carries a proper cnd function `ψ_0` (Farley's cubical cocycle, recorded in
  `thompson-v-has-haagerup-property`).

## Step A. Cocycle identities

**A1.** For a unitary representation `π` of a group `G` and a 1-cocycle `b`, the function
`ω_b(g,h) = Im⟨b(g), π(g)b(h)⟩` satisfies `ω(g,h) + ω(gh,k) = ω(h,k) + ω(g,hk)`.

*Proof.* We have `b(hk) = b(h) + π(h)b(k)`, so
`ω(g,hk) = ω(g,h) + Im⟨b(g), π(gh)b(k)⟩`.
We also have `b(gh) = b(g) + π(g)b(h)`, and unitarity gives
`ω(gh,k) = Im⟨b(g), π(gh)b(k)⟩ + Im⟨b(h), π(h)b(k)⟩`.
Subtracting the two equations gives the identity. ∎

The same identity holds for every coboundary `dβ` and for `ε`. For `ε`, compare the two ways of
bracketing `σ(g)σ(h)σ(k)`.

`ε(1,h) = ε(g,1) = 0` because `σ(1) = 1`. Also `ω_b(1,h) = ω_b(g,1) = 0` because `b(1) = 0`.

**A2 (primitive).** Let `ξ` be a unit vector, `b(x) = π(x)ξ − ξ` and `f(x) = Im⟨ξ, π(x)ξ⟩`.
Then `df = ω_b` exactly.

*Proof.* Expand using unitarity:
`⟨b(g), π(g)b(h)⟩ = ⟨π(g)ξ − ξ, π(gh)ξ − π(g)ξ⟩ = ⟨ξ, π(h)ξ⟩ − 1 − ⟨ξ, π(gh)ξ⟩ + ⟨ξ, π(g)ξ⟩`.
Take imaginary parts: the right side becomes `f(h) − f(gh) + f(g) = (df)(g,h)`. ∎

This identity is check 1 of `experiments/twist-cost-2026-09-17/second_order_checks.py`
(maximum error `7.8e-16`).

## Step B. Statement (0)

**Linearity.**
- `0 = ω_0`, so `0 ∈ V_T`.
- Sums: `ω_{b_1 ⊕ b_2} = ω_{b_1} + ω_{b_2}` for `π_1 ⊕ π_2`.
- Nonnegative scalars: `ω_{√t b} = t ω_b` for `t ≥ 0`.
- Negation: on the conjugate space `H̄`, with `π̄` and the same map `b`, the inner product is
  conjugated, so `ω` changes sign.

Hence `V_T` is closed under real linear combinations.

**Kähler classes are cup products.** Regard `H` as the real Hilbert space `H_R` with
`⟨x,y⟩_R = Re⟨x,y⟩`. Then `π` is orthogonal. Multiplication by `i` is a real-orthogonal map `J`
that commutes with `π`, so `Jb` is again a cocycle. Since `⟨ix, y⟩ = −i⟨x,y⟩`, we get
`Im⟨x,y⟩ = Re⟨ix,y⟩`. Therefore `ω_b(g,h) = ⟨Jb(g), π(g)b(h)⟩_R = (Jb ∪ b)(g,h)`.

**Cup products are Kähler classes.**
1. *Symmetric part.* For one cocycle `b` of an orthogonal `π`, expand `‖b(gh)‖² = ‖b(g) + π(g)b(h)‖²`.
   This gives `b ∪ b = −½ d(‖b‖²)`. Polarizing,
   `b_1 ∪ b_2 + b_2 ∪ b_1 = (b_1+b_2) ∪ (b_1+b_2) − b_1 ∪ b_1 − b_2 ∪ b_2`
   is a coboundary.
2. *Complexify.* Let `H_C = H_R ⊗ C`, with
   `⟨x+iy, x'+iy'⟩ = ⟨x,x'⟩ + ⟨y,y'⟩ + i(⟨x,y'⟩ − ⟨y,x'⟩)`. Put `b = b_2 + i b_1`, a cocycle for
   `π ⊗ 1`. Then `ω_b = b_2 ∪ b_1 − b_1 ∪ b_2`.
3. By step 1 this is cohomologous to `−2 b_1 ∪ b_2`. So `[b_1 ∪ b_2] = −½[ω_b] ∈ V_T`. ∎

**Remark.** If `b` takes values in the real part `H_R ⊂ H_C` of a complexified orthogonal
representation, every `⟨b(g), π(g)b(h)⟩` is real, so `ω_b = 0`.

## Step C. Statement (1), the square-root floor

**The word `w`.** `T̄` is perfect, so `z ∈ [T̄, T̄]`. Since `q` is onto, `q([F,F]) = [T̄,T̄]`.
Choose `w ∈ [F,F]` with `q(w) = z`. As a word in the letters `s^{±1}` (`s ∈ S_+`), `w` has
length `m`, and for each `s` the letter `s` occurs as often as `s^{-1}`, say `a_s` times each.
Then `Σ_s a_s = m/2`.

**Telescoping.** Let `π(w) = U_1 U_2 ⋯ U_m`, where each `U_j` is `π(s)` or `π(s)^{-1}` for some
`s ∈ S_+`. Put `δ = max_{s∈S} ‖π(s)ξ − ξ‖`. Then `‖U_j ξ − ξ‖ ≤ δ` and
`‖U_j^{-1} ξ − ξ‖ = ‖ξ − U_j ξ‖ ≤ δ`.

Let `P_k = U_k ⋯ U_m`, so that `‖P_k ξ − ξ‖ ≤ (m−k+1)δ`. Then
`⟨ξ, U_k P_{k+1} ξ⟩ − 1 = (⟨ξ, U_k ξ⟩ − 1) + ⟨ξ, U_k(P_{k+1}ξ − ξ)⟩`, and
`⟨ξ, U_k(P_{k+1}ξ − ξ)⟩ = ⟨ξ, P_{k+1}ξ⟩ − 1 + ⟨U_k^{-1}ξ − ξ, P_{k+1}ξ − ξ⟩`.

The last term has absolute value at most `δ · (m−k)δ`. Induction on `k` gives

`|⟨ξ, π(w)ξ⟩ − 1 − Σ_j (⟨ξ, U_jξ⟩ − 1)| ≤ Σ_{k=1}^{m−1} (m−k) δ² = m(m−1)δ²/2`.

**First-order term.** Let `u_s = ⟨ξ, π(s)ξ⟩ − 1`. A letter `s^{-1}` contributes `ū_s`. So
`Σ_j (⟨ξ, U_jξ⟩ − 1) = Σ_s a_s (u_s + ū_s) = −Σ_s a_s ‖π(s)ξ − ξ‖²`,
which has absolute value at most `(m/2)δ²`.

**Conclusion.** `π(w) = π(z) = e(θ)I`, so `|e(θ) − 1| ≤ (m(m−1)/2 + m/2)δ² = m²δ²/2`. Taking
the infimum over `(π, ξ)` gives `c(θ) ≥ √(2|e(θ) − 1|)/m`.

Finally `|e(θ) − 1| = 2|sin πθ| ≥ 4‖θ‖`, because `sin πx ≥ 2x` on `[0, ½]`. ∎

Check 2 of the experiment tests the displayed inequality for random near-identity unitaries with
`m = 6`. The worst ratio is `0.139 ≤ 1`.

## Step D. Statement (2), the Kähler lift

Assume `e_R ∈ V_T`. Then there are a unitary representation `π` of `T` on `H`, a cocycle `b`, a
function `β : T → R` and `λ = 1` with `ω_b = λε + dβ`. The argument below works for any real
`λ ≠ 0`. Evaluating at `(1,1)` and using A1 gives `β(1) = (dβ)(1,1) = 0`.

**D1. Weyl operators.** For `u ∈ H` and a unitary `U` on `H`, define `W(u,U)` on exponential
vectors by `W(u,U)ε(v) = exp(−‖u‖²/2 − ⟨u, Uv⟩) ε(Uv + u)`.

*Isometry.* The inner product of `W(u,U)ε(v)` with `W(u,U)ε(v')` is
`exp(−‖u‖² − ⟨Uv,u⟩ − ⟨u,Uv'⟩ + ⟨Uv+u, Uv'+u⟩) = e^{⟨v,v'⟩}`. So `W(u,U)` extends from the span
of the linearly independent total set `{ε(v)}` to an isometry. Its range contains every
`ε(v')`, since `v' = Uv + u` is solvable. So `W(u,U)` is unitary.

*Composition.* Apply `W(w,V)` and then `W(u,U)` to `ε(v)`. The result is
`exp(−‖w‖²/2 − ⟨w,Vv⟩ − ‖u‖²/2 − ⟨u, UVv⟩ − ⟨u, Uw⟩) ε(UVv + Uw + u)`.

Compare with `W(u + Uw, UV)ε(v)`, using `‖u + Uw‖² = ‖u‖² + ‖w‖² + 2Re⟨u,Uw⟩` and
`⟨u+Uw, UVv⟩ = ⟨u,UVv⟩ + ⟨w,Vv⟩`. The exponents differ by
`−⟨u,Uw⟩ + Re⟨u,Uw⟩ = −i Im⟨u,Uw⟩`. Hence

`W(u,U) W(w,V) = e^{−i Im⟨u, Uw⟩} W(u + Uw, UV)`.

Also `W(0, I) = I`, and `W(u,U)Ω = e^{−‖u‖²/2} ε(u)`, so `⟨Ω, W(u,U)Ω⟩ = e^{−‖u‖²/2}`.

**D2. Twisted representations.** For `t > 0`, let `V_t(g) = e^{itβ(g)} W(√t b(g), π(g))` for
`g ∈ T`. By D1 and the cocycle law,
`W(√t b(g), π(g)) W(√t b(h), π(h)) = e^{−it ω_b(g,h)} W(√t b(gh), π(gh))`.

Substituting `ω_b = λε + dβ` gives `V_t(g) V_t(h) = e^{−itλ ε(g,h)} V_t(gh)`.

Define `ρ_t(z^n σ(g)) = e^{−itλn} V_t(g)`. The product rule in `T̄` is
`z^nσ(g) · z^{n'}σ(h) = z^{n+n'+ε(g,h)} σ(gh)`, and both sides of the multiplicativity equation
become `e^{−itλ(n+n'+ε(g,h))} V_t(gh)`. Also `ρ_t(1) = V_t(1) = e^{itβ(1)} W(0,I) = I`.

So `ρ_t` is a unitary representation of `T̄` with `ρ_t(z) = e^{−itλ} I`.

**D3. Defect.** Let `x = z^n σ(g)`. By D1,
`⟨Ω, ρ_t(x)Ω⟩ = e^{iφ} e^{−t‖b(g)‖²/2}` with `φ = t(β(g) − λn)`.

Use `1 − cos φ ≤ |φ|` and `1 − e^{−a} ≤ a`. Then
`1 − Re⟨Ω, ρ_t(x)Ω⟩ = (1 − e^{−a}) + e^{−a}(1 − cos φ) ≤ t A(x)`,
where `a = t‖b(g)‖²/2` and `A(x) = |β(g)| + |λ||n| + ‖b(g)‖²/2`.

Hence `‖ρ_t(x)Ω − Ω‖² = 2(1 − Re⟨Ω, ρ_t(x)Ω⟩) ≤ 2tA(x)`. Put `A = max_{s∈S} A(s)`.

**D4. Upper bound on `c`.** Let `0 < ‖θ‖ ≤ ½`, with representative `θ ∈ [−½, ½]`, and put
`t = 2π‖θ‖/|λ|`.
- `ρ_t(z) = e(−tλ/2π) = e(∓‖θ‖)`, according to the sign of `λ`.
- The conjugate representation `ρ̄_t` on the conjugate Fock space has `ρ̄_t(z) = e(±‖θ‖)` and the
  same defects.

One of `ρ_t`, `ρ̄_t` therefore has `z ↦ e(θ)`. So
`c(θ) ≤ √(2tA) = √(4πA/|λ|) · √‖θ‖`. Together with Step C this gives `c(θ) ≍ √‖θ‖`. ∎

**D5. Haagerup.** Let `t_k = π 2^{−k}/|λ|` and `w_k = 2^{k/2}`, and set
`ψ_1(x) = Σ_{k≥1} w_k (1 − Re⟨Ω, ρ_{t_k}(x)Ω⟩)`.
- *Converges and is cnd.* By D3 each term is at most `w_k t_k A(x)`, and `Σ w_k t_k < ∞`. Each
  term is `½‖ρ_{t_k}(x)Ω − Ω‖²`, which is cnd, so ψ_1 is cnd by (CND). Also `ψ_1(1) = 0` and
  `ψ_1 ≥ 0`.
- *Grows on the centre.* `ψ_1(z^n) = Σ_k w_k (1 − cos(π n 2^{−k}))`. If `2^{k−1} ≤ |n| < 2^k`,
  then `π|n|2^{−k} ∈ [π/2, π)`, so the `k`-th term is at least `w_k`. Hence
  `ψ_1(z^n) ≥ 2^{k/2} ≥ √|n|`.
- *Proper.* Put `ψ = ψ_0 ∘ p + ψ_1`. This is cnd. Suppose `ψ(x) ≤ R`.
  - Then `ψ_0(p(x)) ≤ R`, so `p(x)` lies in a finite set `F_R`.
  - Write `x = z^n σ(g)` with `g ∈ F_R`. By (CND), `√ψ_1(z^n) ≤ √ψ_1(x) + √ψ_1(σ(g)^{-1})`, which
    is at most `√R + max_{g∈F_R} √ψ_1(σ(g)^{-1})`.
  - So `|n|` is bounded, and `{ψ ≤ R}` is finite.

By (CND), `T̄` has the Haagerup property. ∎

## Step E. Statement (3), the converse

**E1. Setup.** Assume `liminf_{θ→0, θ≠0} c(θ)/√‖θ‖ < K_0 < ∞`.
- Choose `θ_n → 0`, with `θ_n ∈ [−½, ½] ∖ {0}` and all of one sign `σ_0 ∈ {±1}`.
- Choose representations `π_n` of `T̄` on `H_n` with `π_n(z) = e(θ_n)I`, and unit vectors `ξ_n`,
  such that `max_s ‖π_n(s)ξ_n − ξ_n‖ ≤ K√|θ_n|` with `K = K_0 + 1`.

Put `b_n(x) = (π_n(x)ξ_n − ξ_n)/√|θ_n|`, a cocycle for `π_n` on `T̄`, and
`f_n(x) = Im⟨ξ_n, π_n(x)ξ_n⟩/|θ_n|`.
- By A2 (both sides scale by `1/|θ_n|`), `df_n = ω_{b_n}`.
- `‖b_n(s)‖ ≤ K` for `s ∈ S`, so `‖b_n(x)‖ ≤ K|x|_S`.

**E2. Normalizing on the free group.** On `F`, let `B_n = b_n ∘ q` and `F_n = f_n ∘ q`, so that
`dF_n = ω_{B_n}`. Let `χ_n : F → R` be the homomorphism with `χ_n(s) = F_n(s)` for `s ∈ S_+`, and
put `η_n = F_n − χ_n`.
- Since `dχ_n = 0`, we have `dη_n = ω_{B_n}`, `η_n(1) = 0` and `η_n(s) = 0` for `s ∈ S_+`.
- `η_n(s^{-1}) = ω_{B_n}(s, s^{-1})`.
- `η_n(y s^{±1}) = η_n(y) + η_n(s^{±1}) − ω_{B_n}(y, s^{±1})`, and
  `|ω_{B_n}(y, y')| ≤ K²|y||y'|`.

Induction on word length gives `|η_n(y)| ≤ K²|y|²` for all `y ∈ F`, uniformly in `n`.

**E3. Three values of η_n.**
- (i) *On `ker q ∩ [F,F]`.* `F_n = f_n(1) = 0` and `χ_n = 0` there, so `η_n = 0` there.
- (ii) *At `w`, with `w` as in Step C.* `η_n(w) = f_n(z) − χ_n(w) = sin(2πθ_n)/|θ_n| → 2πσ_0`.
- (iii) *On `N = ker(p∘q)`.* `B_n(y) = b_n(z^k) = ((e(kθ_n) − 1)/√|θ_n|) ξ_n` for
  `y ∈ N` with `q(y) = z^k`. This has norm at most `2π|k|√|θ_n| → 0`.

**E4. Ultralimit.** Fix a nonprincipal ultrafilter `U` and form `π_U` on `H_U` by (U). Put
`b(x) = [b_n(x)]`, `B = b ∘ q` and `η = lim_U η_n`, which is finite by E2.
- `π_U(z) = lim_U e(θ_n) I = I`, and `b(z) = 0` by E3(iii).
- Hence `b(z^k x) = b(x) = b(x z^k)`, so `π_U` and `b` descend to a representation `π̄` of `T`
  and a cocycle `b̄` with `b = b̄ ∘ p`.
- Passing to the limit in `dη_n = ω_{B_n}` gives `dη = ω_{b̄} ∘ (pq × pq)`, since inner products
  converge.
- From E3: `η = 0` on `ker q ∩ [F,F]` and `η(w) = 2πσ_0`.
- For `y ∈ N`, `B(y) = b̄(1) = 0`, so `dη(y, y') = 0` whenever `y ∈ N` or `y' ∈ N`. In particular
  `η|_N` is a homomorphism.

**E5. The Euler cocycle on `F`.** Define `ν : F → Z` by `q(y) = z^{ν(y)} σ(pq(y))`. Then
`q(yy') = q(y)q(y')` gives `dν = −ε ∘ (pq × pq)`. By `ε(1,·) = ε(·,1) = 0`, `ν|_N` is a
homomorphism with `q(y) = z^{ν(y)}` on `N`.

**E6. Killing the free part.** Let `λ = −2πσ_0 ≠ 0` and `D = η + λν : F → R`. Then:
- `dD = (ω_{b̄} − λε) ∘ (pq × pq)`;
- `D|_N` is a homomorphism;
- for `y ∈ N ∩ [F,F]`, `y w^{−ν(y)} ∈ ker q ∩ [F,F]`, so additivity on `N` gives
  `η(y) = ν(y) η(w) = 2πσ_0 ν(y)`, and therefore `D(y) = 0`.

So `D|_N` factors through `N/(N ∩ [F,F]) ≅ N[F,F]/[F,F] ≤ F/[F,F] ≅ Z^{S_+}`. By (Div) it extends
to a homomorphism `χ : F → R`.

Put `E = D − χ`. Then `E|_N = 0` and `dE = dD`. For `y ∈ F` and `y' ∈ N`,
`E(yy') = E(y) + E(y') − (ω_{b̄} − λε)(pq(y), 1) = E(y)`.

So `E = β ∘ pq` for a function `β : T → R`, since `pq` is onto. Then `dβ = ω_{b̄} − λε` on `T`.
Hence `λ e_R = [ω_{b̄}] ∈ V_T`, and by (0), `e_R ∈ V_T`. ∎

## Step F. Dichotomy

- If `e_R ∈ V_T`, then Steps C and D give `c(θ) ≍ √‖θ‖` on all of `R/Z`, and `T̄` is Haagerup.
- If `e_R ∉ V_T`, then the contrapositive of Step E gives `c(θ)/√‖θ‖ → ∞` as `θ → 0`.

The two cases are exclusive. ∎
