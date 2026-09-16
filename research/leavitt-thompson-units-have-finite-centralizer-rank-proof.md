---
rg: 2
id: leavitt-thompson-units-have-finite-centralizer-rank-proof
kind: route
title: Germs at attracting periodic points give a free module of finite rank, and the kernel is torsion by compactness of supports
target: leavitt-thompson-units-have-finite-centralizer-rank
requires: []
artifacts:
  - research/artifacts/leavitt-thompson-unit-centralizer-rank-2026-09-16.md
---

Full proof: `research/artifacts/leavitt-thompson-unit-centralizer-rank-2026-09-16.md`, Sections 1–3. Below,
`X = {0,1}^ω`, `L` is the maximal code length of `g`, `c(y) = |α_i| − |β_i|` on `[β_i]`, and
`c_n(x) = Σ_(i<n) c(g^i x)`.

1. **Groupoid model (Lemmas 1.1–1.5).**
   - Let `G = {(x, k, y) : σ^a x = σ^b y, k = a − b}` and `Z(α, β) = {(α z, |α| − |β|, β z)}`.
   - `φ(s_α t_β) = 1_(Z(α, β))` defines a unital homomorphism into convolution functions. It is injective: pad
     all terms to a common `|β|`, and distinct pairs then give disjoint sets.
   - So `φ(r) = 1_(W_r)`, where `W_r` is a finite disjoint union of sets `Z(α, β)`. It is closed in
     `X × Z × X`, `|k|` is bounded on it, and `π_1(W_r)` is compact.
   - `φ(u_g) = 1_B` with `B = {(g y, c(y), y)}`, and `u_g` has infinite order iff `g` does.
   - `u r = r u` iff `T(W_r) = W_r`, where `T(x, k, y) = (g x, k + c(x) − c(y), g y)`. Also
     `T^n(x, k, y) = (g^n x, k + c_n(x) − c_n(y), g^n y)`, and `W_(u^m r) = {(g^m x, c_m(x) + k, y)}`.
2. **Dynamics (Lemmas 2.1–2.8).**
   - **Rigid words.** For `|a| >= L`, `g(a z) = g_*(a) z` with `g_*` injective. Iterates of `a` stay rigid while
     their length is at least `L`, `c_n` is locally constant, and `g^n(ρ z) = ρ' z` forces
     `c_n = |ρ'| − |ρ|` on `[ρ]`.
   - **Classes.** Put `μ = inf_n c_n(x)` and `M = sup_n c_n(x)`, and let `A0`, `A+`, `B` be the classes where
     both are finite, only `μ` is finite, and `μ = −∞`.
   - **Bounded cocycle.** Rigid words of bounded length repeat, so `A0` is open and equals the set `P_0` of
     periodic points with `c_p = 0`. On a cylinder around each such point, some `g^p = id` and `c_p = 0`.
   - **`A+`.** Pigeonhole on ladder times `j` (with `c_n > c_j` for all `n > j`) gives `v, γ, p` with
     `g^p(v z) = v γ z`. Then `g^(j + mp) x -> v γ^∞ ∈ P_a` and `c_(j + mp)(x) = c_j(x) + m|γ|`.
   - **`B`.** Pull back the length-`L` prefix at new-minimum times, using the rigid words of `g^(-1)`. A repeated
     prefix `v` gives `g^(−p_k)(v z) = v ε_k z` with `ε_k^(p_2) = ε_2^(p_k)`. So `g^j x = v ε_2^∞` is a
     repelling periodic point, and `B = P_r`.
   - **Finiteness.** The limit `v γ^∞` depends only on `v`, so `P_a` has at most `2^L` orbits and is finite.
     So is `P_r = P_a(g^(-1))`.
   - **Punctured neighbourhoods.** If `y = a δ^∞ ∈ P_r` with `g^(-p)(a z) = a δ z`, every point of `[a] − {y}`
     has infinite orbit and lies in `A+`.
   - **Infinite order.** `X = A0` iff `g` has finite order. So for infinite order `P_a` and `P_r` are nonempty.
3. **Germ map (Lemma 3.1).**
   - Let `Φ = ⊕_(P_a × P_a) F_2[x^(±1)]` and `κ(r)_(p, p') = Σ_k [(p, k, p') ∈ W_r] x^k`.
   - Then `κ(u r) = t κ(r)` with `(t f)_(p, p') = x^(c(g^(-1) p)) f_(g^(-1) p, p')`.
   - `t` permutes the monomial basis, and `t^(|O|)` shifts `k` by `d_O >= 1`. So `Φ` is free over
     `F_2[t^(±1)]` of rank `N(g)`.
4. **Kernel is torsion (Lemma 3.2).** Let `r ∈ C_R(u)` with `κ(r) = 0`, and put `W = W_r`.
   - **(i)** `T^n(W) = W` bounds `c_n(x) − c_n(y)` on arrows, so both endpoints lie in the same class.
   - **(ii)** Suppose an arrow has endpoints in `A+`.
     - Along `n_m = J + m p p'` both endpoints converge to points of `P_a`.
     - The middle coordinate is affine in `m` (local constancy of `c_(J−j)`) and bounded, hence eventually
       constant.
     - Closedness of `W` then puts an arrow in `P_a × Z × P_a`, which is impossible.
   - **(iii)** Suppose an arrow in `Z(α, β) ⊆ W` has endpoints in `B = P_r`. Perturb `z` inside the punctured
     neighbourhoods. The resulting arrow of `Z(α, β)` has endpoints in `A+`, contradicting (ii).
   - **(iv)** So `π_1(W) ⊆ A0`. By compactness, `g^m = id` and `c_m = 0` on `π_1(W)`, so `W_(u^m r) = W` and
     `u^m r = r`.
5. **Rank (Theorem A).**
   - Localization at `F_2[u] − {0}` is exact and kills torsion, so it embeds `S^(-1) C_R(u)` in
     `F_2(t)^(N(g))`. So `rho(u_g) <= N(g)`.
   - `κ(1) != 0` in the torsion-free module `Φ`, so `rho >= 1`.
   - `C_R(u^(-1)) = C_R(u)`, the two localizations agree, and `u_g^(-1) = u_(g^(-1))`. So `rho <= N(g^(-1))`.
   - `rho` is invariant under conjugation by `w ∈ Q`. ∎
