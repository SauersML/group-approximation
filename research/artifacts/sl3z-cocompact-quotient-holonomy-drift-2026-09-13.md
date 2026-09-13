# SL_3(Z) on SL_3(R)/Λ: label holonomy of microstates, and norm drift (2026-09-13)

Lane `ex-sl3z-cocompact-quotient`. Continues `sl3z-cocompact-quotient-microstates-2026-09-13.md`.
Notation: `G = SL_3(R)`, `Γ = SL_3(Z)`, `Λ <= G` a cocompact lattice, `X = G/Λ`. `S = {e_ij^(±1)}` is the
set of 12 elementary matrices, `e_ij = I + E_ij`, and `⟨S | R⟩` is a finite presentation of `Γ` whose
relators have length at most `L`. `||·||` is the Euclidean operator norm.

## 1. Discreteness: a microstate carries Λ-labels that are flat on good relator cycles

Fix a right-invariant Riemannian metric `d` on `G`, so `d(xg, yg) = d(x,y)`. It induces the metric
`d̄(xΛ, yΛ) = min_λ d(x, yλ)` on `X`. Choose a compact `F ⊆ G` with `FΛ = G`, and put
`K = S^(<=L)·F ∪ F`. By compactness there is `C_1 >= 1` with `d(x e x^(−1), 1) <= C_1 d(e,1)` whenever
`x ∈ K ∪ K^(−1)` and `d(e,1) <= 1`. Put `r_Λ = min{ d(λ,1) : λ ∈ Λ ∖ {1} } > 0` and
`ε_0 = min(1, r_Λ/(2 L C_1^2))`. Right-invariance gives the two facts used repeatedly:
`d(ab,1) <= d(a,1) + d(b,1)` and `d(e^(−1),1) = d(e,1)`.

**Setting.** `V` is finite, `σ_s ∈ Sym(V)` for `s ∈ S` (no relation assumed), and `y : V → X`. Lift
`y(v) = g_vΛ` with `g_v ∈ F`. Fix `ε < ε_0`. The pair `(v,s)` is *good* if `d̄(y(σ_s v), s·y(v)) < ε`.

**Lemma 1.1 (labels).** For a good pair there is exactly one `λ = λ(v,s) ∈ Λ` with
`d(g_(σ_s v), s g_v λ) < ε`.

*Proof.* Existence is the definition of `d̄`. If `λ, λ'` both work, put `x = s g_v ∈ K` and
`μ = λ'λ^(−1)`. Then `2ε > d(xλ, xλ') = d(1, xμx^(−1))`, so `d(μ,1) <= 2C_1ε < r_Λ` and `μ = 1`. ∎

For a bad pair, let `λ(v,s)` be any minimizer of `d(g_(σ_s v), s g_v λ)`. Its value is at most
`D_X = diam(X)`.

**Lemma 1.2 (flatness).** Let `r = s_m ··· s_1 ∈ R`, and `v_0 ∈ V` with `v_i = σ_(s_i) v_(i−1)`. Suppose
`v_m = v_0` and all pairs `(v_(i−1), s_i)` are good. Then `λ(v_0,s_1) λ(v_1,s_2) ··· λ(v_(m−1),s_m) = 1`.

*Proof.* Put `λ_i = λ(v_(i−1), s_i)` and `e_i = g_(v_i) λ_i^(−1) g_(v_(i−1))^(−1) s_i^(−1)`. By
right-invariance `d(e_i,1) = d(g_(v_i), s_i g_(v_(i−1)) λ_i) < ε`, and `g_(v_i) = e_i s_i g_(v_(i−1)) λ_i`.
Iterating,

```text
g_(v_m) = E · (s_m ··· s_1) · g_(v_0) · λ_1 ··· λ_m ,     E = Π_(i=m..1) p_i e_i p_i^(−1),   p_i = s_m ··· s_(i+1).
```

Since `s_m ··· s_1 = 1` and `p_i ∈ K`, `d(E,1) <= m C_1 ε`. With `g = g_(v_0) = g_(v_m) ∈ F`, we get
`Λ_r := λ_1···λ_m = g^(−1)E^(−1)g`. So `d(Λ_r, 1) <= L C_1^2 ε < r_Λ`, and `Λ_r = 1`. ∎

**Definition 1.3 (the labelled system).** Put `Ω = V × Λ`, `σ̃_s(v, μ) = (σ_s v, λ(v,s)^(−1) μ)` and
`Φ(v, μ) = g_v μ ∈ G`. Then:

1. each `σ̃_s` is a bijection of `Ω` commuting with right translation by `Λ`;
2. `d(Φ(σ̃_s ω), s·Φ(ω)) = d(g_(σ_s v), s g_v λ(v,s))`, which is `< ε` on good pairs and `<= D_X` on all;
3. if `σ` is an honest action of `Γ` on `V` and every pair is good, then by Lemma 1.2 the maps `σ̃_s`
   satisfy the relators, so `Γ` acts on `Ω`. The stabilizer of `(v,μ)` is the kernel of the
   *holonomy* `ρ_v : Γ_v → Λ` at `v`. Here `ρ_v(γ)` is the inverse of the product of labels along any
   word for `γ ∈ Γ_v`. The product is well defined by flatness, and `ρ_v` is a homomorphism.

So a microstate is a discretized measure-equivalence coupling. `Γ` almost acts on `V × Λ`, commuting
with `Λ`, and `Φ` is an almost bi-equivariant map to `G`. For `Λ = SL_3(Z)` the Hecke models of
`sl3z-lattice-space-action-is-sofic` are the case where every pair is good. There the holonomy is the
Hecke conjugation `x ↦ axa^(−1)`, with infinite image. The lifts cannot stay in a compact set, which is
where cocompactness enters here.

## 2. Norm drift: no finite almost-invariant configurations in SL_3(R)

**Lemma 2.1.** For every `x ∈ SL_3(R)`,

```text
Σ_(s ∈ S) log||s x||  >=  12 log||x|| + κ,        κ = (1/2) log(128/81) > 0.
```

*Proof.* Take a unit `w` with `||xw|| = ||x||` and put `u = xw/||x||`, a unit vector. Then
`||sx|| >= ||sxw|| = ||x||·||su||`, so it suffices to show `Σ_s log||su|| >= κ`. Since
`e_ij^(±1)u = u ± u_j e_i`,

```text
||e_ij u||^2 · ||e_ij^(−1) u||^2 = (1 + u_j^2 + 2u_iu_j)(1 + u_j^2 − 2u_iu_j) = (1 + a)^2 − 4ab,
```

with `a = u_j^2` and `b = u_i^2`. This is `>= 1 − 2a + 5a^2 > 0`. Fix `j`. The two indices `i != j` have
`b_1 + b_2 = 1 − a`. The map `b ↦ log((1+a)^2 − 4ab)` is concave, so the sum of the two terms is at least
its value at an endpoint:

```text
log(1 − 2a + 5a^2) + 2 log(1 + a) = log((1 − 2a + 5a^2)(1 + a)^2) = log(1 + 2a^2 + 8a^3 + 5a^4) =: f(a) >= 0.
```

`f` is increasing on `[0,1]`, and some `j` has `u_j^2 >= 1/3`. So
`Σ_s log||su|| = (1/2) Σ_j Σ_(i != j) log(...) >= (1/2) f(1/3) = (1/2) log(128/81)`. ∎

**Theorem 2.2 (drift).** Let `O` be finite, `τ_s : O → O` bijections for `s ∈ S`, and `Φ : O → SL_3(R)`.
Write `N = log||Φ||`. Suppose that for all pairs `(ω,s)`, `N(τ_s ω) >= log||sΦ(ω)|| − B`, and that on all
but a proportion `θ` of the `12|O|` pairs, `N(τ_s ω) >= log||sΦ(ω)|| − η`. Then `κ <= 12(η + θB)`.

*Proof.* Each `τ_s` is a bijection, so `Σ_ω Σ_s [N(τ_s ω) − N(ω)] = 0`. Split each term as
`[N(τ_s ω) − log||sΦ(ω)||] + [log||sΦ(ω)|| − N(ω)]`. By Lemma 2.1 the second brackets sum to at least
`κ|O|`. The first brackets are at least `−η` on good pairs and `−B` on bad ones. So
`0 >= κ|O| − 12η|O| − 12θB|O|`. ∎

*Metric form.* If `d(Φ(τ_sω), sΦ(ω)) < ε` then `Φ(τ_sω) = e·sΦ(ω)` with `d(e,1) < ε`, so
`N(τ_sω) >= log||sΦ(ω)|| − log||e^(−1)||`. Take `η(ε) = sup{ log||e^(−1)|| : d(e,1) < ε } → 0` and
`B(D) = sup{ log||e^(−1)|| : d(e,1) <= D }`. Then `κ <= 12(η(ε) + θ B(D))`.

No group relations and no freeness are used, only bijectivity and non-amenable drift.

**Corollary 2.3 (finite labelled orbits cost a fixed fraction of defects).** Take a microstate at scale
`ε < ε_0` with `η(ε) < κ/12`, and its labelled system. Every finite `σ̃`-invariant subset `O ⊆ Ω`
contains a proportion at least `θ_* = (κ/12 − η(ε))/B(D_X) > 0` of bad pairs.

*Proof.* Apply Theorem 2.2 to `τ_s = σ̃_s|_O`. Definition 1.3(2) gives `B = B(D_X)` on all pairs and
`η(ε)` on good ones. ∎

In particular, in an honest finite `Γ`-action on which every pair is good, `Γ` has no finite orbit on
`Ω`. So every holonomy `ρ_v : Γ_v → Λ` has infinite image.
