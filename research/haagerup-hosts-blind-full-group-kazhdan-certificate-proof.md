---
rg: 2
id: haagerup-hosts-blind-full-group-kazhdan-certificate-proof
kind: route
title: Induce a C0 positive definite function along the full-group cocycle, extract an invariant vector by (T), and use recurrence against mixing of the representation
target: haagerup-hosts-blind-full-group-kazhdan-certificate
requires: []
---

Discard a null set so that `G` acts freely on `X`. For a Kazhdan group `Γ` write `(Q,ε)` for a Kazhdan pair.

**Step 0: the cocycle.** For `γ ∈ Γ` and `x ∈ X` let `α(γ,x) ∈ G` be the unique element with
`ρ(γ)x = α(γ,x)x`. It is Borel, since `ρ(γ) ∈ [R_G]` is piecewise a translation, and
`α(γγ',x) = α(γ, ρ(γ')x) α(γ',x)`. Discarding a `ρ(Γ)`-invariant null set, these identities hold at every point for
every `γ, γ'`. No bound on the range of `α(γ,·)` is used.

**Step 1: induced representation.** Let `φ` be a normalized positive definite function on `G`, `(π, H, ξ)` its GNS
triple. On `L^2(X, H)` put

```text
(U_γ f)(x) = π(α(γ, ρ(γ)^(-1)x)) f(ρ(γ)^(-1)x).
```

Put `z = ρ(γγ')^(-1)x`. The cocycle identity gives `U_γ U_γ' f(x) = π(α(γ, ρ(γ')z) α(γ',z)) f(z) = U_(γγ') f(x)`,
so `U` is a representation. It is unitary because `ρ(γ)` preserves `μ`. For the constant section `ξ̂ ≡ ξ`, the
substitution `y = ρ(γ)^(-1)x` gives

```text
⟨U_γ ξ̂, ξ̂⟩ = ∫ φ(α(γ, y)) dμ(y) =: Φ(γ).                                   (H1)
```

**Step 2: an invariant vector.** By the Haagerup property there are normalized positive definite `φ_t ∈ C_0(G)` with
`φ_t → 1` pointwise (Bekka--Cherix--Valette; Cherix--Cowling--Jolissaint--Julg--Valette, Definition 1.1.1).
Dominated convergence in `(H1)` gives `Φ_t → 1` pointwise on `Γ`. Fix `δ ∈ (0, 1/4]`, and choose `t` with
`2 − 2 Re Φ_t(q) <= (δε)^2` for the finitely many `q ∈ Q`. Then `||U_q ξ̂ − ξ̂|| <= δε` on `Q`. By
Bekka--de la Harpe--Valette, Proposition 1.1.9, the orthogonal projection `η` of `ξ̂` onto the `U`-invariant vectors
satisfies `||ξ̂ − η|| <= δ`. Invariance of `η`, after discarding one more invariant null set, reads

```text
η(ρ(γ)x) = π(α(γ,x)) η(x)       for every x and every γ ∈ Γ.                  (H2)
```

So `n(x) = ||η(x)||` is `ρ(Γ)`-invariant. Put `E = {n >= 1/2}`, which is `ρ(Γ)`-invariant. Since `||ξ|| = 1`, the set
`X ∖ E` lies in `{||η(x) − ξ|| >= 1/2}`. Chebyshev gives `μ(X ∖ E) <= 4δ^2`.

**Step 3: C_0 coefficients.** `π` is the GNS representation of `φ_t ∈ C_0(G)`. Coefficients `⟨π(g)u, v⟩` with `u, v` in
the span of `π(G)ξ` are finite combinations of translates of `φ_t`, hence in `C_0(G)`. By density and uniform limits,
`g ↦ ⟨π(g)u, u⟩` is in `C_0(G)` for every `u ∈ H`. `H` is separable, since `G` is countable.

**Step 4: recurrence lemma.** Let `R'` be the orbit relation of `ρ(Γ)` and `A` a Borel set. Then for a.e. `x ∈ A` with
infinite `R'`-class, the set `[x]_(R') ∩ A` is infinite.

Proof of the lemma:

* Let `B` be the set of `x ∈ A` with infinite class but finite `[x] ∩ A`. Then `R'|B` has finite classes, so it has a
  Borel transversal `T`.
* Enumerate `Γ = {γ_0 = e, γ_1, …}`. For `x ∈ T` and `k >= 0`, let `i_k(x)` be the `k`-th index `i` at which
  `ρ(γ_i)x` is a new point of the class. This is Borel, and defined for all `k` because classes are infinite.
* The sets `T_k = {ρ(γ_(i_k(x)))x : x ∈ T}` are pairwise disjoint. Each is the image of `T` under a countably-piecewise
  measure-preserving injection, so `μ(T_k) = μ(T)`.
* Infinitely many disjoint sets of measure `μ(T)` force `μ(T) = 0`. So `μ([T]) = 0` and `μ(B) = 0`. ∎

**Step 5: finite orbits on `E`.** Let `I ⊆ E` be the `ρ(Γ)`-invariant set of points with infinite orbit, and suppose
`μ(I) > 0`. Cover `H` by countably many open balls `B_j` of radius `1/8`. Some `A = I ∩ η^(-1)(B_j)` has positive
measure. By Step 4, a.e. `x ∈ A` has infinitely many `y ∈ [x] ∩ A`.

* Write `y = ρ(γ)x = g_y x` with `g_y = α(γ,x)`. Distinct `y` give distinct `g_y`, since `G` acts freely.
* By `(H2)`, `η(y) = π(g_y)η(x)`.
* Both `η(x)` and `η(y)` lie in `B_j`, so `||η(y) − η(x)|| < 1/4`, while `||η(x)|| = ||η(y)|| >= 1/2`. Hence

```text
Re ⟨π(g_y)η(x), η(x)⟩ = (||η(x)||^2 + ||η(y)||^2 − ||η(y) − η(x)||^2)/2 >= 1/4 − 1/32 > 0
```

for infinitely many distinct `g_y`. This contradicts Step 3 with `u = η(x)`. So `μ(I) = 0`, and a.e. orbit in `E` is
finite. As `δ → 0`, `μ(X ∖ E) → 0`, which proves clause 1.

**Step 6: clause 2.** Apply clause 1 to `L`: a.e. `ρ(L)`-orbit `O` is finite. Discard an `L`-invariant null set so that
every orbit is finite and every `f` below is pointwise invariant.

* **Normality on each orbit.** Let `Q_O` be the image of `L` in `Sym(O)`, and `P_O` the image of `Γ` (`O` is
  `ρ(Γ)`-invariant). If `gΓg^(-1) <= Γ`, the image of `g` conjugates `P_O` into itself. `P_O` is finite, so the
  conjugate equals `P_O` and the image of `g` normalizes `P_O`. Such `g` generate `L` by infranormality. So `P_O` is
  normal in `Q_O`.
* **Invariance.** Let `f` be `ρ(Γ)`-invariant, `l ∈ L` and `γ ∈ Γ`. Put `y = ρ(l^(-1))x` and `O = ρ(L)y`. By
  normality, some `γ' ∈ Γ` has `ρ(l^(-1)γl) = ρ(γ')` on `O`. Then

```text
f(ρ(l^(-1))ρ(γ)x) = f(ρ(l^(-1)γl) y) = f(ρ(γ')y) = f(y) = f(ρ(l^(-1))x).
```

So `f ∘ ρ(l^(-1))` is `ρ(Γ)`-invariant for every `l`, and `L^∞(X)^(ρ(Γ))` is `ρ(L)`-invariant. ∎

**The same for Bernoulli extensions over `R_(ρ(Γ))`.** In the extension `Y` with fibers `{0,1}^([x]_(R_G)/R')` the lift
`ρ̃(l)(x,ω) = (ρ(l)x, ω)` has the base orbits as orbits in the first coordinate. The computation of Step 6 uses only
`ρ(l^(-1)γl)y = ρ(γ')y` on base orbits, so it goes through verbatim for `ρ̃`.
