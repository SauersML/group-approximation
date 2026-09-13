---
rg: 2
id: spectral-gap-refutes-exactification-on-nonamenable-groups-proof
kind: route
title: Run the Ornstein–Weiss map along Bowen's free subrelation, bound would-be right inverses by Kesten's spectral gap on the odd sector, and spread the failure by self-absorption
target: spectral-gap-refutes-exactification-on-nonamenable-groups
requires:
  - bernoulli-shifts-are-von-neumann-day
  - iid-density-iff-collapse-and-endomorphism-density
  - bernoulli-isomorphism-from-approximate-right-inverses
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
  - nonamenable-bernoulli-shifts-are-weakly-isomorphic
  - generators-dense-iff-zero-rokhlin-entropy
---

Notation of the target; `1 = 1_G`, addition mod 2. The proof follows `ornstein-weiss-map-has-no-approximate-right-inverses-proof`,
with cosets of a subgroup replaced by orbits of a subrelation.

**Item 1.**
- *Cocycles.* By the remarks on `bernoulli-shifts-are-von-neumann-day`, `T_s(u) = c_s(u)·u` with Borel `c_s` and `T_s`
  measure-preserving. `τ` is equivariant: `τ^(hu)_s(hg) = hg·c_s(g^-1 u)^-1 = h·τ^u_s(g)`.
- *Forest.* Site `g` corresponds to the point `g^-1 u`, and `τ^u_s(g)` to `c_s(g^-1 u)·g^-1 u = T_s(g^-1 u)`. So the
  graph on `G` with edges `{g, τ^u_s g}` is the Schreier graph of the `F_2`-action on the `G`-orbit of `u`. For a.e.
  `u` that action is free, so the graph is a disjoint union of Cayley trees of `F_2`, without loops, multiple edges or
  cycles.
- *Law.* A linear form in the coordinates of `δ_u(y)` with finitely many non-zero coefficients equals `Σ_h d_h y_h`.
  Here `d_h` is the parity of the number of weighted edges at `h`. A finite non-empty edge set of a forest has a
  vertex of odd degree, so the form is non-zero, and its character has mean zero given `u`. Hence `δ_u(y)` is i.i.d.
  uniform and independent of `u`.
- *Endomorphism.* `δ_(hu)(h·y) = h·δ_u(y)`, so `φ` is an equivariant, measure-preserving endomorphism. It ignores `w`,
  so it is not invertible.

**Item 2.**
- *Lift.* `Ω = U × {0,1}^G` with `(ρ × u_2)^G`, and `Π(u, z) = (u, δ_u z)`, which is equivariant and
  measure-preserving by item 1. Put `Ψ(u, z) = (−1)^(z_1 + f(Π(u,z))_1)`.
- *Lifted action.* `T~_s(u, z) = c_s(u)·(u, z) = (T_s u, c_s(u)·z)`. It is a bijection, with inverse through
  `T_s^-1`. It preserves measure: `T_s` does, and `z ↦ c·z` preserves `u_2^G`. The cocycle identity
  `c_(st)(u) = c_s(T_t u)·c_t(u)` makes it an `F_2`-action, free because `T` is free.
- *Almost invariance.* Put `c = c_s(u)`. Then `(c·z)_1 = z_(c^-1) = z_(τ^u_s 1)` and
  `f(Π(T~_s ω))_1 = f(c·Π ω)_1 = f(Π ω)_(τ_s 1)`. So `Ψ(T~_s ω)·Ψ(ω) = (−1)^(z_1 + z_(τ_s 1) + f_1 + f_(τ_s 1))`, where
  `z_1 + z_(τ_a 1) = y_1` and `z_1 + z_(τ_b 1) = w_1`. Hence `||Ψ ∘ T~_s − Ψ||²` is 4 times the `s`-defect probability.
- *Oddness.* Let `O(u) ⊆ G` be the sites of the tree through `1`, and `σ(u, z) = (u, z + 1_(O(u)))`. `σ` preserves
  measure. `Π ∘ σ = Π`, because every edge has both endpoints in `O(u)` or neither. And `Ψ ∘ σ = −Ψ`.
- *Odd sector.* Expand `Ψ(u, z) = Σ_S c_S(u) χ_S(z)` over finite `S ⊆ G`. Oddness forces `c_S(u) = 0` unless
  `|S ∩ O(u)|` is odd. Let `Y = {(u, S) : |S ∩ O(u)| odd}`, with `ρ^G` times counting measure. Coefficients identify
  the odd functions isometrically with `L²(Y)`.
  - `Ψ ↦ Ψ ∘ T~_s` becomes composition with `(u, S) ↦ (T_s u, c_s(u)S)`. This uses `(c·z)_g = z_(c^-1 g)` and
    `O(T_s u) = c_s(u)·O(u)`.
  - These maps are measure-preserving bijections of `Y`, and they define a free `F_2`-action on `Y`.
- *Fundamental domain.* Fix a Borel linear order on `U`. For `(u, S) ∈ Y` the finite non-empty set
  `P(u, S) = {g^-1 u : g ∈ S ∩ O(u)}` of points of `F_2·u` is constant along the `F_2`-orbit of `(u, S)`. Put
  `D = {(u, S) ∈ Y : u = min P(u, S)}`, which is Borel. The orbit of `(u, S)` is `{(T_w u, c_w(u)S) : w ∈ F_2}`, and
  `w ↦ T_w u` is injective, so the orbit meets `D` exactly once. Hence `L²(Y) ≅ L²(D) ⊗ ℓ²(F_2)`, with `F_2` acting
  through the regular representation.
- *Kesten.* By Kesten's theorem (Trans. Amer. Math. Soc. 92 (1959)), `||λ(a) + λ(a)^* + λ(b) + λ(b)^*|| = 2√3` on
  `ℓ²(F_2)`. So for the unit vector `Ψ`:
  `||Ψ∘T~_a − Ψ||² + ||Ψ∘T~_b − Ψ||² = 4 − ⟨(V_a + V_a^* + V_b + V_b^*)Ψ, Ψ⟩ >= 4 − 2√3`,
  where `V_s Ψ = Ψ ∘ T~_s`. Dividing by 4 gives the bound.
- *Right inverses.* Let `ζ ∈ End_G(X)`, write `ζ(x) = (u', y', w')`, and put `ε = d(φ ∘ ζ, id)`. Take `f = y'`.
  - Since `φ(ζ(x)) = (u', δ_(u')(y'))`, we have `µ{u'_1 ≠ u_1} <= ε`, and the defects of `f` along `τ^(u')` are at
    most `ε`.
  - Fix `s`, a finite `W ⊆ G` and a function `C` of `u|W` with `ρ^G{c_s(u) ≠ C(u|W)} < η`. Both `u` and `u'` have
    law `ρ^G`, the second because `ζ` preserves measure. And `u'|W = u|W` off a set of measure `|W|·ε`, by
    invariance. So `µ{c_s(u') ≠ c_s(u)} <= 2η + |W|·ε`.
  - Put `η_s(ε) = inf over (W, C, η) of (2η + |W|·ε)`; it tends to `0` as `ε → 0`. Then the defects of `f` along
    `τ^u`, which is the `τ` of the bound above, are at most `ε + η_s(ε)`.
  - So `2ε + η_a(ε) + η_b(ε) >= 1 − √3/2`. The left side tends to `0` as `ε → 0`, so `ε >= c` for some `c > 0` that
    depends only on `c_a` and `c_b`.

  In the coset version the subrelation does not depend on the point, and the constant `(2 − √3)/4` survives for
  every equivariant Borel `ζ`.

**Item 3.** Let `H(κ) > log 4`.
- Choose a nontrivial finite `ρ` with `H(ρ) = H(κ) − log 4`. Then `X_κ ≅ X` by
  `bernoulli-shifts-with-equal-base-entropy-are-isomorphic`.
- `X` lacks ARI by item 2, so `X_κ` lacks it, by invariance (item 2 of `iid-density-iff-collapse-and-endomorphism-density`).
- DENSE implies ARI (item 4 of `bernoulli-isomorphism-from-approximate-right-inverses`), so DENSE(`X_κ`) fails.

**Item 4.** Suppose both have ARI, with `H(λ) = H(κ) + d` and `d > 0`.
- There are factor maps both ways (`nonamenable-bernoulli-shifts-are-weakly-isomorphic`). Item 3 of
  `bernoulli-isomorphism-from-approximate-right-inverses` gives `X_κ ≅ X_λ`.
- With `ρ_d` of entropy `d`, equal base entropy gives `X_λ ≅ X_κ × X_(ρ_d)`. So `X_κ ≅ X_κ × X_(ρ_d)^n` for every `n`.
- For `n` with `H(κ) + nd > log 4`, invariance of ARI contradicts item 3.

**Item 5.** Density in `Ind_λ(X_κ)` gives `X_κ ≅ X_λ` and DENSE(`X_λ`), by item 4, (a) ⇒ (d), of
`iid-density-iff-collapse-and-endomorphism-density`; `Fac` is non-empty by weak isomorphism. So both shifts have
ARI. This contradicts item 4 when `H(κ) ≠ H(λ)`, and item 3 when `H(λ) > log 4`.

**Item 6.** Let `A`, `B` be the factor joinings in the two directions, and suppose `A ⊆ cl(B)` and `B ⊆ cl(A)`.
- The category argument in the proof of item 3 of `bernoulli-isomorphism-from-approximate-right-inverses` uses only
  these inclusions and `A ≠ ∅`. So it gives an isomorphism `θ: X_κ → X_λ`.
- For `η ∈ End_G(X_λ)`, put `φ = θ^-1 ∘ η ∈ Fac_G(X_λ, X_κ)`. Then `graph(φ) ∈ A ⊆ cl(B)`, so there are
  `ψ_n ∈ Fac_G(X_κ, X_λ)` whose transposed graphs converge to `graph(φ)`.
- The (⇐) part of item 1 of that proof, with `φ` in place of an endomorphism, gives `d(φ ∘ ψ_n, id) → 0`.
- With `ζ_n = ψ_n ∘ θ^-1 ∈ End_G(X_λ)` we have `η ∘ ζ_n = θ ∘ (φ ∘ ψ_n) ∘ θ^-1 → id`, since conjugation by `θ` is a
  homeomorphism for the intrinsic topology.
- So `X_λ` has ARI, and so does `X_κ` by invariance. That contradicts item 4.

**Item 7.**
- *Nonamenability.* A group with zero supremum is not sofic, hence nonamenable (item 6 of
  `bernoulli-isomorphism-from-approximate-right-inverses`).
- *The three claims fail.* Items 3 and 5 refute each claim on every such group: each quantifies over all finite bases,
  including pairs of different entropy and entropies above `log 4`. Conversely, if no group has zero supremum, the
  claims hold vacuously.
- *Positive entropy.* If no free ergodic action of `G` has positive Rokhlin entropy, the supremum is `0` by definition.
  If the supremum is `0`, every free ergodic action has Rokhlin entropy `0`, by item 2 of
  `generators-dense-iff-zero-rokhlin-entropy`. So "no group has zero supremum" is "every group has a positive-entropy
  free ergodic action".
