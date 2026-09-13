---
rg: 2
id: ornstein-weiss-map-has-no-approximate-right-inverses-proof
kind: route
title: A right inverse of the Ornstein–Weiss map yields an odd almost invariant vector for the free subgroup, which Kesten's spectral bound excludes, and self-absorption spreads the failure to every pair of entropies
target: ornstein-weiss-map-has-no-approximate-right-inverses
requires:
  - iid-density-iff-collapse-and-endomorphism-density
  - bernoulli-isomorphism-from-approximate-right-inverses
  - bernoulli-shifts-with-equal-base-entropy-are-isomorphic
  - nonamenable-bernoulli-shifts-are-weakly-isomorphic
---

Notation of the target. `(g·x)(h) = x(g^-1 h)`, addition is mod 2, and `1 = 1_G`.

**Item 1.**
- *Equivariance.* `δ(k·y)_g = y_(k^-1 g) + y_(k^-1 g a) = δ(y)_(k^-1 g)`, and likewise in the second component.
- *Law.* Fix finitely many sites with coefficient vectors `(c¹_g, c²_g) ∈ {0,1}²`, not all zero. Then
  `Σ_g c¹_g δ(y)¹_g + c²_g δ(y)²_g = Σ_h d_h y_h`, where `d_h` is the number mod 2 of weight-one edges at `h`. Here
  `c¹_g` weights the edge `{g, ga}` and `c²_g` weights the edge `{g, gb}`. These edges form a forest: each left coset
  `gF` carries the Cayley tree of `F`. A finite non-empty edge set in a forest has a vertex of odd degree, so `d ≠ 0`
  and `E[(−1)^(Σ d_h y_h)] = 0`. So all non-trivial characters of `δ(y)` have mean zero, and `δ(y)` is i.i.d. uniform.
- *Endomorphism.* `δ(y)` is independent of `r`, so `φ` pushes `(u_4 × ρ)^G` to itself. It ignores `w`, so it is
  not injective.

**Item 2.**
- *Lift.* Let `Ω` be the Bernoulli shift with base `{0,1} × R` and measure `(u_2 × ρ)^G`, with points `ω = (z, r)`.
  Put `Π(z, r) = (δ(z), r)`. By item 1, `Π` is equivariant and pushes the measure of `Ω` to `µ`. Define the unit
  vector `Ψ(ω) = (−1)^(z_1 + f(Π ω)_1)` in `L²(Ω)`.
- *Almost invariance.* Put `(s·Ψ)(ω) = Ψ(s^-1·ω)`.
  - `(a^-1·z)_1 = z_a`, and `f(Π(a^-1 ω))_1 = f(a^-1·Π ω)_1 = f(Π ω)_a` by equivariance.
  - Hence `Ψ(a^-1 ω)·Ψ(ω) = (−1)^(z_1 + z_a + f_1 + f_a)`, where `f = f(Π ω)`. Also `z_1 + z_a = y_1` for `x = Π ω`.
  - So `||a·Ψ − Ψ||² = 4·µ{f(x)_1 + f(x)_a ≠ y_1}`. In the same way `||b·Ψ − Ψ||² = 4·µ{f(x)_1 + f(x)_b ≠ w_1}`.
- *Mean zero.* Let `τ(z, r) = (z + 1_F, r)`, flipping `z` on the subgroup `F`. It preserves measure, and `Π ∘ τ = Π`
  because `g ∈ F ⇔ ga ∈ F ⇔ gb ∈ F`. Since `1 ∈ F`, `Ψ ∘ τ = −Ψ`, so `∫Ψ = 0`.
- *Spectral gap.* Choose an orthonormal basis `e_0 = 1, e_1, …` of `L²` of the finite base. The products
  `⊗_g e_(σ(g))`, for finitely supported index maps `σ` on `G`, form an orthonormal basis of `L²(Ω)`. `G` permutes them
  by translating `σ`, and `L²_0(Ω)` is spanned by those with non-empty support.
  - If `k ∈ F` fixes such a `σ`, it preserves its finite non-empty support. So `k` has finite order, and `k = 1`.
  - So `F` acts freely on this basis, and `L²_0(Ω)` is a direct sum of copies of `ℓ²(F)`.
- *Kesten.* By Kesten's theorem (H. Kesten, *Symmetric random walks on groups*, Trans. Amer. Math. Soc. 92 (1959)),
  `||λ(a) + λ(a^-1) + λ(b) + λ(b^-1)|| = 2√3` on `ℓ²(F_2)`, and hence on every direct sum of copies. For the unit
  vector `Ψ ∈ L²_0(Ω)`:
  `||aΨ − Ψ||² + ||bΨ − Ψ||² = 4 − ⟨(a + a^-1 + b + b^-1)Ψ, Ψ⟩ >= 4 − 2√3`.
- *Conclusion.* Dividing by 4 gives the displayed inequality. For `ζ` equivariant, take `f` = the `y`-component of
  `ζ`. Then `d(φ ∘ ζ, id) >= µ{δ(f(x))_1 ≠ (y_1, w_1)}`, which is at least the larger of the two defect
  probabilities, hence `>= (1 − √3/2)/2`. Only a positive spectral gap is needed qualitatively; nonamenability of
  `F_2` supplies one without the exact constant.

**Item 3.** Let `H(κ) >= log 4`.
- Choose a finite base `ρ` with `H(ρ) = H(κ) − log 4`, trivial if the difference is `0`. Then `X_κ ≅ X` by
  `bernoulli-shifts-with-equal-base-entropy-are-isomorphic`.
- By item 2, `φ` has no approximate right inverses in `End_G(X)`, so `X` lacks ARI. ARI is an isomorphism invariant,
  so `X_κ` lacks it too.
- DENSE implies ARI (item 4 of `bernoulli-isomorphism-from-approximate-right-inverses`), so DENSE(`X_κ`) fails.

**Item 4.** Suppose both have ARI and `H(λ) = H(κ) + d` with `d > 0`.
- `G` is nonamenable, so there are factor maps in both directions (`nonamenable-bernoulli-shifts-are-weakly-isomorphic`).
  Item 3 of `bernoulli-isomorphism-from-approximate-right-inverses` gives `X_κ ≅ X_λ`.
- Let `ρ_d` be a finite base with entropy `d`. Then `X_λ ≅ X_κ × X_(ρ_d)` by equal base entropy, so
  `X_κ ≅ X_κ × X_(ρ_d)`.
- Applying this to the first factor repeatedly gives `X_κ ≅ X_κ × X_(ρ_d)^n`, which is the Bernoulli shift with base
  `κ × ρ_d^n`, of entropy `H(κ) + nd`.
- For `n` with `H(κ) + nd >= log 4`, invariance of ARI and item 3 contradict ARI(`X_κ`).

**Item 5.** Suppose the generating partitions are dense in `Ind_λ(X_κ)`.
- `Fac_G(X_κ, X_λ) ≠ ∅` by nonamenability. Item 4, (a) ⇒ (d), of `iid-density-iff-collapse-and-endomorphism-density`
  gives `X_κ ≅ X_λ` and DENSE(`X_λ`).
- So `X_λ` has ARI, and by invariance so does `X_κ`.
- If `H(κ) ≠ H(λ)`, this contradicts item 4. If `H(λ) >= log 4`, it contradicts item 3.

**Consequences.** A group with zero supremum is not sofic (item 6 of
`bernoulli-isomorphism-from-approximate-right-inverses`). If it contains `F_2`, items 3–5 refute each of the three
claims, which quantify over all finite bases.
