---
rg: 2
id: lamplighter-host-finite-simple-limit-proof
kind: route
title: View models on configurations give surjective matrix models, marked convergence and expansion for the lamplighter host
target: lamplighter-host-is-limit-of-finite-simple-expanders
requires: [lamplighter-bernoulli-crossed-products-simple-kazhdan-lef, elementary-group-property-t-over-free-algebras]
artifacts:
  - research/artifacts/sk-strong-8-finite-simple-limits-2026-09-13.md
---

Full derivation: artifact §1–§3.

- **Models.** `Y_n = F_2^(Q_n)`. `Q_n` permutes coordinates, `a` translates by `1_e`, and `D_n(f)δ_y = F(y∘φ_n|_W)δ_y`. Put `Φ_n(Σ f_ℓ u_ℓ) = Σ D_n(f_ℓ)U_n(ψ_n ℓ)`.
- **Lemma 1** (partial homomorphism). Covariance `(ψ_n(ℓ)^(-1)y)(φ_n h) = (ℓ^(-1)(y∘φ_n))(h)` is checked on the letters `s` and `a` and extended by induction.
- **Lemma 2** (eventually nonzero). Choose a cylinder where the chosen coefficient is 1, with witness coordinates separating the finitely many `ℓx`; all configurations are legal and `Δ` is infinite. The targets `ψ_n(ℓ)y` are distinct, so `Φ_n(r)δ_y ≠ 0` for all large `n`.
- **Lemma 3** (onto).
  - Conjugates of `D_n(p)` by `Q_n` give the coordinate evaluations, hence all diagonal units.
  - Conjugates of the flip give every translation. So every matrix unit is reached, and `ρ_n` is onto `M_(2^|Q_n|)(F_2)`.
  - `ρ_n = Φ_n∘π` on bounded degree for large `n`.
- **Theorem.**
  - `EL_3(M_N(F_2)) = SL_(3N)(F_2)`. A word is trivial in `H` iff it is trivial in the approximant for large `n`, by Lemmas 2 and 3, so the marked groups converge.
  - `EL_3` over the free algebra has (T), so the marked finite quotients form expanders (Margulis; compare Kassabov 2007).

**Review (sk-verify-8, 2026-09-13, `research/artifacts/sk-review-8-2026-09-13-part1.md`):** Lemmas 1–3 and convergence PASS. GAP G1 in Theorem A, steps 1 and 3 (artifact §3), with a repair. The phrases "marked quotients of `Λ = EL_3(F)`" and "a Kazhdan pair `(Σ, ε)` with `Σ` the marking" fail, because `Σ = {e_ij(t)}` does not generate `EL_3(F)`. Use `Σ⁺ = Σ ∪ {e_ij(1)}`, a generating set of the Kazhdan group `EL_3(F)`. In every quotient `e_ij(1) = [e_ik(t_s), e_kj(t_s′)]` has length 4, so `(Σ, ε/4)` is a uniform Kazhdan pair.
