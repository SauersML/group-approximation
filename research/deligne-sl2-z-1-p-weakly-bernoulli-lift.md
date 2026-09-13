---
rg: 2
id: deligne-sl2-z-1-p-weakly-bernoulli-lift
kind: claim
title: Every finite universal-cover quotient of SL_2(Z[1/p]) lifts some free action weakly equivalent to Bernoulli
distinct_from:
  weakly-bernoulli-liftable-actions-force-virtual-splitting: that is the open claim over w-rigid bases; this is the same existence question over a non-Kazhdan, non-amenable base with a persistent class, where neither Popa's theorem nor treeability decides it.
  sl2-half-central-extension-not-residually-amenable: that records non-residual-finiteness of the extension; this asks whether the extension admits a weakly Bernoulli liftable action.
  weakly-bernoulli-lifts-over-amenable-free-product-bases: that settles the positive polarity when the persistent class is carried by an amenable free factor; this is the first test base where it is not.
---

**OPEN.** Let `p` be prime and `Q = SL_2(Z[1/p])`, a lattice in `SL_2(R) × SL_2(Q_p)`. Let `Γ~` be its preimage in
`SL_2(R)~ × SL_2(Q_p)`, a central extension of `Q` by `Z`, and put `W_m = Γ~/mZ`. The claim: for every `m >= 1`, some free
p.m.p. `Q`-action that is the `Z/m`-quotient of a free `W_m`-action is weakly contained in `[0,1]^Q`. By
`weakly-bernoulli-lift-iff-bernoulli-almost-lifts`, this is the same as almost-lifts of the index cocycle on the
Bernoulli shift.

- **Divisors.** If the claim holds for `m'`, it holds for every divisor `m` of `m'`. Quotient a lift `X` by the central
  subgroup `mZ/m'Z`; the result is a free `W_m`-action with the same `Z/m`-quotient.
- **Where the content is.** Some `W_m` are not residually finite (`sl2-half-central-extension-not-residually-amenable`,
  after Deligne and Raghunathan). Those are the cases with content.

**Why it matters.**
- `Q` is non-amenable, has no property (T), and carries a persistent class.
- **Positive answer.**
  - A persistent class over a non-rigid base would not obstruct weakly Bernoulli lifts, even when no amenable factor
    carries the class.
  - `sl2-z-1-p-cover-quotients-sofic-from-weak-lifts` would make every `W_m` sofic
    (`sl2-z-1-p-universal-cover-quotients-are-sofic`). Then `SL_2(Z[1/p])` would not be Hilbert--Schmidt stable, and
    the Dogon--Vigdorovich route through `iwahori-local-global-defect-question` would close.
  - So a positive answer is at least as hard as soficity of these extensions.
- **Negative answer.**
  - It would be the first obstruction to weakly Bernoulli lifts over a non-Kazhdan base. The virtual-splitting claim
    would then be about persistent classes, not about w-rigid bases.
  - A non-hyperlinear `W_m` gives a negative answer. One would follow from Hilbert--Schmidt stability of `Q`, by
    Dogon--Vigdorovich.

## Attempts

- **Vertex lifts exist (ex2-rokhlin-liftable-positive, 2026-09-13).** `SL_2(Z) = Z/4 *_(Z/2) Z/6`, and every free
  action of it lifts across every finite extension.
  - A lift on the `Z/2`-subgroupoid extends to `Z/6`. Choose a transversal `T` for the `Z/6`-orbits and put frames
    `F(c^j t) = σ(c^j)` and `F(h c^j t) = ψ(h, c^j t) σ(c^j)`, where `h` generates `Z/2`, `c` has order three, and `ψ`
    is the given lift. Then `φ(g, x) = F(g x) F(x)^-1` is a lift extending `ψ`.
  - By Serre's tree, `Q = SL_2(Z) *_(Γ_0(p)) SL_2(Z)`, so lifts `φ_A` and `φ_B` exist on both vertex subgroupoids of
    any free action `Y`.
  - Their disagreement `θ = φ_A φ_B^-1` on `Γ_0(p) ⋉ Y` is an `N`-valued cocycle. `Y` lifts exactly iff
    `θ ∈ res_A Z^1(A ⋉ Y, N) + res_B Z^1(B ⋉ Y, N) + B^1`, a measured Mayer--Vietoris condition.
  - For almost-lifts, gluing as in `weakly-bernoulli-lifts-over-amenable-free-product-bases-proof` shows that
    approximating `θ` in measure on a generating set of `Γ_0(p)` suffices. The converse needs stability of
    almost-cocycles on virtually free groups and is not written.
  - **Where it dies.** Nothing known decides whether `res_A + res_B` is dense in the cocycles of `Γ_0(p)` on the
    Bernoulli shift. Popa's theorem needs relative property (T), and the treeable node needs a treeable action.
    Non-treeability of `[0,1]^Q` (`β^(2)_2(Q) != 0` with Gaboriau) is expected but not imported.
- **Homogeneous lifts are not weakly Bernoulli (sketch).** Let `G = SL_2(R) × SL_2(Q_p)`, `G~` the cover through
  `SL_2(R)~`, and `Δ̄ = Λ_1 × Λ_2` with free lattices `Λ_i`. The preimage of `Δ̄` splits, so `Q ↷ G/Δ̄` lifts exactly
  (to `(G~/mZ)/Δ`). It is not weakly contained in Bernoulli.
  - Its Koopman representation contains `ρ = L^2_0(SL_2(R)/Λ_1) ⊗ 1`.
  - If `ρ|_Q ≺ λ_Q`, then `ρ ⊗ L^2(G/Q) = Ind_Q^G ρ|_Q ≺ λ_G`, so `ρ ≺ λ_G`. Then the trivial representation of
    `SL_2(Q_p)` would be weakly contained in its regular representation, which is false.
  - For irreducible `Δ̄` (S-arithmetic) the Deligne--Raghunathan mechanism is expected to make the preimage
    non-split. This is not checked.
