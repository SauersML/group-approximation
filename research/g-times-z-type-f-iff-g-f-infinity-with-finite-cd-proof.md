---
rg: 2
id: g-times-z-type-f-iff-g-f-infinity-with-finite-cd-proof
kind: route
title: "Proof that G x Z is of type F exactly when G is finitely presented of type FP"
target: g-times-z-type-f-iff-g-f-infinity-with-finite-cd
requires: []
---

Notation as in K. S. Brown, *Cohomology of Groups* (GTM 87), Chapter VIII. Standard
facts used, all textbook material (Brown VIII §§4, 6, 7; C. T. C. Wall, Finiteness
conditions for CW-complexes, Ann. of Math. 81 (1965)):

- (S1) For `n ≥ 2`, `G` is of type `F_n` iff `G` is finitely presented and of type `FP_n`.
- (S2) `G` is of type FP iff it is of type `FP_∞` and `cd G < ∞`. (If `cd G = n` and
  `F_* → Z` is a resolution by finitely generated free modules, then
  `ker(F_{n−1} → F_{n−2})` is projective because `cd G ≤ n`, and finitely generated
  as the image of `F_n`; truncate there.)
- (S3) Eilenberg trick. If a module has a finite resolution by finitely generated
  projectives `P_*` with `Σ (−1)^i [P_i] ∈ Z·[R]` in `K_0(R)`, it has a finite
  resolution by finitely generated free modules: add a complement `Q_i` of
  `P_i` to degrees `i` and `i+1`, inductively from the bottom, until only the top
  module `P'_n` is non-free; its class is then an integer multiple of `[R]`, so
  it is stably free, and adding a free module to the top two degrees finishes.
- (S4) A finitely presented group of type FL is of type F (Wall; Brown VIII §7).
- (S5) Bieri–Eckmann criterion (Brown VIII §4): `H` is of type `FP_n` iff for every
  family `(M_λ)` of `ZH`-modules the natural map
  `H_k(H; ∏ M_λ) → ∏ H_k(H; M_λ)` is bijective for `k < n` and surjective for `k = n`.

Let `Γ = G × Z`, `i : G → Γ`, `g ↦ (g, 0)`, and `r : Γ → G` the projection, so
`r ∘ i = id_G`.

**(1) ⇒ (3).** Suppose `Γ` is of type F.

*Finite presentation.* Let `Γ = ⟨X | R⟩` be finite and `e = i ∘ r`. Then
`ker r = ker e` is the normal closure `N` of `{x^{-1} e(x) : x ∈ X}`: for `g ∈ ker r`,
`g^{-1} e(g) = g^{-1}`, and the set of `g` with `g^{-1} e(g) ∈ N` is closed under
products, since `(gh)^{-1} e(gh) = h^{-1} (g^{-1} e(g)) h · h^{-1} e(h)`; conversely
`r(x^{-1} e(x)) = 1`. So `G ≅ Γ/N = ⟨X | R, x^{-1} e(x) (x ∈ X)⟩` is finitely presented.

*`FP_∞`.* For a `ZG`-module `M` write `r^*M` for `M` viewed as a `ZΓ`-module via `r`.
The maps `i_* : H_k(G; M) → H_k(Γ; r^*M)` (allowed because `i^* r^* M = M`) and
`r_* : H_k(Γ; r^*M) → H_k(G; M)` are natural in `M` and compose to
`(r ∘ i)_* = id`. Since `r^* ∏ M_λ = ∏ r^* M_λ`, naturality makes the comparison map
of (S5) for `G` at `(M_λ)` a retract, in the category of arrows, of the comparison
map for `Γ` at `(r^* M_λ)`. A retract of a bijection is a bijection and a retract of
a surjection is a surjection. `Γ` is of type `FP_∞`, so (S5) gives `G` of type
`FP_n` for every `n`.

*Finite cd and FP.* `cd G ≤ cd Γ < ∞` because `G` is a subgroup. By (S2), `G` is of
type FP.

**(3) ⇒ (1).** `Γ` is finitely presented. Let `P_* → Z` be a finite projective
resolution over `ZG`, and `Q_*` the resolution
`0 → Z[t^{±1}] --(t−1)--> Z[t^{±1}] → Z → 0` over `Z[Z] = Z[t^{±1}]`. Projective
`ZG`-modules are free abelian groups (summands of free `ZG`-modules), so by the
Künneth theorem over `Z` the complex `P_* ⊗_Z Q_*` of `ZΓ = ZG ⊗_Z Z[t^{±1}]`-modules
has homology `Z` in degree 0 and nothing else. Its terms `P_i ⊗_Z Z[t^{±1}] ≅ ZΓ ⊗_{ZG} P_i`
are finitely generated projective. Its Euler class in `K_0(ZΓ)` is
`Σ_i (−1)^i [ZΓ ⊗ P_i] − Σ_i (−1)^i [ZΓ ⊗ P_i] = 0`. By (S3) `Γ` is of type FL, and
by (S4) of type F.

**(2) ⟺ (3).** (S1) with `n = ∞` and (S2).

Unreviewed as of 2026-09-13: owed to z-verify-topology.
