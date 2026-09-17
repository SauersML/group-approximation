---
rg: 2
id: full-group-kazhdan-pairs-have-invariant-fixed-algebras-proof
kind: route
title: Round the full group into permutations, amplify by tensor powers, and put swap permutations of invariant sets into the Kun-Thom centralizer
target: full-group-kazhdan-pairs-have-invariant-fixed-algebras
requires:
  - kun-thom-sofic-centralizer-normalization
artifacts:
  - research/artifacts/kun-thom-2608-06222-verified.md
---

**Conventions.**

* `𝒮_𝒰 = ∏_{n→𝒰} Sym(V_n)` carries the normalized Hamming metric `d`. For permutation matrices,
  `‖P − Q‖_2² = 2 d(P, Q)`, where `‖x‖_2 = tr(x*x)^{1/2}`.
* A *sofic representation* is a homomorphism `σ : H → 𝒮_𝒰` with `d(σ(h), 1) = 1` for `h ≠ 1`, as in
  Kun--Thom. Their Theorem 4.1 (verbatim in the artifact) is used for a free ultrafilter on a countable
  index set, which is harmless.
* `H ≤ [R]` acts on sets by `hE = h(E)`, so `1_{hE} = 1_E ∘ h⁻¹`.

## Step 1. The full group rounds to permutations

Let `Θ : L^∞(X) ⋊ G → M = ∏_{n→𝒰} M_{|V_n|}(ℂ)` be Păunescu's embedding, with `ι = Θ|_{L^∞(X)}` into
`D_𝒰` and `Θ(u_g) ∈ 𝒮_𝒰`. Because `a` is free, `L^∞(X) ⋊ G = L(R)`.

Take `φ ∈ [R]` and let `X_g = {x : φx = gx}`; these sets partition `X`. In `L(R)`,
`u_φ = Σ_g u_g 1_{X_g}` converges in `‖·‖_2`.

*Claim: `Θ(u_φ) ∈ 𝒮_𝒰`.*

1. Fix `ε > 0` and a finite `F ⊂ G` with `μ(⋃_{g∉F} X_g) < ε`.
2. For `g ∈ F`, lift `ι(1_{X_g})` to subsets `B_{g,n} ⊆ V_n`, and lift `Θ(u_g)` to permutations `σ_n(g)`.
3. Removing overlaps costs density `o(1)` along `𝒰`, since the `X_g` are disjoint and `ι` is
   trace-preserving. So take the `B_{g,n}` disjoint.
4. The images `σ_n(g) B_{g,n}` lift `Θ(u_g) ι(1_{X_g}) Θ(u_g)* = ι(1_{gX_g}) = ι(1_{φ X_g})`. These are
   again disjoint in the limit.
5. So the partial map `v ↦ σ_n(g) v` on `B_{g,n}` is injective off a set of density `o(1)`. Its domain
   has density `≥ 1 − ε − o(1)`.
6. Extend it arbitrarily to a permutation `π_n`. Then `‖Θ(u_φ) − [π_n]‖_2 ≤ C √ε`.
7. `𝒮_𝒰` is `‖·‖_2`-closed in `U(M)`: a `‖·‖_2`-limit of elements of `𝒮_𝒰` lies in `𝒮_𝒰`, by the usual
   diagonal choice of indices. The claim follows.

So `Θ` restricts to a group homomorphism `Θ : [R] → 𝒮_𝒰` with:

* (i) `Θ(φ) ι(f) Θ(φ)* = ι(f ∘ φ⁻¹)`;
* (ii) `tr Θ(φ) = τ(u_φ) = μ(Fix φ)`, i.e. `d(Θ(φ), 1) = 1 − μ(Fix φ)`.

## Step 2. Free amplification without leaving the model

Let `σ_n(h)` be permutations lifting `Θ(h)` for `h ∈ H`.

* Put `c_h = μ(Fix h)`. For `h ≠ 1` in `[R]`, `c_h < 1`.
* Put `ε_n(g,h) = d(σ_n(g) σ_n(h), σ_n(gh))`, which tends to `0` along `𝒰`.

On the index set `N × N`, define the free ultrafilter
`𝒲 = {S : {k : {n : (n,k) ∈ S} ∈ 𝒰} ∈ 𝒱}`, where `𝒱` is any free ultrafilter on `N`. Then
`lim_𝒲 F(n,k) = lim_{k→𝒱} lim_{n→𝒰} F(n,k)`.

Define `ρ_{n,k}(h) = σ_n(h)^{⊗(k+1)} × id` acting on `V_n^{k+1} × {0,1}`.

* The defect `d(ρ(g) ρ(h), ρ(gh))` is at most `(k+1) ε_n(g,h)`. Its `𝒰`-limit is `0` for each `k`.
* `d(ρ_{n,k}(h), 1) = 1 − (fixed fraction of σ_n(h))^{k+1}`. This tends to `1 − c_h^{k+1}` along `𝒰`,
  and then to `1` along `𝒱` when `h ≠ 1`.

So `ρ = [ρ_{n,k}] : H → 𝒮_𝒲` is a sofic representation.

## Step 3. Swap permutations of invariant sets

For a measurable `E ⊆ X`:

* lift `ι(1_E)` to `A_n(E) ⊆ V_n`;
* let `s_{n,k}(E)` swap `(v, i) ↔ (v, 1−i)` exactly when the first coordinate `v_1` lies in `A_n(E)`;
* put `s(E) = [s_{n,k}(E)]_𝒲 ∈ 𝒮_𝒲`.

Two permutations `s_{n,k}(A)` and `s_{n,k}(B)` disagree exactly where `v_1 ∈ A △ B`. So
`d(s(E), s(E')) = lim_𝒰 |A_n(E) △ A_n(E')| / |V_n| = μ(E △ E')`. Thus `s(E)` does not depend on the
lifts, and `s(E) = s(E')` iff `E = E'` a.e.

Conjugation: `ρ_{n,k}(h) s_{n,k}(A) ρ_{n,k}(h)⁻¹ = s_{n,k}(σ_n(h) A)`. By (i),
`lim_𝒰 |σ_n(h) A_n(E) △ A_n(hE)| / |V_n| = ‖Θ(h) ι(1_E) Θ(h)* − ι(1_{hE})‖_1 = 0`. Hence

`ρ(h) s(E) ρ(h)⁻¹ = s(hE)` for all `h ∈ H`. (★)

Now let `E` be `Γ`-invariant.

1. By (★), `ρ(γ) s(E) ρ(γ)⁻¹ = s(γE) = s(E)` for `γ ∈ Γ`, so `s(E) ∈ C_{𝒮_𝒲}(ρ(Γ))`.
2. Theorem 4.1 applies: `Γ ≤ H` are Kazhdan and `Γ` is infranormal in `H`. So for `h ∈ H`,
   `s(hE) = ρ(h) s(E) ρ(h)⁻¹ ∈ C(ρ(Γ))`.
3. Applying (★) again, `s(γhE) = s(hE)` for all `γ ∈ Γ`, i.e. `μ(γhE △ hE) = 0`.
4. So `hE` is `Γ`-invariant. Spectral projections of `Γ`-invariant functions are `Γ`-invariant, so
   `h · L^∞(X)^Γ ⊆ L^∞(X)^Γ`. ∎

**Trust surface.** The only external input is Kun--Thom Theorem 4.1, which is unrefereed. Păunescu's definition
is used verbatim. Steps 1--3 are internal and elementary.

## Calibration

* **C1: Kun--Thom group.** Let `b = G_KT ↷ K^{G/Γ}` be the generalized Bernoulli action, and `a = b × β` with
  `β` a Bernoulli shift of `G_KT`. Then `a` is free, `G_KT ≤ [R_a]`, and `L^∞^Γ` is not invariant. The
  statement recovers Corollary D for `a`, which is `kun-thom-free-nonsofic-action`.
* **C2: finite orbits, unconditional.** If `Γ` has finite orbits a.e., the conclusion holds with no soficity
  and no Theorem 4.1.
  1. For `h ∈ P_Γ`, `Γhx ⊇ hΓh⁻¹ hx = h(Γx)`. So `f(x) = |Γx|` satisfies `f ∘ h ≥ f`.
  2. `h` preserves `μ`, so `f ∘ h = f` a.e. The inclusion is then an equality `Γhx = hΓx`.
  3. So `h`, and hence `h⁻¹`, maps `Γ`-saturated sets to `Γ`-saturated sets. `P_Γ` generates `H`.
  4. This covers profinite and finite-orbit seeds. It is consistent with `𝒮 ⊇` amenable groups: a Kazhdan
     `H` inside a hyperfinite `R` has finite orbits on a.e. ergodic component, because ergodic actions of
     Kazhdan groups are strongly ergodic (Connes--Weiss), while ergodic hyperfinite relations with infinite
     orbits are not.
* **C3: what is new.** For a mixing `a`, every infinite Kazhdan subgroup of `G` acting through `a` is
  ergodic. So Theorem C and Theorem 4.1 are blind to `a` along subgroups:
  `kazhdan-fixed-algebra-blind-to-subgroup-ergodic-actions` and
  `permutation-centralizer-blind-to-weakly-mixing-actions`.
  Subgroups of `[R_a]` are not ergodic in general. This is the blind spot the statement addresses. Also, the swap `s(E)` lives on the doubled space, outside the embedded crossed product, so the computation `Θ(M) ∩ C(σ(Γ)) = σ(C_G(Γ))` of `permutation-centralizer-blind-to-weakly-mixing-actions` does not constrain it. By
  `howe-moore-lattice-nonsofic-action-transfers-to-mixing`, restricting `SL_3(Z)` to mixing `a` loses
  nothing.
