---
rg: 2
id: kt-actor-model-with-totally-non-roundable-vertex
kind: claim
title: Some trace-preserving model of the Kun--Thom actor is at intertwining distance at least kappa from every genuine model on the polynomial vertex
refuted_by:
  - theorem-e-vertex-rounds-at-every-actor-model
distinct_from:
  hs-stable-vertex-rounding-for-every-model: that is (H1) at every actor model, the rounding side of (FT); this is one actor model at which no nonzero invariant corner of the vertex rounds, the no-rounding side.
  el-r-polynomial-vertex-not-flexibly-hs-stable: that asks for a non-roundable vertex model with no extension required; this requires a trace-preserving model of the whole actor, where retract and scalar witnesses are void.
  kt-canonical-hs-normalization-fails: that is a non-normalizing Connes-embeddable actor model, equivalent to a hyperlinear intermediate wreath; this asks only for total non-roundability, which a normalizing model may also have.
  kazhdan-cover-models-round-iff-kernel-fixed-mass-one: that decides rounding of vertex models pulled back from a Kazhdan cover of the vertex; this is the actor-extendable existence question, where the cover must cover the actor.
---

**OPEN.** Setting of `compressor-extension-makes-roundable-vertex-part-invariant`:
`Γ = EL_r(F_q[x_1..x_d]) < G = EL_r(F_q[x^(±1)]) ⋊ SL_d(Z)`, `r, d >= 3`, `(F_Γ, κ)` a Kazhdan pair of `Γ`,
`M = prod_U M_n`, and `d(σ)` the intertwining defect of `σ|Γ` against genuine-coordinate models.

**Claim.** For some prime power `q` and some `r, d >= 3` with `gcd(r, q-1) = 1`, there is a trace-preserving
`σ : G -> U(M)` with `d(σ) >= κ`. Equivalently, no nonzero projection of `R = σ(Γ)' ∩ M` is roundable.

With `gcd(r, q-1) = 1` this is exactly the negation of (H1) at the Theorem E pair, and of the finitary
inequality (FT) at `κ/4` (Corollary D and §6 of that node's artifact). Any model at which (H1) fails
contains a witness: its summand `σ_nr`.

**What a witness decides.**
- **If it normalizes `R`.** (H1) and the unit-type chain are false at that parameter, while
  `hs-uniform-compression-stability-at-the-theorem-e-pair` stays open. The win-win crux is then UCS alone.
- **If it does not normalize `R`.** `kt-canonical-hs-normalization-fails` holds, so some intermediate coset
  wreath is hyperlinear and Question 3.4 has a negative answer.
- Restrictions of wreath models are witnesses of the second kind (`kt-wreath-models-never-round-on-the-vertex`).

**Factorial dichotomy (proved here).** Let `σ` be a trace-preserving actor model with `σ(G)' ∩ M` a factor.
Then `σ|Γ` is either fully roundable or totally non-roundable.
- `p_max ∈ σ(G)' ∩ Z(R)`, by the theorem of `compressor-extension-makes-roundable-vertex-part-invariant`.
- `σ(G)' ∩ M ⊆ R`, since `Γ ⊆ G`. So `p_max` commutes with `σ(G)' ∩ M` and lies in its centre, `C`.

## Attempts

- **Wreath and intermediate wreath models.** Witnesses whenever they exist. Their existence is
  hyperlinearity of some `W_K` (`kt-hyperlinear-coset-wreath-forces-nonroundable-vertex`), the target itself.
- **Genuine-coordinate and profinite actor models.** They round exactly. Congruence projections have zero
  mass at every fixed level (`theorem-e-congruence-projections-vanish-at-regular-trace`), so a witness is far
  from genuine on the actor.
- **Retract witnesses.** Void: the torus forces an actor model killing `e_ij(x_2 R_+)` to be trivial on `Γ`
  (`el-r-polynomial-vertex-not-flexibly-hs-stable`).
- **Scalar cocycles.** Void wherever the vertex multiplier is finite
  (`finite-multiplier-projective-models-round-strictly`).
  - In the stable range `r >= d + 3`, `H_2(Γ; Z) = K_2(r, F_q[x_1..x_d]) = K_2(F_q) = 0`.
  - The imports are van der Kallen injective stability and Quillen homotopy invariance. Neither is
    source-verified here.
  - So there is no rational class on the vertex, whatever `H^2` of the actor carries.
- **Følner layering along one compressor.** It gives an exact origin-type vertex at the Theorem E pair
  (`one-compressor-actor-models-with-exact-origin-vertex`). A layered witness needs a non-genuine layer,
  and at a Kazhdan actor there are no Følner layers along `SL_d(Z)`.
  - **Calibration (lane `ex2-ft-actor-models`).** At the one-compressor affine symplectic pair, layered
    Schrödinger--Weil models are totally non-roundable and do normalize the commutant
    (`layered-weil-actor-models-non-roundable-and-normalizing`).
    - So witnesses of the first, normalizing kind exist at some infranormal pair with a residually finite
      Kazhdan vertex.
    - They spend a rational vertex class and Følner layers along a `Z` quotient. The Theorem E pair has
      neither.
- **Kazhdan covers of the actor (lane `ex2-ft-actor-models`, 2026-09-13).** The criterion needs no trace
  hypothesis.
  - **Setting.** `q : G~ -> G` is finitely generated with kernel `N` and section `s`. `Γ^ ≤ G~` is a finitely
    generated Kazhdan subgroup with `q(Γ^) = Γ`, and `N_Γ = N ∩ Γ^`. The `ρ_k` are finite-dimensional unitary
    representations of `G~` with `||ρ_k(m) - 1||_2 -> 0` for every `m ∈ N`.
  - **The model.** Let `λ_k` be regular representations of finite quotients of `G` with injectivity radius
    tending to infinity. Then `σ = ((ρ_k∘s) ⊗ λ_k)_U` is a trace-preserving actor model: `|tr ρ_k| <= 1` and
    `tr λ_k -> δ_e`.
  - **Criterion.** `σ|Γ` rounds iff `tr E_k -> 1`, where `E_k` projects onto `Fix_(N_Γ)(ρ_k)`.
    - `N_Γ` acts trivially on `λ_k∘q`, so `Fix_(N_Γ)(ρ_k ⊗ λ_k∘q) = Fix_(N_Γ)(ρ_k) ⊗ ℓ²(Q_k)`.
    - The proof of `kazhdan-cover-models-round-iff-kernel-fixed-mass-one` then runs at `Γ^`: two genuine
      `Γ^`-representations close on generators share a corner, and the corner is `N_Γ`-fixed.
  - **Finite `N_Γ` dies.** `tr E_k = |N_Γ|^(-1) Σ_(m ∈ N_Γ) tr ρ_k(m) -> 1`.
  - **Central `N_Γ` dies when `H_2(Γ; Q) = 0` and `N_Γ` is finitely generated.**
    - For a central extension the exact sequence `H_2(Γ; Q) -> N_Γ ⊗ Q -> H_1(Γ^; Q)` makes
      `N_Γ ⊗ Q` inject into `H_1(Γ^; Q)`.
    - A Kazhdan `Γ^` has `H_1(Γ^; Q) = 0`. So `N_Γ` is a finitely generated torsion group, hence finite.
  - **Truncated covers die once `G` is finitely presented.**
    - For `r >= d + 3`, `St_r(F_q[Z^d])` is finitely presented (`steinberg-finite-presentation-and-kazhdan-theorem`).
    - `K_2(r, F_q[Z^d]) = K_2(F_q[Z^d])` is finitely generated (same unverified imports).
    - So `G` is finitely presented, and every truncated cover equals `G` from some stage on.
  - **A producer that needs no finite quotients** (`hyperlinear-truncated-actor-covers-refute-vertex-rounding`).
    - Suppose infinitely many truncated presentations `G_L` are hyperlinear with infinite vertex kernel. Then a
      witness exists.
    - Under (H1), those `G_L` would be finitely presented non-hyperlinear groups.
    - At rank 3, torus degree shifting reduces the question (sketch) to finite generation of `K_2(3, F_q[Z^d])`
      as an `SL_d(Z)`-module.
  - **What survives.** A Kazhdan cover whose vertex kernel is infinite, non-central, finitely normally
    generated and without relative property (T) in `Γ^`. It must also carry representations almost trivial
    on `N` with fixed mass bounded away from 1. No such cover of any higher-rank Kazhdan group is known.
  - **Scope.** The rank-3 parameters, including the Lean parameter `(2, 3, 3)`, are outside the stable range.
    There `Γ` is not finitely presented (retract onto `SL_3(F_q[t])`), and finite presentability of `G` is
    not decided.
- **Sofic actor models.** They normalize `R` (Kun--Thom 4.1). Whether their vertex restrictions round in HS is
  not known. A sofic witness would be of the first kind above.
