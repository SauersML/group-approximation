import GroupApproximation.Sofic.ProjectionCompressionCollapse
import GroupApproximation.Sofic.CollapseUniverseScope

/-!
# `thm:collapse`, derived as the manuscript derives it

Proof-ledger row `CO.04`.  Its sentence is the proof paragraph of
`thm:collapse`:

> `p = ½(1 − Θ(k))` is a projection by (W1), commutes with the compressed copy
> by (W2), and its `Θ(L)`-conjugates commute by (W3), so projection collapse
> applies and `u = 1 − 2p` commutes with `Θ(L)`; kernels are normal, so `Θ` is
> trivial on `D_coll(L,s)`.

The row's note records the defect this file removes: "the statement is
formalized; the printed derivation is now a corollary of projection collapse,
while Lean proves it directly by the finite-stage route".  The direct route is
`InvolutionCollapseEndpoint.actualCoronaMFInvisible_of_involutiveWitness`,
which runs `actualCoronaMFInvisible_commutator` without ever forming the
projection `p`.  This file performs the printed derivation instead, clause for
clause:

* **(W1) makes `p` a projection.**  `u = Θ(k)` is a self-adjoint unitary
  because `k² = 1`, and `p = 2⁻¹ • (1 − u)` satisfies `star p = p` and
  `p * p = p` — the two computations the printed sentence attributes to (W1).
* **(W2) makes `p` commute with the compressed copy.**  `s γ s⁻¹` commutes
  with `k` in the group, so its image commutes with `u`, hence with `p`.
* **(W3) makes the `Θ(L)`-conjugates commute.**  The displayed identity
  `Θ(γ) p Θ(γ)* = ½(1 − Θ(γ k γ⁻¹))` is proved as `conj_smul_one_sub`, and
  pairwise commutation of the conjugated involutions transfers to the
  displayed projections.
* **Projection collapse applies.**  The three facts are exactly the
  hypotheses of `ProjectionCompressionCollapse.corona_projection_collapse`,
  the formalized `thm:projection-collapse`, whose conclusion is that `p`
  commutes with the full image of `L`.
* **Hence `u = 1 − 2p` commutes with `Θ(L)`,** so `Θ(⁅γ, k⁆) = 1`; ranging
  over all coronas gives `ActualCoronaMFInvisible ⁅γ, k⁆`, and "kernels are
  normal" is the passage from the marked commutators to their normal closure,
  `involutiveCollapseDefect_le_actualCoronaMFResidual_printed`.

`manuscriptInvolutiveCollapse_printed` restates
`ManuscriptExactWrappers.manuscriptInvolutiveCollapse` character for
character, proved through this route.  The finite-stage chain is untouched
and still proves the same statements; as with the transport and the
central-sign criterion, a consumer picks its route by picking a name.

The derivation is not circular: `corona_projection_collapse` is a proved
theorem of the tree, and this file consumes only its *statement*.  The printed
logical order — `thm:projection-collapse` first, `thm:collapse` as its
corollary — is thereby a real derivation in Lean, which is what the row's
proof column asks for.
-/

namespace GroupApproximation
namespace CollapsePrintedCorollary

open scoped commutatorElement

universe u

noncomputable section

variable {E : Type u} [Group E] [Countable E]

/-!
The scalar bookkeeping of the printed derivation is done once, in this
section, over an arbitrary complex algebra.  The corona's instances are
registered on an opaque definition, so `rw` with `Module`-projected lemmas
(`smul_smul`, `two_smul`) fails to match there syntactically; in a generic
algebra the projections are the canonical ones and the rewrites go through,
and applying the finished lemmas at the corona is a definitional-unfolding
`exact`, which does succeed. -/

section ScalarHelpers

variable {A : Type*} [Ring A] [Module ℂ A]
  [SMulCommClass ℂ A A] [IsScalarTower ℂ A A]

/-- Two affine images `c • (1 − a)` and `c • (1 − b)` commute as soon as `a`
and `b` do.  The scalar bookkeeping behind clause (W3) of the printed
derivation. -/
private theorem smul_one_sub_mul_comm
    (c : ℂ) {a b : A} (hab : a * b = b * a) :
    (c • (1 - a)) * (c • (1 - b)) = (c • (1 - b)) * (c • (1 - a)) := by
  rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, mul_smul_comm]
  congr 2
  have h₁ : (1 - a) * (1 - b) = 1 - a - b + a * b := by noncomm_ring
  have h₂ : (1 - b) * (1 - a) = 1 - b - a + b * a := by noncomm_ring
  rw [h₁, h₂, hab]
  abel

/-- `p = ½(1 − u)` is idempotent for an involution `u`: the (W1) computation. -/
private theorem half_one_sub_idempotent {u : A} (huu : u * u = 1) :
    ((2 : ℂ)⁻¹ • (1 - u)) * ((2 : ℂ)⁻¹ • (1 - u)) = (2 : ℂ)⁻¹ • (1 - u) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hexp : (1 - u) * (1 - u) = 1 - u - u + u * u := by noncomm_ring
  rw [hexp, huu]
  have h2 : (1 : A) - u - u + 1 = (2 : ℂ) • (1 - u) := by
    rw [two_smul ℂ]
    abel
  rw [h2, smul_smul]
  have hc : (2 : ℂ)⁻¹ * (2 : ℂ)⁻¹ * 2 = (2 : ℂ)⁻¹ := by norm_num
  rw [hc]

/-- The displayed conjugation identity, generically: conjugating
`½(1 − u)` by a unitary pair carrying `u` to `m` gives `½(1 − m)`. -/
private theorem conj_half_one_sub {v w u m : A}
    (hvw : v * w = 1) (hm : v * u * w = m) :
    v * ((2 : ℂ)⁻¹ • (1 - u)) * w = (2 : ℂ)⁻¹ • (1 - m) := by
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [mul_sub, mul_one, sub_mul, hvw, hm]

/-- Commuting with `½(1 − u)` is commuting with `1 − u`. -/
private theorem mul_one_sub_comm_of_half {v u : A}
    (h : v * ((2 : ℂ)⁻¹ • (1 - u)) = ((2 : ℂ)⁻¹ • (1 - u)) * v) :
    v * (1 - u) = (1 - u) * v := by
  have h1 : (2 : ℂ)⁻¹ • (v * (1 - u)) = (2 : ℂ)⁻¹ • ((1 - u) * v) := by
    rw [← mul_smul_comm, ← smul_mul_assoc]
    exact h
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  calc v * (1 - u) = (2 : ℂ) • (2 : ℂ)⁻¹ • (v * (1 - u)) :=
        (smul_inv_smul₀ h2 _).symm
    _ = (2 : ℂ) • (2 : ℂ)⁻¹ • ((1 - u) * v) := by rw [h1]
    _ = (1 - u) * v := smul_inv_smul₀ h2 _

end ScalarHelpers

/-- **The printed proof of `thm:collapse`, one corona representation at a
time.**  Given the involutive witness data, every norm-matrix C\*-corona
representation kills every collapse commutator — proved by forming
`p = 2⁻¹ • (1 − Θ(k))`, checking the three witness clauses on it, and applying
the formalized `thm:projection-collapse`. -/
theorem coronaRep_commutator_eq_one_printed
    (L : Subgroup E) (hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    {k : E} (hk : CollapseUniverseScope.IsInvolutiveCompressionWitness L s k)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : E →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      ∀ γ ∈ L, rho ⁅γ, k⁆ = 1 := by
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  -- `u = Θ(k)`, as an element of the corona algebra.
  set u : NormMatrixCStarCorona (fun n ↦ X n) :=
    ((rho k : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
      NormMatrixCStarCorona (fun n ↦ X n)) with hu_def
  -- (W1): `u` is a self-adjoint unitary, because `k² = 1`.
  have hk2 : rho k * rho k = 1 := by rw [← map_mul, hk.1, map_one]
  have huu : u * u = 1 := congrArg Subtype.val hk2
  have hstar_mul : star u * u = 1 :=
    Unitary.star_mul_self_of_mem (rho k).prop
  have hustar : star u = u := by
    calc star u = star u * (u * u) := by rw [huu, mul_one]
      _ = star u * u * u := by rw [mul_assoc]
      _ = u := by rw [hstar_mul, one_mul]
  -- (W1): `p = 2⁻¹ • (1 − u)` is a projection.
  have hsa : star ((2 : ℂ)⁻¹ • (1 - u)) = (2 : ℂ)⁻¹ • (1 - u) := by
    rw [star_smul, star_sub, star_one, hustar, star_inv₀, star_ofNat]
  have hproj : ((2 : ℂ)⁻¹ • (1 - u)) * ((2 : ℂ)⁻¹ • (1 - u)) =
      (2 : ℂ)⁻¹ • (1 - u) :=
    half_one_sub_idempotent huu
  -- The displayed identity: `Θ(γ) p Θ(γ)* = ½(1 − Θ(γ k γ⁻¹))`.
  have hconj : ∀ γ' : E,
      ((rho γ' : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * ((2 : ℂ)⁻¹ • (1 - u)) *
        star ((rho γ' : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) =
      (2 : ℂ)⁻¹ • (1 -
        ((rho (γ' * k * γ'⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n))) := by
    intro γ'
    have hstarv : star ((rho γ' :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) =
        ((rho γ'⁻¹ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) := by
      rw [map_inv, ← Unitary.star_eq_inv, Unitary.coe_star]
    have hvv : ((rho γ' : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) *
        ((rho γ'⁻¹ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) = 1 := by
      have h1 : rho γ' * rho γ'⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      exact congrArg Subtype.val h1
    have hmid : ((rho γ' : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * u *
        ((rho γ'⁻¹ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) =
        ((rho (γ' * k * γ'⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) := by
      have h1 : rho γ' * rho k * rho γ'⁻¹ = rho (γ' * k * γ'⁻¹) := by
        rw [← map_mul, ← map_mul]
      exact congrArg Subtype.val h1
    rw [hstarv, mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_sub, mul_one, sub_mul, hvv, hmid]
  -- (W2): `p` commutes with the compressed copy.
  have hpcomm : ∀ γ' ∈ L,
      ((rho (s * γ' * s⁻¹) :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * ((2 : ℂ)⁻¹ • (1 - u)) =
        ((2 : ℂ)⁻¹ • (1 - u)) *
          ((rho (s * γ' * s⁻¹) :
              unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) := by
    intro γ' hγ'
    have hcomQ : ((rho (s * γ' * s⁻¹) :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) * u =
        u * ((rho (s * γ' * s⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) :=
      congrArg Subtype.val ((hk.2.1 γ' hγ').map rho).eq
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    rw [mul_sub, mul_one, sub_mul, one_mul, hcomQ]
  -- (W3): the displayed projections commute pairwise.
  have horb : ∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
      Commute
        (((rho γ₁ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) * ((2 : ℂ)⁻¹ • (1 - u)) *
          star ((rho γ₁ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)))
        (((rho γ₂ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n)) * ((2 : ℂ)⁻¹ • (1 - u)) *
          star ((rho γ₂ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
            NormMatrixCStarCorona (fun n ↦ X n))) := by
    intro γ₁ h₁ γ₂ h₂
    rw [hconj γ₁, hconj γ₂]
    have hw : ((rho (γ₁ * k * γ₁⁻¹) :
          unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) *
        ((rho (γ₂ * k * γ₂⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) =
        ((rho (γ₂ * k * γ₂⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) *
        ((rho (γ₁ * k * γ₁⁻¹) :
            unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
          NormMatrixCStarCorona (fun n ↦ X n)) :=
      congrArg Subtype.val ((hk.2.2 γ₁ h₁ γ₂ h₂).map rho).eq
    exact smul_one_sub_mul_comm (2 : ℂ)⁻¹ hw
  -- Projection collapse applies: `p` commutes with the full image of `L`.
  have hcollapse :=
    ProjectionCompressionCollapse.corona_projection_collapse L hT hcomp X hX
      rho ((2 : ℂ)⁻¹ • (1 - u)) hsa hproj hpcomm horb
  -- Hence `u = 1 − 2p` commutes with `Θ(L)`, and the commutator dies.
  intro γ hγ
  have hpγ := hcollapse γ hγ
  have h2 : ((rho γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * (1 - u) =
      (1 - u) * ((rho γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) :=
    mul_one_sub_comm_of_half hpγ
  have hvu : ((rho γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) * u =
      u * ((rho γ : unitary (NormMatrixCStarCorona (fun n ↦ X n))) :
        NormMatrixCStarCorona (fun n ↦ X n)) := by
    rw [mul_sub, sub_mul, mul_one, one_mul] at h2
    exact sub_right_inj.mp h2
  have hcommU : rho γ * rho k = rho k * rho γ := Subtype.ext hvu
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr hcommU

/-- **The element-level `thm:collapse`, by the printed route.**  Statement
identical to `CollapseUniverseScope.actualCoronaMFInvisible_of_involutiveWitness`;
the proof is the printed derivation through `thm:projection-collapse` rather
than the direct finite-stage route. -/
theorem actualCoronaMFInvisible_of_involutiveWitness_printed
    {L : Subgroup E} (hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    {k : E} (hk : CollapseUniverseScope.IsInvolutiveCompressionWitness L s k)
    {γ : E} (hγ : γ ∈ L) :
    ActualCoronaMFInvisible ⁅γ, k⁆ := by
  intro X hX
  letI : ∀ n, Nonempty (X n) := fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  exact coronaRep_commutator_eq_one_printed L hT hcomp hk X hX rho γ hγ

/-- **`thm:collapse`, by the printed route.**  "Kernels are normal, so `Θ` is
trivial on `D_coll(L,s)`": the collapse defect is the normal closure of the
marked commutators, each of which the printed derivation kills. -/
theorem involutiveCollapseDefect_le_actualCoronaMFResidual_printed
    {L : Subgroup E} (hT : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) :
    CollapseUniverseScope.involutiveCollapseDefect L s ≤
      actualCoronaMFResidual E := by
  rw [CollapseUniverseScope.involutiveCollapseDefect]
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨k, hk, γ, hγ, rfl⟩
  exact actualCoronaMFInvisible_of_involutiveWitness_printed hT hcomp hk hγ

/-- **The closed form of `thm:collapse`, by the printed route.**  Statement
identical to `ManuscriptExactWrappers.manuscriptInvolutiveCollapse`, proved as
the manuscript proves it: through `thm:projection-collapse`. -/
theorem manuscriptInvolutiveCollapse_printed :
    ∀ {H : Type u} [Group H] [Countable H]
      (L : Subgroup H), HasKazhdanPropertyT.{u, u} ↥L →
      ∀ (s : H), (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      CollapseUniverseScope.involutiveCollapseDefect L s ≤
        actualCoronaMFResidual H := by
  intro H _ _ L hT s hcomp
  exact involutiveCollapseDefect_le_actualCoronaMFResidual_printed hT hcomp

end

end CollapsePrintedCorollary
end GroupApproximation
