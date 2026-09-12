import GroupApproximation.Sofic.OmegaKazhdanCompression

/-!
# KT.19 and KT.21 on `B_ω` and `K_ω`

Ledger rows `KT.19` and `KT.21` are the two halves of the paragraph
*The two projections agree* of the Kazhdan transport result:

> Let `V = π(s)` and `Q = V P V*`.  Since `s ι(Γ) s⁻¹ ⊆ ι(Γ)`, every vector of
> `Fix` is fixed by each `π(s ι(γ) s⁻¹)`; and `η` is fixed by all
> `π(s ι(γ) s⁻¹)` exactly when `V* η ∈ Fix`.  Hence
> `ran P = Fix ⊆ V Fix = ran Q`, so `P ≤ Q`.  The element `r = V* Q` satisfies
> `r* r = Q` and `r r* = V* Q V = P`, so `P ∼ Q`.

Both rows were recorded MISMATCH for the same reason: `KT.19` was carried by a
finite-stage rotated-corner statement rather than by a statement about vectors
of `K_ω`, and `KT.21` set `r = V* Q` in an abstract star ring and proved only
the two `σ`-identities, never `r* r = Q` and `r r* = P` on their own.

This file states both on the printed objects.

* `omegaFix` is `Fix ⊆ K_ω` itself -- the vectors of the Hilbert-space
  ultraproduct fixed by every `π(ι γ)`, as a subspace, since the printed proof
  uses it as one;
* `kt_19_omega_fix_conjugated` is the first printed sentence verbatim, and
  `kt_19_omega_mem_fix_iff` the second;
* `kt_21_omega_isometry_identities` is `r* r = Q`, `r r* = P`, `r Q = r` and
  `Q r = r` in `B_ω = OmegaAdjointCorona Y ω`.

The four identities of `KT.21` are proved once in a bare star ring
(`isometry_identities_of`) from exactly the printed inputs -- `V` unitary, `P` a
projection, and `Q P = P`, which is the printed `P ≤ Q` -- and then instantiated
at `B_ω`, where every input is a theorem of the compression bundle and none is a
hypothesis: `shift_star_mul`, `shift_mul_star`, `kt_08_isSelfAdjoint_proj`,
`kt_08_proj_mul_proj` and `kt_09_conjugate_mul_proj`.
-/

namespace GroupApproximation
namespace OmegaConjugationOperators

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection

noncomputable section

/-! ## KT.21: the partial isometry `r = V* Q`

A bare star ring suffices: no norm, no completeness and no finiteness enters
these four identities.  Finiteness is what KT.10 adds on top of them. -/

section StarRing

variable {B : Type*} [Ring B] [StarRing B]

/-- **KT.21, the four printed identities of `r = V* Q`.**

With `Q = V P V*` and `r = V* Q`, the manuscript's `r* r = Q` and `r r* = P`
hold, and so do the two absorption identities `r Q = r` and `Q r = r` consumed
by the finite-algebra comparison result.  The hypotheses are exactly the
printed ones: `V` is unitary, `P` is a projection, and `Q P = P`, which is the
printed `P ≤ Q`. -/
theorem isometry_identities_of {V P : B}
    (hVsm : star V * V = 1) (hVms : V * star V = 1)
    (hPs : star P = P) (hPp : P * P = P)
    (hQP : V * P * star V * P = P) :
    star (star V * (V * P * star V)) * (star V * (V * P * star V))
        = V * P * star V ∧
      star V * (V * P * star V) * star (star V * (V * P * star V)) = P ∧
      star V * (V * P * star V) * (V * P * star V)
        = star V * (V * P * star V) ∧
      V * P * star V * (star V * (V * P * star V))
        = star V * (V * P * star V) := by
  -- `r = V* Q = P V*`
  have hr : star V * (V * P * star V) = P * star V := by
    calc star V * (V * P * star V) = star V * V * (P * star V) := by noncomm_ring
      _ = P * star V := by rw [hVsm, one_mul]
  -- `Q* = Q`
  have hQs : star (V * P * star V) = V * P * star V := by
    rw [star_mul, star_mul, star_star, hPs]
    exact (mul_assoc V P (star V)).symm
  -- `Q Q = Q`
  have hQQ : V * P * star V * (V * P * star V) = V * P * star V := by
    calc V * P * star V * (V * P * star V)
        = V * P * (star V * V) * P * star V := by noncomm_ring
      _ = V * P * 1 * P * star V := by rw [hVsm]
      _ = V * (P * P) * star V := by noncomm_ring
      _ = V * P * star V := by rw [hPp]
  -- `r* = Q V`
  have hrs : star (star V * (V * P * star V)) = V * P * star V * V := by
    rw [star_mul, hQs, star_star]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc star (star V * (V * P * star V)) * (star V * (V * P * star V))
        = V * P * star V * V * (star V * (V * P * star V)) := by rw [hrs]
      _ = V * P * star V * (V * star V) * (V * P * star V) := by noncomm_ring
      _ = V * P * star V * 1 * (V * P * star V) := by rw [hVms]
      _ = V * P * star V * (V * P * star V) := by noncomm_ring
      _ = V * P * star V := hQQ
  · calc star V * (V * P * star V) * star (star V * (V * P * star V))
        = star V * (V * P * star V) * (V * P * star V * V) := by rw [hrs]
      _ = star V * (V * P * star V * (V * P * star V)) * V := by noncomm_ring
      _ = star V * (V * P * star V) * V := by rw [hQQ]
      _ = star V * V * P * (star V * V) := by noncomm_ring
      _ = 1 * P * 1 := by rw [hVsm]
      _ = P := by noncomm_ring
  · calc star V * (V * P * star V) * (V * P * star V)
        = star V * (V * P * star V * (V * P * star V)) := by noncomm_ring
      _ = star V * (V * P * star V) := by rw [hQQ]
  · calc V * P * star V * (star V * (V * P * star V))
        = V * P * star V * (P * star V) := by rw [hr]
      _ = V * P * star V * P * star V := by noncomm_ring
      _ = P * star V := by rw [hQP]
      _ = star V * (V * P * star V) := hr.symm

end StarRing

section Omega

variable {Γ H : Type} [Group Γ] [Group H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (ω : Ultrafilter ℕ)

/-- `π(g)` read inside `B_ω` rather than in its unitary group. -/
def omegaRep (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (g : H) :
    OmegaAdjointCorona Y ω :=
  ((D.pi g : unitary (OmegaAdjointCorona Y ω)) : OmegaAdjointCorona Y ω)

@[simp] theorem omegaRep_s
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    omegaRep Y ω D D.s = D.shift := rfl

/-- Conjugation by `V = π(s)` is the representation of conjugation in `H`. -/
theorem omegaRep_conj
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) (γ : Γ) :
    D.shift * omegaRep Y ω D (D.iota γ) * star D.shift
      = omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹) :=
  D.shift_conj_coe γ

/-! ## KT.21 on `B_ω` -/

/-- The manuscript's `Q = V P V*` in `B_ω`. -/
def omegaConjProj (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    OmegaAdjointCorona Y ω :=
  D.shift * D.proj * star D.shift

/-- The manuscript's `r = V* Q` in `B_ω`. -/
def omegaImplementer (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    OmegaAdjointCorona Y ω :=
  star D.shift * omegaConjProj Y ω D

@[simp] theorem omegaConjProj_def
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    omegaConjProj Y ω D = D.shift * D.proj * star D.shift := rfl

@[simp] theorem omegaImplementer_def
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    omegaImplementer Y ω D = star D.shift * (D.shift * D.proj * star D.shift) :=
  rfl

/-- **KT.21 on `B_ω`, as printed.**  In the norm ultraproduct itself, the
element `r = V* Q` satisfies `r* r = Q` and `r r* = P`, and is absorbed by `Q`
on both sides.

No hypothesis stands in for the printed inputs: unitarity of `V = π(s)` is
`shift_star_mul` and `shift_mul_star`, the projection properties of `P` are
`kt_08_isSelfAdjoint_proj` and `kt_08_proj_mul_proj`, and `P ≤ Q` in the form
`Q P = P` is `kt_09_conjugate_mul_proj`, which is where the one-sided
compression `s ι(Γ) s⁻¹ ⊆ ι(Γ)` is consumed. -/
theorem kt_21_omega_isometry_identities
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    star (omegaImplementer Y ω D) * omegaImplementer Y ω D
        = omegaConjProj Y ω D ∧
      omegaImplementer Y ω D * star (omegaImplementer Y ω D) = D.proj ∧
      omegaImplementer Y ω D * omegaConjProj Y ω D = omegaImplementer Y ω D ∧
      omegaConjProj Y ω D * omegaImplementer Y ω D = omegaImplementer Y ω D :=
  isometry_identities_of D.shift_star_mul D.shift_mul_star
    D.kt_08_isSelfAdjoint_proj.star_eq D.kt_08_proj_mul_proj
    D.kt_09_conjugate_mul_proj

/-! ## KT.19: `Fix` inside `K_ω`, and the conjugated fixed vectors -/

variable (w : ℕ → ℝ)

theorem omegaAct_mul (hw : ∀ n, 0 ≤ w n) (a b : OmegaAdjointCorona Y ω)
    (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (a * b) ζ
      = omegaAct Y w ω hw a (omegaAct Y w ω hw b ζ) := by
  simp only [map_mul, Module.End.mul_apply]

theorem omegaAct_one (hw : ∀ n, 0 ≤ w n) (ζ : Vec Y w ω) :
    omegaAct Y w ω hw 1 ζ = ζ := by
  simp only [map_one, Module.End.one_apply]

/-- **`Fix ⊆ K_ω`**, the subspace of vectors of the Hilbert-space ultraproduct
fixed by every `π(ι γ)`.

The printed proof treats `Fix` as a subspace -- "both `Fix` and its
orthocomplement are invariant under each unitary `π(ι s')`" -- so it is built as
one here; the module structure costs nothing, each `π(ι γ)` acting by a linear
endomorphism of `K_ω`. -/
def omegaFix (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω)) :
    Submodule ℂ (Vec Y w ω) where
  carrier := {ζ | ∀ γ : Γ, omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ)) ζ = ζ}
  zero_mem' := by
    intro γ
    exact map_zero _
  add_mem' := by
    intro x y hx hy γ
    rw [map_add, hx γ, hy γ]
  smul_mem' := by
    intro c x hx γ
    rw [map_smul, hx γ]

theorem mem_omegaFix_iff (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    (ζ : Vec Y w ω) :
    ζ ∈ omegaFix Y ω w hw D ↔
      ∀ γ : Γ, omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ)) ζ = ζ :=
  Iff.rfl

/-- **KT.19, as printed.**  Since `s ι(Γ) s⁻¹ ⊆ ι(Γ)`, every vector of `Fix` is
fixed by each `π(s ι(γ) s⁻¹)`.

This is a statement about the vectors of `K_ω` under the action of `B_ω`, not a
finite-stage rotated-corner estimate, and it consumes the compression hypothesis
`compresses` of the bundle and nothing else. -/
theorem kt_19_omega_fix_conjugated (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    {ζ : Vec Y w ω} (hζ : ζ ∈ omegaFix Y ω w hw D) (γ : Γ) :
    omegaAct Y w ω hw (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) ζ = ζ := by
  obtain ⟨δ, hδ⟩ := D.compresses γ
  rw [hδ]
  exact (mem_omegaFix_iff Y ω w hw D ζ).1 hζ δ

/-- **KT.19, the printed converse.**  A vector `η` is fixed by all
`π(s ι(γ) s⁻¹)` exactly when `V* η ∈ Fix`.

Together with `kt_19_omega_fix_conjugated` this is the printed chain
`ran P = Fix ⊆ V Fix = ran Q`: the first sentence sends `Fix` into the
`π(s ι(·) s⁻¹)`-fixed vectors, and this equivalence identifies the latter with
`V Fix`. -/
theorem kt_19_omega_mem_fix_iff (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    (η : Vec Y w ω) :
    (∀ γ : Γ, omegaAct Y w ω hw
        (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) η = η) ↔
      omegaAct Y w ω hw (star D.shift) η ∈ omegaFix Y ω w hw D := by
  constructor
  · intro h
    refine (mem_omegaFix_iff Y ω w hw D _).2 fun γ ↦ ?_
    have halg : omegaRep Y ω D (D.iota γ) * star D.shift
        = star D.shift
            * (D.shift * omegaRep Y ω D (D.iota γ) * star D.shift) := by
      calc omegaRep Y ω D (D.iota γ) * star D.shift
          = star D.shift * D.shift
              * (omegaRep Y ω D (D.iota γ) * star D.shift) := by
            rw [D.shift_star_mul, one_mul]
        _ = star D.shift
              * (D.shift * omegaRep Y ω D (D.iota γ) * star D.shift) := by
            noncomm_ring
    calc omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ))
            (omegaAct Y w ω hw (star D.shift) η)
        = omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ) * star D.shift) η := by
          rw [omegaAct_mul]
      _ = omegaAct Y w ω hw (star D.shift)
            (omegaAct Y w ω hw (D.shift * omegaRep Y ω D (D.iota γ)
              * star D.shift) η) := by
          rw [halg, omegaAct_mul]
      _ = omegaAct Y w ω hw (star D.shift) η := by
          rw [omegaRep_conj, h γ]
  · intro h γ
    have hγ := (mem_omegaFix_iff Y ω w hw D _).1 h γ
    calc omegaAct Y w ω hw (omegaRep Y ω D (D.s * D.iota γ * D.s⁻¹)) η
        = omegaAct Y w ω hw
            (D.shift * omegaRep Y ω D (D.iota γ) * star D.shift) η := by
          rw [omegaRep_conj]
      _ = omegaAct Y w ω hw D.shift
            (omegaAct Y w ω hw (omegaRep Y ω D (D.iota γ))
              (omegaAct Y w ω hw (star D.shift) η)) := by
          rw [omegaAct_mul, omegaAct_mul]
      _ = omegaAct Y w ω hw D.shift (omegaAct Y w ω hw (star D.shift) η) := by
          rw [hγ]
      _ = omegaAct Y w ω hw (D.shift * star D.shift) η := by rw [omegaAct_mul]
      _ = η := by rw [D.shift_mul_star, omegaAct_one]

end Omega

end

end OmegaConjugationOperators
end GroupApproximation
