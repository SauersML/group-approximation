import GroupApproximation.Sofic.OmegaKazhdanCompression

/-!
# `Fix ⊆ ran P` for the action of `B_ω` on `K_ω`

`Sofic/OmegaKazhdanCompression.lean` says of itself:

> This is not yet a re-proof of `thm:kazhdan-transport` along the printed route:
> that also needs the action of `B_ω` on `K_ω` to read `Fix ⊆ ran P` back off
> the spectral gap, which the development still does through the algebraic
> absorption identities on the cofinite corona.  KT.00 stays open, and this file
> does not claim otherwise.

`Sofic/UltraproductKazhdanProjection.lean` already proves that inclusion, as
`KazhdanCompressionRep.kt_08_act_proj_of_fixed`, for an *arbitrary* action of the
ambient algebra on an abelian group -- parametrised unbundled precisely so that
"a caller with a concrete action on the Hilbert ultraproduct can use it".  Six
hypotheses stand between it and the concrete action `omegaAct`, and five are
immediate from `omegaAct` being a ring homomorphism into `Module.End`.

The sixth is not: **`ℂ`-linearity in the algebra argument**.  That is the field
`UltraproductModelConstruction.act_smul` calls "not cosmetic: `ℂ`-linearity in
the algebra argument is exactly what turns the Kazhdan spectral gap into the
statement `Fix ⊆ ran P`", through the resolvent factorisation
`1 - P = cfc (gapResolvent c) h · (1 - h)`.  `actQ_smul` has it on
representatives; what was missing is that scalars pass through the *`ω`*-corona
quotient map, so that the descended action inherits it.

This file supplies that bridge and the resulting inclusion:

* `omegaMk_smul` -- scalars pass through `[·]_ω`;
* `omegaAct_smul` -- hence `omegaAct` is `ℂ`-linear in the algebra argument;
* `omegaAct_proj_of_fixed` -- **`Fix ⊆ ran P`** on the printed objects: a vector
  of `K_ω` fixed by every `π(ι γ)` is fixed by the Kazhdan projection.

With `kt_08_rep_mul_proj`, which is the reverse inclusion `ran P ⊆ Fix`, this is
the printed "the spectral projection `P` of `h` at the isolated point `1` belongs
to `B_ω` … and projects onto `Fix`", on `B_ω` and `K_ω` themselves.
-/

namespace GroupApproximation
namespace OmegaActionLinear

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open UltraproductKazhdanProjection
-- `BoundedMatrixSequence` is `lp` over the matrix algebras, so its ring and
-- module structure are synthesized only with the matrix norm in scope.  Every
-- file that manipulates bounded sequences directly carries this open; the
-- corona-level files do not need it, which is why the omission survived here.
open scoped Matrix.Norms.L2Operator

noncomputable section

section Scalars

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (w : ℕ → ℝ)
  (ω : Ultrafilter ℕ)

/-- **Scalars pass through `[·]_ω`.**  The `ω`-corona is an ideal quotient of a
complex algebra, and its algebra map is the quotient map composed with the
algebra map upstairs; this is the `ω`-analogue of `coronaMk_smul`.

`RingHom.map_mul` is spelled out rather than `map_mul`: with the homomorphism
left to a metavariable, resolving `MulHomClass` for the quotient map runs past
the default `synthInstance` budget, because `BoundedMatrixSequence` is an `lp`
bundle over the matrix algebras and its instance tower is deep. -/
theorem omegaMk_smul (c : ℂ) (a : BoundedMatrixSequence (DblIdx Y)) :
    omegaMk Y ω (c • a) = c • omegaMk Y ω a := by
  have hmk : ∀ b : BoundedMatrixSequence (DblIdx Y),
      omegaMk Y ω b
        = Ideal.Quotient.mk
            (nullMatrixSequenceIdeal (DblIdx Y) (ω : Filter ℕ)) b :=
    fun _ ↦ rfl
  -- Name the ring hom `map_mul` is about: left to a metavariable, the
  -- `MulHomClass` search for the quotient map runs past its heartbeat budget.
  rw [hmk, hmk, Algebra.smul_def, Algebra.smul_def,
    RingHom.map_mul (Ideal.Quotient.mk (nullMatrixSequenceIdeal (DblIdx Y) (ω : Filter ℕ))),
    Ideal.Quotient.mk_algebraMap ℂ
      (nullMatrixSequenceIdeal (DblIdx Y) (ω : Filter ℕ)) c]
  -- All that is left is `OmegaAdjointCorona Y ω` versus the quotient it is
  -- defined to be, on the algebra map's target.
  rfl

/-- **`omegaAct` is `ℂ`-linear in the algebra argument.**  This is the field
`Fix ⊆ ran P` consumes, through the resolvent factorisation of `1 - P`. -/
theorem omegaAct_smul (hw : ∀ n, 0 ≤ w n) (c : ℂ)
    (x : OmegaAdjointCorona Y ω) :
    omegaAct Y w ω hw (c • x) = c • omegaAct Y w ω hw x := by
  obtain ⟨a, rfl⟩ := omegaMk_surjective Y ω x
  rw [← omegaMk_smul, omegaAct_omegaMk, omegaAct_omegaMk, actQ_smul]

/-! ## The six action laws, on the nose -/

theorem omegaAct_mul (hw : ∀ n, 0 ≤ w n) (a b : OmegaAdjointCorona Y ω)
    (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (a * b) ζ
      = omegaAct Y w ω hw a (omegaAct Y w ω hw b ζ) := by
  simp only [map_mul, Module.End.mul_apply]

theorem omegaAct_one (hw : ∀ n, 0 ≤ w n) (ζ : Vec Y w ω) :
    omegaAct Y w ω hw 1 ζ = ζ := by
  simp only [map_one, Module.End.one_apply]

theorem omegaAct_sub (hw : ∀ n, 0 ≤ w n) (a b : OmegaAdjointCorona Y ω)
    (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (a - b) ζ
      = omegaAct Y w ω hw a ζ - omegaAct Y w ω hw b ζ := by
  simp only [map_sub, LinearMap.sub_apply]

theorem omegaAct_zero (hw : ∀ n, 0 ≤ w n) (a : OmegaAdjointCorona Y ω) :
    omegaAct Y w ω hw a (0 : Vec Y w ω) = 0 :=
  map_zero _

theorem omegaAct_smul_apply (hw : ∀ n, 0 ≤ w n) (c : ℂ)
    (a : OmegaAdjointCorona Y ω) (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (c • a) ζ = c • omegaAct Y w ω hw a ζ := by
  rw [omegaAct_smul]
  simp only [LinearMap.smul_apply]

theorem omegaAct_sum (hw : ∀ n, 0 ≤ w n) {ι : Type*} (t : Finset ι)
    (f : ι → OmegaAdjointCorona Y ω) (ζ : Vec Y w ω) :
    omegaAct Y w ω hw (∑ i ∈ t, f i) ζ
      = ∑ i ∈ t, omegaAct Y w ω hw (f i) ζ := by
  rw [map_sum]
  simp only [LinearMap.sum_apply]

end Scalars

/-! ## `Fix ⊆ ran P` on `B_ω` and `K_ω` -/

section Fix

variable {Γ H : Type} [Group Γ] [Group H]
variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)] (w : ℕ → ℝ)
  (ω : Ultrafilter ℕ)

/-- **`Fix ⊆ ran P`, on the printed objects.**  A vector of `K_ω` fixed by every
`π(ι γ)` is fixed by the Kazhdan projection `P`.

This is `kt_08_act_proj_of_fixed` at the concrete action of `B_ω` on `K_ω`; the
spectral gap enters through the resolvent factorisation
`1 - P = cfc (gapResolvent rate) h · (1 - h)` inside that theorem, and
`omegaAct_smul` is what lets it be applied here at all.

Together with `kt_08_rep_mul_proj` -- `π(ι γ) P = P`, the inclusion
`ran P ⊆ Fix` -- this is the printed "`P` … projects onto `Fix`". -/
theorem omegaAct_proj_of_fixed (hw : ∀ n, 0 ≤ w n)
    (D : KazhdanCompressionRep Γ H (OmegaAdjointCorona Y ω))
    {ζ : Vec Y w ω}
    (hζ : ∀ γ : Γ, omegaAct Y w ω hw
        ((D.pi (D.iota γ) : unitary (OmegaAdjointCorona Y ω)) :
          OmegaAdjointCorona Y ω) ζ = ζ) :
    omegaAct Y w ω hw D.proj ζ = ζ :=
  D.kt_08_act_proj_of_fixed (fun a ξ ↦ omegaAct Y w ω hw a ξ)
    (fun a b ξ ↦ omegaAct_mul Y w ω hw a b ξ)
    (fun ξ ↦ omegaAct_one Y w ω hw ξ)
    (fun a b ξ ↦ omegaAct_sub Y w ω hw a b ξ)
    (fun a ↦ omegaAct_zero Y w ω hw a)
    (fun c a ξ ↦ omegaAct_smul_apply Y w ω hw c a ξ)
    (fun t f ξ ↦ omegaAct_sum Y w ω hw t f ξ)
    hζ

end Fix

end

end OmegaActionLinear
end GroupApproximation
