import GroupApproximation.Analysis.OmegaConjugationOperators
import GroupApproximation.Sofic.OmegaAlmostRepresentation

/-!
# KT.25 and KT.27: the conclusion paragraph, on `B_ω` and `K_ω`

The printed proof of the Kazhdan transport result ends:

> *Conclusion.*  Let `ξ = [x_n]_ω ∈ K_ω`; the uniform operator-norm bound makes
> this class well defined.  By unitary invariance of the normalized
> Hilbert--Schmidt norm, the commutator hypothesis says exactly that each
> `π(ι(γ))` fixes `ξ`.  Thus `ξ ∈ Fix`. … The matrix `U_n(s)x_nU_n(s)*` is the
> vector `Ad U_n(s) x_n` of `K_n`, so, again by unitary invariance,
> `‖[U_n(s)x_nU_n(s)*, U_n(ι(γ))]‖ = ‖(Ad U_n(ι(γ)) − 1) Ad U_n(s) x_n‖ → 0`
> along `ω`.

Ledger rows `KT.25` and `KT.27` carried this with finite-stage substitutes: a
spectral-capture estimate in place of exact membership in `Fix`, and a
displacement chain with explicit constants in place of the vector identity.
This file states both on the actual objects, for the actual `π(g) = [Ad U_n(g)]_ω`
of `Sofic/OmegaAlmostRepresentation.lean` acting on `K_ω` through `omegaAct`.

## The three statements

* `applyFam_adSeq` is the printed sentence "the matrix `U_n(s)x_nU_n(s)*` is the
  vector `Ad U_n(s) x_n` of `K_n`": the operator sequence representing `π(s)`,
  applied to the family of vectors `x_n`, *is* the family `U_n(s)x_nU_n(s)*`.
* `kt_25_act_fixes_iff` is the printed "exactly": `π(g)` fixes `[x_n]_ω` **iff**
  the commutator `x_nU_n(g) − U_n(g)x_n` is null at the weight along `ω`.  The
  two directions are the two uses the printed proof makes of unitary invariance
  -- KT.25 reads it left to right to put `ξ` in `Fix`, KT.27 reads it right to
  left to send the transported commutator to zero.
* `kt_27_transported_commutator_null` composes them at the transported vector,
  which is the displayed limit itself.

Unitary invariance is `matMass_adjoint_sub_eq`: `Ad U(X) − X` and `XU − UX`
differ by right multiplication by the unitary `U`, which `matMass` does not see.
Everything is at the unnormalized mass, so it holds at every weight at once,
exactly as `kt_01_matMass_adjoint` does.
-/

namespace GroupApproximation
namespace OmegaCommutatorFixes

open Filter Matrix Topology
open UltraproductModelConstruction OmegaOperatorUltraproduct
open ScaledKazhdanTransport UltraproductScaledTransport

noncomputable section

universe u

/-! ## Unitary invariance of the commutator mass -/

/-- **Unitary invariance, in the form the conclusion paragraph uses it.**  The
displacement of the adjoint action and the commutator have the same Frobenius
mass, because they differ by right multiplication by `U`:
`(UXU* − X)U = UX − XU`. -/
theorem matMass_adjoint_sub_eq {Z : Type*} [Fintype Z] [DecidableEq Z]
    {U : Matrix Z Z ℂ} (hU : U ∈ Matrix.unitaryGroup Z ℂ) (X : Matrix Z Z ℂ) :
    matMass (U * X * Uᴴ - X) = matMass (X * U - U * X) := by
  have hUU : U * Uᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hUsU : Uᴴ * U = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at h
  have hkey : (U * X * Uᴴ - X) * U = -(X * U - U * X) := by
    have h1 : U * X * Uᴴ * U = U * X := by
      rw [mul_assoc, hUsU, mul_one]
    rw [sub_mul, h1]
    abel
  calc matMass (U * X * Uᴴ - X)
      = matMass ((U * X * Uᴴ - X) * U) :=
        (matMass_mul_right_of_mul_star_self hUU _).symm
    _ = matMass (-(X * U - U * X)) := by rw [hkey]
    _ = matMass (X * U - U * X) := matMass_neg _

/-! ## The action of `π(g) = [Ad U_n(g)]_ω` on classes of `K_ω` -/

section Representation

variable {G : Type u} [Group G] (A : OpAlmostRepresentation G)

/-- **KT.27, the vector identity.**  "The matrix `U_n(s)x_nU_n(s)*` is the vector
`Ad U_n(s) x_n` of `K_n`": the operator sequence `Ad U_n(s)` representing `π(s)`
sends the family of vectors `x_n` to the family `U_n(s)x_nU_n(s)*`.

This is an identity of families, not an estimate; the whole content is that the
doubled matrix `conjDouble U` acts on row-major coordinates by conjugation. -/
theorem applyFam_adSeq (g : G) (ξ : MatFam A.model) :
    applyFam A.model (OmegaAlmostRepresentation.adSeq A g) ξ
      = fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ) * ξ n
          * (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ := by
  funext n
  show rowMat ((OmegaAlmostRepresentation.adSeq A g :
        ∀ m, Matrix (DblIdx A.model m) (DblIdx A.model m) ℂ) n
      *ᵥ rowVec (ξ n))
      = (A.map n g : Matrix (A.model n) (A.model n) ℂ) * ξ n
          * (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ
  rw [OmegaAlmostRepresentation.adSeq_apply,
    OpAlmostRepresentation.adjoint_map]
  exact rowMat_conjDouble_mulVec (A.model n) _ (ξ n)

variable (w : ℕ → ℝ) (ω : Ultrafilter ℕ)

/-- **KT.27, on classes.**  `π(g)` acts on `[ξ_n]_ω ∈ K_ω` by the ultraproduct
of the adjoint actions.

No freeness hypothesis on `ω` is needed: the action of `B_ω` on `K_ω` is defined
by factoring the coordinatewise action through the `ω`-null ideal, so the
representative `Ad U_n(g)` computes it directly.  (On the cofinite corona the
same statement needs `ω ≤ cofinite`, which is why `act_pi_cls` carries it.) -/
theorem omegaAct_piOmega_cls (hw : ∀ n, 0 ≤ w n) (g : G) (ξ : MatFam A.model) :
    omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g)
        (cls A.model w ω ξ)
      = cls A.model w ω (fun n ↦
          (A.map n g : Matrix (A.model n) (A.model n) ℂ) * ξ n
            * (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) := by
  have hmass : ∀ n, matMass ((A.map n g : Matrix (A.model n) (A.model n) ℂ)
      * ξ n * (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)
      = matMass (ξ n) :=
    fun n ↦ kt_01_matMass_adjoint (A.map n g).2 (ξ n)
  rw [OmegaAlmostRepresentation.piOmega_def, omegaAct_omegaMk]
  by_cases hb : ξ ∈ massBounded A.model w
  · obtain ⟨C, hC⟩ := hb
    have hb' : ξ ∈ massBounded A.model w := ⟨C, hC⟩
    have hcb : (fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ) * ξ n
        * (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)
          ∈ massBounded A.model w :=
      ⟨C, fun n ↦ by rw [hmass n]; exact hC n⟩
    rw [cls_of_mem A.model w ω hb', actQ_mk, cls_of_mem A.model w ω hcb]
    exact congrArg Submodule.Quotient.mk
      (Subtype.ext (applyFam_adSeq A g ξ))
  · have hcb : (fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ) * ξ n
        * (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)
          ∉ massBounded A.model w := by
      rintro ⟨C, hC⟩
      exact hb ⟨C, fun n ↦ by rw [← hmass n]; exact hC n⟩
    rw [cls_of_not_mem A.model w ω hb, cls_of_not_mem A.model w ω hcb, map_zero]

/-! ## KT.25 and KT.27: the printed "exactly" -/

/-- **KT.25 and KT.27, the printed equivalence.**  For a uniformly mass-bounded
family `x`, the class `ξ = [x_n]_ω` is fixed by `π(g)` **exactly when** the
commutator `x_nU_n(g) − U_n(g)x_n` is null at the weight along `ω`.

Read left to right this is KT.25 -- "the commutator hypothesis says exactly that
each `π(ι(γ))` fixes `ξ`, thus `ξ ∈ Fix`".  Read right to left it is the step
KT.27 consumes just before the contradiction: fixedness of the transported class
returns the vanishing of the transported commutator along `ω`.  In both
directions the bridge is unitary invariance of the normalized Hilbert--Schmidt
norm, which is `matMass_adjoint_sub_eq` at the unnormalized mass. -/
theorem kt_25_act_fixes_iff (hw : ∀ n, 0 ≤ w n) (C : ℝ) (x : MatFam A.model)
    (hx : WeightBounded A.model w C x) (g : G) :
    omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g)
          (cls A.model w ω x)
        = cls A.model w ω x ↔
      WeightNull A.model w (ω : Filter ℕ)
        (fun n ↦ x n * (A.map n g : Matrix (A.model n) (A.model n) ℂ)
          - (A.map n g : Matrix (A.model n) (A.model n) ℂ) * x n) := by
  have hmass : ∀ n, matMass ((A.map n g : Matrix (A.model n) (A.model n) ℂ)
      * x n * (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ)
      = matMass (x n) :=
    fun n ↦ kt_01_matMass_adjoint (A.map n g).2 (x n)
  have hxc : WeightBounded A.model w C
      (fun n ↦ (A.map n g : Matrix (A.model n) (A.model n) ℂ) * x n
        * (A.map n g : Matrix (A.model n) (A.model n) ℂ)ᴴ) := by
    intro n
    rw [hmass n]
    exact hx n
  rw [omegaAct_piOmega_cls, cls_eq_iff_weightNull A.model w ω hw C _ x hxc hx]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    rwa [← matMass_adjoint_sub_eq (A.map n g).2 (x n)]
  · intro h ε hε
    filter_upwards [h ε hε] with n hn
    rwa [matMass_adjoint_sub_eq (A.map n g).2 (x n)]

/-- **KT.27, as printed.**  If `π(ι(γ))` fixes the transported class
`π(s)[x_n]_ω`, then the transported commutator
`[U_n(s)x_nU_n(s)*, U_n(ι(γ))]` is null at the weight along `ω` -- the displayed
limit of the conclusion paragraph.

The proof is the printed one: the transported class is the class of the family
`U_n(s)x_nU_n(s)*` (`omegaAct_piOmega_cls`, whose content is the vector identity
`applyFam_adSeq`), that family is again uniformly mass-bounded because unitary
conjugation preserves the mass, and the equivalence above turns fixedness back
into a vanishing commutator. -/
theorem kt_27_transported_commutator_null (hw : ∀ n, 0 ≤ w n) (C : ℝ)
    (x : MatFam A.model) (hx : WeightBounded A.model w C x) (s g : G)
    (hfix : omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω g)
          (omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω s)
            (cls A.model w ω x))
        = omegaAct A.model w ω hw (OmegaAlmostRepresentation.piOmega A ω s)
            (cls A.model w ω x)) :
    WeightNull A.model w (ω : Filter ℕ)
      (fun n ↦ ((A.map n s : Matrix (A.model n) (A.model n) ℂ) * x n
            * (A.map n s : Matrix (A.model n) (A.model n) ℂ)ᴴ)
          * (A.map n g : Matrix (A.model n) (A.model n) ℂ)
        - (A.map n g : Matrix (A.model n) (A.model n) ℂ)
          * ((A.map n s : Matrix (A.model n) (A.model n) ℂ) * x n
            * (A.map n s : Matrix (A.model n) (A.model n) ℂ)ᴴ)) := by
  have hmass : ∀ n, matMass ((A.map n s : Matrix (A.model n) (A.model n) ℂ)
      * x n * (A.map n s : Matrix (A.model n) (A.model n) ℂ)ᴴ)
      = matMass (x n) :=
    fun n ↦ kt_01_matMass_adjoint (A.map n s).2 (x n)
  have hxs : WeightBounded A.model w C
      (fun n ↦ (A.map n s : Matrix (A.model n) (A.model n) ℂ) * x n
        * (A.map n s : Matrix (A.model n) (A.model n) ℂ)ᴴ) := by
    intro n
    rw [hmass n]
    exact hx n
  rw [omegaAct_piOmega_cls] at hfix
  exact (kt_25_act_fixes_iff A w ω hw C _ hxs g).1 hfix

end Representation

/-! ## KT.25 as membership in `Fix`

`Sofic/OmegaConjugationOperators.lean` builds `Fix ⊆ K_ω` for a Kazhdan
compression bundle over `B_ω`.  The printed conclusion "`ξ ∈ Fix`" is that
membership, once the bundle's representation is the one carried by the almost
representation.  That identification is `omegaCompressionRep_pi`, a `rfl`, so
the hypothesis `hD` below is a definitional link between two constructed
objects and not a mathematical assumption. -/

section Fix

open UltraproductKazhdanProjection

variable {Γ G : Type} [Group Γ] [Group G]

/-- **KT.25, as printed.**  If for every `γ ∈ Γ` the commutator
`x_nU_n(ι(γ)) − U_n(ι(γ))x_n` is null at the weight along `ω`, then the class
`ξ = [x_n]_ω` lies in `Fix`.

The uniform mass bound `hx` is the printed "the uniform operator-norm bound
makes this class well defined". -/
theorem kt_25_mem_omegaFix (A : OpAlmostRepresentation G) (w : ℕ → ℝ)
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ Filter.cofinite)
    (hw : ∀ n, 0 ≤ w n) (C : ℝ) (x : MatFam A.model)
    (hx : WeightBounded A.model w C x)
    (D : KazhdanCompressionRep Γ G (OmegaAdjointCorona A.model ω))
    (hD : D.pi = OmegaAlmostRepresentation.piHom A ω hω)
    (hcomm : ∀ γ : Γ, WeightNull A.model w (ω : Filter ℕ)
      (fun n ↦ x n
          * (A.map n (D.iota γ) : Matrix (A.model n) (A.model n) ℂ)
        - (A.map n (D.iota γ) : Matrix (A.model n) (A.model n) ℂ) * x n)) :
    cls A.model w ω x
      ∈ OmegaConjugationOperators.omegaFix A.model ω w hw D := by
  refine (OmegaConjugationOperators.mem_omegaFix_iff A.model ω w hw D _).2
    fun γ ↦ ?_
  have hrep : OmegaConjugationOperators.omegaRep A.model ω D (D.iota γ)
      = OmegaAlmostRepresentation.piOmega A ω (D.iota γ) := by
    show ((D.pi (D.iota γ) : unitary (OmegaAdjointCorona A.model ω)) :
        OmegaAdjointCorona A.model ω)
      = OmegaAlmostRepresentation.piOmega A ω (D.iota γ)
    rw [hD]
    rfl
  rw [hrep]
  exact (kt_25_act_fixes_iff A w ω hw C x hx (D.iota γ)).2 (hcomm γ)

end Fix

end

end OmegaCommutatorFixes
end GroupApproximation
