import GroupApproximation.Analysis.FilterMatrixCStarCorona
import GroupApproximation.Analysis.FaithfulTracialMatrix
import GroupApproximation.Analysis.NonUnitalMFSupportCorner
import GroupApproximation.Analysis.ReducedGroupCStarStablyFinite
import GroupApproximation.Analysis.ShulmanTraceClasses
import GroupApproximation.Analysis.TracialQuotientCStar
import GroupApproximation.Analysis.TracialUltraproductCStar

/-!
# The unconditional C-star core of the Goldbring--Hart route

Goldbring--Hart, Proposition 6.1, starts with a non-Connes-embeddable
`II₁` factor `M`.  Regarded as a unital C-star algebra, `M` has a unique
faithful trace and is stably finite.  A hypothetical unital embedding of `M`
into a norm-matrix/UHF C-star ultrapower descends through the trace ideal to a
tracial matrix ultrapower.  Uniqueness of the trace makes the descended map
faithful, contradicting the choice of `M`.

This file proves the part of that route which the repository can state with
its existing concrete operator algebras, and no literature assumptions:

* a faithful tracial state makes every finite matrix amplification finite;
* the tracial matrix quotient has its canonical faithful tracial state;
* an operator-norm-null sequence is Hilbert--Schmidt-null along every
  ultrafilter refining the cofinite filter;
* consequently the norm-matrix corona has a canonical unital star
  homomorphism to the tracial matrix quotient; and
* a unital star homomorphism from a uniquely and faithfully traced algebra to
  a faithfully traced algebra is injective.  Applied to the preceding map,
  this is the exact trace-ideal step in Goldbring--Hart.

No predicate for Connes embeddability, no substitute for the negative
solution of CEP, and no assumed Goldbring--Hart package is introduced here.

## The remaining interface mismatch

The repository's `HasMFEmbedding` permits a *nonunital* homomorphism
`A →⋆ₙₐ Q`, whereas Proposition 6.1 uses a unital C-star embedding.  The
trace-ideal argument cannot simply forget this distinction: the support
projection of a nonunital embedding can have zero normalized trace after
passing to the tracial quotient.  `NonUnitalMFSupportCorner` proves that this
support is a nonzero projection, produces a projection lift with infinitely
many nonzero coordinates, and proves that compression by the lift preserves
the represented corona elements.  What remains is the sequence-level assembly
which relabels those coordinates and identifies their finite corners with a
new full matrix corona.  Thus the theorems below intentionally take an
explicit `StarAlgHom`, not `HasMFEmbedding`.  Closing the manuscript's
historical implication against its present `IsMFAlgebra` definition still
requires that corner-corona assembly, as well as a formal source for a
non-Connes-embeddable factor and the separable elementary-substructure step.
-/

namespace GroupApproximation

noncomputable section

universe u v

/-! ## Faithful traces imply stable finiteness -/

namespace FaithfulTracialState

/-- A unital C-star algebra carrying a faithful tracial state is stably
finite.  This is the general form of the trace argument previously used only
for reduced group C-star algebras. -/
theorem isStablyFiniteCStarAlgebra {A : Type u} [CStarAlgebra A]
    (tau : FaithfulTracialState A) : IsStablyFiniteCStarAlgebra A :=
  IsStablyFiniteCStarAlgebra.of_matrix_isometry_unitary
    fun n _ _ hn _ hv => tau.matrix_mul_star_eq_one_of_star_mul_eq_one n hn hv

end FaithfulTracialState

/-! ## Unique trace makes a unital traced representation faithful -/

/-- A unital star homomorphism out of a uniquely and faithfully traced
C-star algebra into another faithfully traced C-star algebra is injective.

The target trace pulls back to a tracial state on the source.  Uniqueness
identifies that pullback with the faithful source trace, so an element in the
kernel has zero source `2`-norm and is zero. -/
theorem StarAlgHom.injective_of_faithfulTracialState_of_trace_preserving
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (tauA : FaithfulTracialState A) (tauB : FaithfulTracialState B)
    (pi : A →⋆ₐ[ℂ] B) (htrace : forall a : A, tauB (pi a) = tauA a) :
    Function.Injective pi := by
  intro a b hab
  have hdiff : pi (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  apply sub_eq_zero.mp
  apply tauA.eq_zero_of_map_star_mul_self_eq_zero
  calc
    tauA (star (a - b) * (a - b)) =
        tauB (pi (star (a - b) * (a - b))) :=
      (htrace (star (a - b) * (a - b))).symm
    _ = tauB (star (pi (a - b)) * pi (a - b)) := by
      rw [map_mul, map_star]
    _ = 0 := by rw [hdiff, star_zero, zero_mul, FaithfulTracialState.map_zero]

/-- Unique trace supplies the trace-preservation hypothesis of
`injective_of_faithfulTracialState_of_trace_preserving`. -/
theorem StarAlgHom.injective_of_unique_faithfulTracialState
    {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]
    (tauA : FaithfulTracialState A)
    (hunique : forall sigma : TracialState A, forall a : A, sigma a = tauA a)
    (tauB : FaithfulTracialState B) (pi : A →⋆ₐ[ℂ] B) :
    Function.Injective pi := by
  apply StarAlgHom.injective_of_faithfulTracialState_of_trace_preserving
    tauA tauB pi
  intro a
  exact hunique (tauB.toTracialState.compStarAlgHom pi) a

namespace TracialUltraproduct

open Filter Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-! ## The quotient map and its faithful trace -/

/-- The quotient map to the Hilbert--Schmidt-null quotient, bundled as a
complex unital star-algebra homomorphism. -/
def tracialMatrixQuotientQuotient (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (l : Filter ℕ) :
    ModelBoundedSequence X →⋆ₐ[ℂ] TracialMatrixQuotient X l where
  toFun := tracialMatrixQuotientMk X l
  map_one' := map_one (tracialMatrixQuotientMk X l)
  map_mul' := map_mul (tracialMatrixQuotientMk X l)
  map_zero' := map_zero (tracialMatrixQuotientMk X l)
  map_add' := map_add (tracialMatrixQuotientMk X l)
  commutes' z := by
    unfold tracialMatrixQuotientMk TracialMatrixQuotient
    exact Ideal.Quotient.mk_algebraMap ℂ (hilbertSchmidtNullIdeal X l) z
  map_star' a := (tracialMatrixQuotient_star_mk X l a).symm

/-- The ultratrace on the tracial matrix quotient, as a faithful tracial
state. -/
def ultratraceFaithfulTracialState (X : ℕ → FiniteModel)
    [∀ n, Nonempty (X n)] (omega : Ultrafilter ℕ) :
    FaithfulTracialState (TracialMatrixQuotient X (omega : Filter ℕ)) where
  toLinearMap := ultratraceLinearMap X omega
  map_one := ultratrace_one X omega
  map_star_mul_self_nonneg x := by
    obtain ⟨t, ht, htrace⟩ := ultratrace_star_mul_self_nonneg X omega x
    change 0 ≤ ultratrace X omega (star x * x)
    rw [htrace]
    exact RCLike.ofReal_nonneg.mpr ht
  map_mul_comm := ultratrace_mul_comm X omega
  eq_zero_of_map_star_mul_self_eq_zero := fun {x} hx =>
    (ultratrace_star_mul_self_eq_zero_iff X omega x).mp hx

/-! ## From the norm corona to the tracial quotient -/

/-- Operator-norm nullity along `cofinite` implies normalized
Hilbert--Schmidt nullity along every refining ultrafilter. -/
theorem isHilbertSchmidtNull_of_isNullMatrixSequence_cofinite
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (omega : Ultrafilter ℕ) (homega : (omega : Filter ℕ) ≤ cofinite)
    (a : ModelBoundedSequence X)
    (ha : IsNullMatrixSequence (fun n => (X n).carrier) cofinite a) :
    IsHilbertSchmidtNull X (omega : Filter ℕ) a := by
  have hop : Tendsto (fun n => ‖a n‖) (omega : Filter ℕ) (nhds 0) :=
    ha.mono_left homega
  exact squeeze_zero'
    (Eventually.of_forall fun n => Real.sqrt_nonneg (hsNormSq (X n) (a n)))
    (Eventually.of_forall fun n =>
      PrelimNotation.hsNorm_le_l2_opNorm (X n) (a n)) hop

/-- The canonical unital star homomorphism from the cofinite norm-matrix
corona to the tracial matrix quotient along a refining ultrafilter.  It is the
quotient by the trace ideal in Goldbring--Hart's proof. -/
def normMatrixCStarCoronaToTracialMatrixQuotient
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (omega : Ultrafilter ℕ) (homega : (omega : Filter ℕ) ≤ cofinite) :
    NormMatrixCStarCorona (fun n => X n) →⋆ₐ[ℂ]
      TracialMatrixQuotient X (omega : Filter ℕ) := by
  unfold NormMatrixCStarCorona
  exact filterMatrixCoronaStarLift (fun n => X n) cofinite
    (tracialMatrixQuotientQuotient X (omega : Filter ℕ))
    (fun a ha => (tracialMatrixQuotientMk_eq_zero_iff X
      (omega : Filter ℕ) a).mpr
        (isHilbertSchmidtNull_of_isNullMatrixSequence_cofinite
          X omega homega a ha))

@[simp] theorem normMatrixCStarCoronaToTracialMatrixQuotient_mk
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (omega : Ultrafilter ℕ) (homega : (omega : Filter ℕ) ≤ cofinite)
    (a : ModelBoundedSequence X) :
    normMatrixCStarCoronaToTracialMatrixQuotient X omega homega
        (normMatrixCStarCoronaMk (fun n => X n) a) =
      tracialMatrixQuotientMk X (omega : Filter ℕ) a :=
  rfl

/-! ## The exact Goldbring--Hart trace-ideal step -/

/-- A unital norm-corona representation of a uniquely and faithfully traced
C-star algebra remains faithful after quotienting by the trace ideal.

This is the exact contradiction-producing step of Goldbring--Hart,
Proposition 6.1, isolated from the external existence of a non-Connes-
embeddable factor. -/
theorem injective_tracialMatrixQuotient_comp_of_unique_trace
    {A : Type u} [CStarAlgebra A]
    (tau : FaithfulTracialState A)
    (hunique : forall sigma : TracialState A, forall a : A, sigma a = tau a)
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (omega : Ultrafilter ℕ) (homega : (omega : Filter ℕ) ≤ cofinite)
    (e : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n => X n)) :
    Function.Injective
      ((normMatrixCStarCoronaToTracialMatrixQuotient X omega homega).comp e) := by
  let pi : A →⋆ₐ[ℂ] TracialMatrixQuotient X (omega : Filter ℕ) :=
    (normMatrixCStarCoronaToTracialMatrixQuotient X omega homega).comp e
  change Function.Injective pi
  refine StarAlgHom.injective_of_faithfulTracialState_of_trace_preserving
    (tauA := tau) (tauB := ultratraceFaithfulTracialState X omega)
    (pi := pi) ?_
  intro a
  exact hunique
    ((ultratraceFaithfulTracialState X omega).toTracialState.compStarAlgHom pi) a

end TracialUltraproduct

end

end GroupApproximation
