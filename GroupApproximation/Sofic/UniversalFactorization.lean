import GroupApproximation.Sofic.LinearResidual
import GroupApproximation.Sofic.CoronaRadicalPullback

/-!
# Section 42: the universal quotient theorem

Section 41 pins the kernel of a surjection `Φ : W ↠ P` against several
approximation radicals at once.  Section 42 records what that identification
buys: the entire representation functor into each of the relevant classes of
targets is unchanged by passing from `W` to the explicit quotient `P`.

Everything rests on one abstract observation.  If `Φ` is onto and every
homomorphism out of `W` into a fixed target kills `ker Φ`, then precomposition
with `Φ` carries homomorphisms out of `P` bijectively onto homomorphisms out of
`W`: surjectivity of `Φ` makes precomposition injective, and the universal
property of `W ⧸ ker Φ` makes it surjective.  "Unique factorization" means
exactly this bijectivity — every homomorphism out of `W` is `ψ ∘ Φ` for one and
only one `ψ`.  The descent step asks nothing of the target beyond a monoid
structure, which is what lets the same lemma serve matrix representations,
whose target is not a group.

The instantiations differ only in the class of targets used to discharge the
kernel hypothesis: unitary groups of norm matrix coronas against the MF radical
(Theorem 42.1), finite-dimensional unitary groups against the
finite-dimensional unitary residual (Theorem 42.2), finite groups against the
finite residual (Theorem 42.3, with Corollary 42.4 covering residually finite
targets), and square matrices over an arbitrary field against the all-fields
linear residual of Section 46.  Each comes with the corresponding comparison of
radicals `Rad W = Φ⁻¹(Rad P)`, in the shape of the existing
`coronaMFResidual_eq_comap` for a quotient map: the forward inclusion is formal,
and the reverse inclusion is precisely the factorization.
-/

namespace GroupApproximation
namespace UniversalFactorization

open MatricialStabilityRadical

universe u v w

/-- A homomorphism out of `W` that kills the kernel of a surjection `Φ`
descends along `Φ`.  This is the first isomorphism theorem followed by the
universal property of the quotient, and it needs only a monoid structure on the
target, so it applies to matrix representations as well as to unitary ones. -/
theorem exists_comp_eq {W : Type u} [Group W] {P : Type v} [Group P]
    {T : Type w} [Monoid T] (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (θ : W →* T) (hθ : Φ.ker ≤ θ.ker) : ∃ ψ : P →* T, ψ.comp Φ = θ := by
  let e : W ⧸ Φ.ker ≃* P := QuotientGroup.liftEquiv Φ.ker hsurj rfl
  refine ⟨(QuotientGroup.lift Φ.ker θ hθ).comp e.symm.toMonoidHom,
    MonoidHom.ext fun x ↦ ?_⟩
  have hx : e.symm (Φ x) = (QuotientGroup.mk x : W ⧸ Φ.ker) :=
    e.symm_apply_apply (QuotientGroup.mk x)
  show (QuotientGroup.lift Φ.ker θ hθ) (e.symm (Φ x)) = θ x
  rw [hx, QuotientGroup.lift_mk']

/-- **The factorization lemma.**  If `Φ` is onto and its kernel is invisible to
every homomorphism from `W` to `T`, then precomposition with `Φ` is a bijection
from homomorphisms `P →* T` to homomorphisms `W →* T`: every homomorphism out
of `W` factors through `P`, and does so in exactly one way. -/
theorem comp_bijective_of_ker_le {W : Type u} [Group W] {P : Type v} [Group P]
    {T : Type w} [Monoid T] (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (hker : ∀ θ : W →* T, Φ.ker ≤ θ.ker) :
    Function.Bijective (fun ψ : P →* T ↦ ψ.comp Φ) := by
  constructor
  · intro ψ₁ ψ₂ h
    refine MonoidHom.ext fun p ↦ ?_
    obtain ⟨x, rfl⟩ := hsurj p
    exact DFunLike.congr_fun h x
  · intro θ
    exact exists_comp_eq Φ hsurj θ (hker θ)

variable {W : Type u} [Group W] {P : Type v} [Group P]

/-! ## The four target classes -/

/-- **Theorem 42.1.**  When the kernel of a surjection lies inside the MF
radical, precomposition is a bijection on homomorphisms into the unitary group
of any standard cofinite norm matrix corona: every matrix-corona representation
of `W` factors uniquely through `P`. -/
theorem corona_comp_bijective (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ coronaMFResidual W) (X : ℕ → FiniteModel)
    (hX : ∀ n, 0 < Fintype.card (X n)) :
    Function.Bijective (fun ψ : P →* NormMatrixCoronaUnitary X ↦ ψ.comp Φ) :=
  comp_bijective_of_ker_le Φ hsurj fun θ _ hx ↦
    MonoidHom.mem_ker.mpr (hker hx X hX θ)

/-- **Theorem 42.2.**  When the kernel of a surjection lies inside the
finite-dimensional unitary residual, finite-dimensional unitary representation
theory cannot distinguish `W` from `P`: precomposition is a bijection on
homomorphisms into the unitary group of every finite model. -/
theorem fdUnitary_comp_bijective (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ fdUnitaryResidual W) (Y : FiniteModel) :
    Function.Bijective (fun ψ : P →* Matrix.unitaryGroup Y ℂ ↦ ψ.comp Φ) :=
  comp_bijective_of_ker_le Φ hsurj fun θ _ hx ↦
    MonoidHom.mem_ker.mpr (mem_fdUnitaryResidual_iff.mp (hker hx) Y θ)

/-- **Theorem 42.3.**  When the kernel of a surjection lies inside the finite
residual, precomposition is a bijection on homomorphisms into every finite
group.  The kernel of a homomorphism to a finite group has finite index, so the
finite residual is invisible to it. -/
theorem finite_comp_bijective (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ finiteResidual W) (T : Type w) [Group T] [Finite T] :
    Function.Bijective (fun ψ : P →* T ↦ ψ.comp Φ) := by
  refine comp_bijective_of_ker_le Φ hsurj fun θ _ hx ↦ ?_
  haveI : Finite θ.range := Subtype.finite
  exact mem_finiteResidual_iff.mp (hker hx) θ.ker inferInstance

/-- **Corollary 42.4.**  The same conclusion for an arbitrary residually finite
target: a homomorphism from `W` to a residually finite group cannot see the
finite residual, so it factors uniquely through `P`. -/
theorem residuallyFinite_comp_bijective (Φ : W →* P)
    (hsurj : Function.Surjective Φ) (hker : Φ.ker ≤ finiteResidual W)
    (T : Type w) [Group T] (hT : IsResiduallyFinite T) :
    Function.Bijective (fun ψ : P →* T ↦ ψ.comp Φ) :=
  comp_bijective_of_ker_le Φ hsurj fun θ ↦
    hker.trans (finiteResidual_le_ker θ hT)

/-- When the kernel of a surjection lies inside the all-fields linear residual,
precomposition is a bijection on homomorphisms into the square matrices of any
size over any field in `Type`.  The target here is a monoid rather than a
group, which is why the factorization lemma is stated for monoid targets. -/
theorem linear_comp_bijective (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ linearResidual W) (F : Type) [Field F] (d : ℕ) :
    Function.Bijective
      (fun ψ : P →* Matrix (Fin d) (Fin d) F ↦ ψ.comp Φ) :=
  comp_bijective_of_ker_le Φ hsurj fun θ _ hx ↦
    MonoidHom.mem_ker.mpr (hker hx F inferInstance d θ)

/-! ## The radicals correspond -/

/-- The MF radical of the source is the preimage of the MF radical of the
target.  The forward inclusion holds for any homomorphism; the reverse one uses
Theorem 42.1 to pull a corona representation of `W` back from one of `P`. -/
theorem coronaMFResidual_eq_comap (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ coronaMFResidual W) :
    coronaMFResidual W = (coronaMFResidual P).comap Φ := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_comap]
    intro X hX ψ
    exact hx X hX (ψ.comp Φ)
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    intro X hX θ
    obtain ⟨ψ, hψ⟩ := exists_comp_eq Φ hsurj θ
      fun _ hy ↦ MonoidHom.mem_ker.mpr (hker hy X hX θ)
    rw [← hψ]
    exact hx X hX ψ

/-- The finite-dimensional unitary residual of the source is the preimage of
the finite-dimensional unitary residual of the target. -/
theorem fdUnitaryResidual_eq_comap (Φ : W →* P)
    (hsurj : Function.Surjective Φ) (hker : Φ.ker ≤ fdUnitaryResidual W) :
    fdUnitaryResidual W = (fdUnitaryResidual P).comap Φ := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_comap, mem_fdUnitaryResidual_iff]
    intro Y ψ
    exact mem_fdUnitaryResidual_iff.mp hx Y (ψ.comp Φ)
  · intro x hx
    rw [Subgroup.mem_comap, mem_fdUnitaryResidual_iff] at hx
    rw [mem_fdUnitaryResidual_iff]
    intro Y θ
    obtain ⟨ψ, hψ⟩ := exists_comp_eq Φ hsurj θ
      fun _ hy ↦
        MonoidHom.mem_ker.mpr (mem_fdUnitaryResidual_iff.mp (hker hy) Y θ)
    rw [← hψ]
    exact hx Y ψ

/-- The finite residual of the source is the preimage of the finite residual of
the target.  A finite-index subgroup of `W` is tested through the finite
quotient by its normal core, which descends to `P` by Theorem 42.3, and the
descended homomorphism again has finite-index kernel. -/
theorem finiteResidual_eq_comap (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ finiteResidual W) :
    finiteResidual W = (finiteResidual P).comap Φ := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_comap]
    exact map_finiteResidual_le Φ (Subgroup.mem_map_of_mem Φ hx)
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [mem_finiteResidual_iff]
    intro L hL
    haveI := hL
    haveI : Finite (W ⧸ L.normalCore) :=
      L.normalCore.finite_quotient_of_finiteIndex
    have hkerθ : Φ.ker ≤ (QuotientGroup.mk' L.normalCore).ker := by
      intro y hy
      rw [QuotientGroup.ker_mk']
      exact mem_finiteResidual_iff.mp (hker hy) L.normalCore inferInstance
    obtain ⟨ψ, hψ⟩ :=
      exists_comp_eq Φ hsurj (QuotientGroup.mk' L.normalCore) hkerθ
    haveI : Finite ψ.range := Subtype.finite
    have hψx : ψ (Φ x) = 1 :=
      MonoidHom.mem_ker.mp (mem_finiteResidual_iff.mp hx ψ.ker inferInstance)
    have hθx : (QuotientGroup.mk' L.normalCore) x = 1 := by
      rw [← hψ]
      exact hψx
    exact L.normalCore_le ((QuotientGroup.eq_one_iff x).mp hθx)

/-- The all-fields linear residual of the source is the preimage of the
all-fields linear residual of the target. -/
theorem linearResidual_eq_comap (Φ : W →* P) (hsurj : Function.Surjective Φ)
    (hker : Φ.ker ≤ linearResidual W) :
    linearResidual W = (linearResidual P).comap Φ := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_comap]
    intro F hF d ψ
    exact hx F hF d (ψ.comp Φ)
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    intro F hF d θ
    obtain ⟨ψ, hψ⟩ := exists_comp_eq Φ hsurj θ
      fun _ hy ↦ MonoidHom.mem_ker.mpr (hker hy F hF d θ)
    rw [← hψ]
    exact hx F hF d ψ

end UniversalFactorization
end GroupApproximation
