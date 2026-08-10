import NonsoficGroupsExist.Sofic.FreeLampReduction
import NonsoficGroupsExist.Sofic.WeakMFTransfer

/-!
# Weak-MF nonsofic doubles and finite-lamp amalgams

This file records the formal endpoint of the weak-MF double argument.  For a
pair `Γ ≤ G`, put

`H K = G *_Γ (Γ × K)`.

For the Kun--Thom pair, the operator-algebraic argument in
`docs/WEAK_MF_NONSOFIC_DOUBLE.md` proves that `H K` is weak-MF for every
finite `K`: profinite regular representations detect the amalgamation
subalgebra, Shulman's MF amalgamation theorem handles a finite star of copies,
and the exact induced representation handles the finite extension.  That
analytic conclusion is an explicit premise of the endpoint theorems below;
it is not something Lean's current C*-algebra library proves.

Everything after that boundary is kernel-checked here.  In particular,
Kun--Thom centralizer normalization plus one strict compressor forces every
nontrivial finite-lamp amalgam to be nonsofic.  Combining the two inputs gives
an explicit family of groups which are weak-MF but not sofic.

The final results use the literal conjunction `IsWeakMF H ∧ ¬ IsSofic H`.
In particular, the cited analytic premises remain visible in every theorem
signature rather than being hidden behind a proposition alias.
-/

namespace NonsoficGroupsExist

open Monoid

variable (G : Type) [Group G] (Γ : Subgroup G)

/-! ## The symmetric double -/

/-- The two vertex groups of the symmetric amalgam. -/
abbrev DoubleFactor : Bool → Type := fun _ ↦ G

instance doubleFactorGroup : ∀ b, Group (DoubleFactor G b) :=
  fun _ ↦ inferInstanceAs (Group G)

/-- Both edge maps are the inclusion `Γ ↪ G`. -/
def doubleMap : ∀ b, ↥Γ →* DoubleFactor G b := fun _ ↦ Γ.subtype

theorem doubleMap_injective : ∀ b, Function.Injective (doubleMap G Γ b) :=
  fun _ ↦ Γ.subtype_injective

/-- The symmetric double `G *_Γ G`. -/
abbrev SymmetricDouble : Type := PushoutI (doubleMap G Γ)

/-- One of the two canonical vertex-group embeddings. -/
def inDouble (b : Bool) : G →* SymmetricDouble G Γ :=
  PushoutI.of (φ := doubleMap G Γ) b

theorem inDouble_injective (b : Bool) :
    Function.Injective (inDouble G Γ b) :=
  PushoutI.of_injective (doubleMap_injective G Γ) b

instance doubleFactorCountable [Countable G] :
    ∀ b, Countable (DoubleFactor G b) := fun _ ↦ inferInstanceAs (Countable G)

instance symmetricDoubleCountable [Countable G] :
    Countable (SymmetricDouble G Γ) := by
  haveI h0 : Countable (FreeMonoid (Σ b, DoubleFactor G b)) :=
    inferInstanceAs (Countable (List (Σ b, DoubleFactor G b)))
  haveI h1 : Countable (CoprodI (DoubleFactor G)) :=
    Con.mk'_surjective.countable
  haveI h2 : Countable (FreeMonoid (CoprodI (DoubleFactor G) ⊕ ↥Γ)) :=
    inferInstanceAs (Countable (List (CoprodI (DoubleFactor G) ⊕ ↥Γ)))
  haveI h3 : Countable (Coprod (CoprodI (DoubleFactor G)) ↥Γ) :=
    Con.mk'_surjective.countable
  exact Con.mk'_surjective.countable

/-- **The weak-MF nonsofic symmetric double.**  The operator-algebraic and
finite-extension inputs are explicitly named.  Given them, the Kun--Thom
normalization argument proving nonsoficity is kernel-checked. -/
theorem weakMF_and_not_isSofic_symmetricDouble_of_analytic_inputs [Countable G]
    (hMF : IsWeakMF (SymmetricDouble G Γ))
    (hflip : IsSofic (SymmetricDouble G Γ) →
      IsSofic (FreeLamp G Γ (Multiplicative (ZMod 2))))
    (hcn : CentralizerNormalization G Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hstrict : t⁻¹ * γ * t ∉ Γ) :
    IsWeakMF (SymmetricDouble G Γ) ∧ ¬ IsSofic (SymmetricDouble G Γ) := by
  obtain ⟨k, hk⟩ := exists_ne (1 : Multiplicative (ZMod 2))
  refine ⟨hMF, ?_⟩
  intro hsofic
  exact freeLamp_not_isSofic G Γ (Multiplicative (ZMod 2))
    hcn hγ hstrict hk (hflip hsofic)

/-- **Finite-lamp weak-MF/nonsofic separation.**

Assume the regular-amalgam weak-MF input and Kun--Thom centralizer
normalization for `Γ ≤ G`.  If one conjugate of an element of `Γ` leaves
`Γ`, then every nontrivial finite lamp produces a weak-MF nonsofic group.

The weak-MF conjunct is exactly the analytic input.  The nonsofic conjunct is
the fully formalized amalgam normal-form/centralizer-normalization reduction
from `FreeLampReduction`. -/
theorem weakMF_and_not_isSofic_freeLamp_of_analytic_input [Countable G]
    {K : Type} [Group K] [Finite K] [Nontrivial K]
    (hMF : IsWeakMF (FreeLamp G Γ K))
    (hcn : CentralizerNormalization G Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hstrict : t⁻¹ * γ * t ∉ Γ)
    : IsWeakMF (FreeLamp G Γ K) ∧ ¬ IsSofic (FreeLamp G Γ K) := by
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  exact ⟨hMF, freeLamp_not_isSofic G Γ K hcn hγ hstrict hk⟩

/-- The family theorem in pointwise form: no choice of a nontrivial finite
lamp can restore soficity or destroy weak-MF. -/
theorem every_finiteLamp_weakMF_and_not_isSofic_of_analytic_inputs [Countable G]
    (hMF : ∀ (K : Type) [Group K] [Finite K],
      IsWeakMF (FreeLamp G Γ K))
    (hcn : CentralizerNormalization G Γ)
    {t γ : G} (hγ : γ ∈ Γ) (hstrict : t⁻¹ * γ * t ∉ Γ) :
    ∀ (K : Type) [Group K] [Finite K] [Nontrivial K],
      IsWeakMF (FreeLamp G Γ K) ∧ ¬ IsSofic (FreeLamp G Γ K) := by
  intro K _ _ _
  exact weakMF_and_not_isSofic_freeLamp_of_analytic_input
    G Γ (hMF K) hcn hγ hstrict

end NonsoficGroupsExist
