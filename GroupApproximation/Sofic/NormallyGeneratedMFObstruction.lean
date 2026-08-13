import GroupApproximation.Sofic.NormMFResidualFunctorial
import GroupApproximation.Kazhdan.Kazhdan
import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Normally generated MF obstructions

An MF-invisible element which normally generates its ambient group forces the
whole norm-MF residual to be the ambient group.  Consequently every
homomorphism to a group with trivial norm-MF residual is trivial.  This file
also packages the input supplied by a normally generated finitely presented
Kazhdan envelope theorem as explicit data: no existence theorem is postulated.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v w x

variable {Γ : Type u} [Group Γ]

/-- Every finite-dimensional linear representation, over every field, is
trivial.  The explicit name records the field-general statement and avoids
identifying it with any one topological convention for "almost periodic". -/
def AllFiniteDimensionalRepresentationsTrivial
    (Γ : Type u) [Group Γ] : Prop :=
  ∀ {k : Type v} {V : Type w} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V], ∀ π : Γ →* (Module.End k V)ˣ, π = 1

/-- A homomorphism is trivial as soon as it kills an element which normally
generates its source.  This is the purely algebraic bridge from a marked
finite-dimensional kill theorem to field-general representation-triviality
of a normally generated envelope; it makes no assumption on the target. -/
theorem hom_eq_one_of_map_eq_one_of_normalClosure_eq_top {x : Γ}
    (hgen : Subgroup.normalClosure ({x} : Set Γ) = ⊤)
    {M : Type v} [Group M] (f : Γ →* M) (hx : f x = 1) : f = 1 := by
  apply MonoidHom.ext
  intro g
  have hclosure : Subgroup.normalClosure ({x} : Set Γ) ≤ f.ker := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact (MonoidHom.mem_ker).mpr hx
  apply MonoidHom.mem_ker.mp
  apply hclosure
  rw [hgen]
  exact Subgroup.mem_top g

/-- If a normally generating element lies in the commutator subgroup, then
the whole group is perfect. -/
theorem isPerfect_of_mem_commutator_normalClosure_eq_top {x : Γ}
    (hx : x ∈ commutator Γ)
    (hgen : Subgroup.normalClosure ({x} : Set Γ) = ⊤) :
    Group.IsPerfect Γ := by
  rw [Group.isPerfect_def, eq_top_iff]
  intro g _
  have hclosure : Subgroup.normalClosure ({x} : Set Γ) ≤ commutator Γ := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hx
  apply hclosure
  rw [hgen]
  exact Subgroup.mem_top g

/-- If an MF-invisible element normally generates the group, then every
element is MF-invisible. -/
theorem normMFResidual_eq_top_of_mem_normalClosure_eq_top {x : Γ}
    (hx : x ∈ normMFResidual Γ)
    (hgen : Subgroup.normalClosure ({x} : Set Γ) = ⊤) :
    normMFResidual Γ = ⊤ := by
  apply top_unique
  rw [← hgen]
  apply Subgroup.normalClosure_le_normal
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  simpa [hy] using hx

/-- Full source residual and trivial target residual force every homomorphism
to be pointwise trivial.  No countability hypothesis is needed. -/
theorem map_eq_one_of_residual_eq_top_to_residual_eq_bot
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] (hM : normMFResidual M = ⊥)
    (f : Γ →* M) (g : Γ) : f g = 1 := by
  have hg : g ∈ normMFResidual Γ := by
    rw [hΓ]
    exact Subgroup.mem_top g
  have hfg : f g ∈ normMFResidual M :=
    mem_normMFResidual_iff.mpr
      ((mem_normMFResidual_iff.mp hg).map f)
  rw [hM] at hfg
  exact Subgroup.mem_bot.mp hfg

/-- Homomorphism-level form of
`map_eq_one_of_residual_eq_top_to_residual_eq_bot`. -/
theorem hom_eq_one_of_residual_eq_top_to_residual_eq_bot
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] (hM : normMFResidual M = ⊥)
    (f : Γ →* M) : f = 1 := by
  ext g
  exact map_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ hM f g

/-- A full-residual group has no nontrivial quotient whose residual is
trivial. -/
theorem not_surjective_of_residual_eq_top_to_residual_eq_bot
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Nontrivial M]
    (hM : normMFResidual M = ⊥) (f : Γ →* M) :
    ¬ Function.Surjective f := by
  intro hsurj
  obtain ⟨m, hm⟩ := exists_ne (1 : M)
  obtain ⟨g, rfl⟩ := hsurj m
  exact hm (map_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ hM f g)

/-- Every homomorphism from a full-residual group to a countable
operator-MF group is trivial. -/
theorem hom_eq_one_of_residual_eq_top_to_isOperatorMF
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Countable M]
    (hM : IsOperatorMF M) (f : Γ →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isOperatorMF hM) f

/-- There is no nontrivial countable operator-MF quotient of a
full-residual group. -/
theorem not_surjective_of_residual_eq_top_to_isOperatorMF
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Countable M] [Nontrivial M]
    (hM : IsOperatorMF M) (f : Γ →* M) :
    ¬ Function.Surjective f :=
  not_surjective_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isOperatorMF hM) f

/-- Every homomorphism from a full-residual group to a finite group is
trivial. -/
theorem hom_eq_one_of_residual_eq_top_to_finite
    (hΓ : normMFResidual Γ = ⊤)
    (M : Type) [Group M] [Finite M] (f : Γ →* M) : f = 1 := by
  exact hom_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isWeakMF (isWeakMF_of_finite M)) f

/-- A full-residual group has no nontrivial finite quotient. -/
theorem not_surjective_of_residual_eq_top_to_finite
    (hΓ : normMFResidual Γ = ⊤)
    (M : Type) [Group M] [Finite M] [Nontrivial M]
    (f : Γ →* M) : ¬ Function.Surjective f := by
  exact not_surjective_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isWeakMF (isWeakMF_of_finite M)) f

/-- Every homomorphism from a full-residual group to a countable residually
finite group is trivial. -/
theorem hom_eq_one_of_residual_eq_top_to_residuallyFinite
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Countable M] [Group.ResiduallyFinite M]
    (f : Γ →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isWeakMF
      (isWeakMF_of_residuallyFinite (H := M))) f

/-- A full-residual group has no nontrivial countable residually finite
quotient. -/
theorem not_surjective_of_residual_eq_top_to_residuallyFinite
    (hΓ : normMFResidual Γ = ⊤)
    {M : Type v} [Group M] [Countable M] [Group.ResiduallyFinite M]
    [Nontrivial M] (f : Γ →* M) : ¬ Function.Surjective f :=
  not_surjective_of_residual_eq_top_to_residual_eq_bot hΓ
    (normMFResidual_eq_bot_of_isWeakMF
      (isWeakMF_of_residuallyFinite (H := M))) f

/-! ## Explicit envelope data -/

/-- Data furnished by a normally generated finitely presented Kazhdan
envelope theorem.  The literature-dependent existence of such data is not
asserted here: a consumer must provide the envelope, embedding, and proofs. -/
structure NormallyGeneratedKazhdanEnvelopeData
    (E : Type u) [Group E] (w : E) where
  Envelope : Type v
  [groupEnvelope : Group Envelope]
  embedding : E →* Envelope
  embedding_injective : Function.Injective embedding
  [finitelyPresented : Group.IsFinitelyPresented Envelope]
  kazhdan : HasKazhdanPropertyT.{v, 0} Envelope
  normally_generates :
    Subgroup.normalClosure ({embedding w} : Set Envelope) = ⊤

namespace NormallyGeneratedKazhdanEnvelopeData

variable {E : Type u} [Group E] {w : E}
    (D : NormallyGeneratedKazhdanEnvelopeData.{u, v} E w)

local instance : Group D.Envelope := D.groupEnvelope
local instance : Group.IsFinitelyPresented D.Envelope := D.finitelyPresented

/-- A finitely presented group is countable, extracted directly from its
finite free-group presentation. -/
theorem envelopeCountable : Countable D.Envelope := by
  obtain ⟨n, f, hsurj, -⟩ := D.finitelyPresented.out
  letI : Countable (FreeGroup (Fin n)) := by
    have hfree : Function.Surjective
        (FreeGroup.mk : List (Fin n × Bool) → FreeGroup (Fin n)) := by
      intro g
      obtain ⟨L, hL⟩ := Quot.exists_rep g
      exact ⟨L, by rw [← FreeGroup.quot_mk_eq_mk, hL]⟩
    exact hfree.countable
  exact hsurj.countable

/-- Injectivity of the envelope embedding preserves nontriviality of the
marked element. -/
theorem embedding_ne_one {hw : w ≠ 1} : D.embedding w ≠ 1 := by
  intro h
  apply hw
  apply D.embedding_injective
  simpa using h

/-- Any homomorphism out of the envelope is trivial once it kills the
normally generating embedded mark.  In particular, a finite-dimensional
kill theorem for the source mark can be transported through `embedding` and
then upgraded to triviality of the whole envelope representation. -/
theorem hom_eq_one_of_map_embedding_eq_one
    {M : Type*} [Group M] (f : D.Envelope →* M)
    (hw : f (D.embedding w) = 1) : f = 1 :=
  hom_eq_one_of_map_eq_one_of_normalClosure_eq_top
    D.normally_generates f hw

/-- Precomposition form of `hom_eq_one_of_map_embedding_eq_one`.  It is
tailored to a marked kill theorem on the source: if the restriction of an
envelope representation along `embedding` kills `w`, normal generation
forces the entire envelope representation to be trivial. -/
theorem hom_eq_one_of_comp_embedding_map_eq_one
    {M : Type*} [Group M] (f : D.Envelope →* M)
    (hw : (f.comp D.embedding) w = 1) : f = 1 := by
  apply D.hom_eq_one_of_map_embedding_eq_one f
  simpa using hw

/-- A field-general marked kill theorem on the source upgrades, by
precomposition and normal generation, to triviality of every
finite-dimensional linear representation of the envelope. -/
theorem allFiniteDimensionalRepresentationsTrivial
    (hkill : ∀ {k : Type w} {V : Type x}
      [Field k] [AddCommGroup V] [Module k V]
      [FiniteDimensional k V],
      ∀ π : E →* (Module.End k V)ˣ, π w = 1) :
    AllFiniteDimensionalRepresentationsTrivial.{v, w, x} D.Envelope := by
  intro k V _ _ _ _ π
  apply D.hom_eq_one_of_comp_embedding_map_eq_one π
  exact hkill (k := k) (V := V) (π.comp D.embedding)

/-- The supplied envelope is perfect whenever its normally generating
embedded mark belongs to its commutator subgroup. -/
theorem envelopeIsPerfect
    (hw : D.embedding w ∈ commutator D.Envelope) :
    Group.IsPerfect D.Envelope :=
  isPerfect_of_mem_commutator_normalClosure_eq_top hw D.normally_generates

/-- A concrete source commutator remains a commutator under the envelope
embedding; if it is the normally generating mark, the envelope is perfect. -/
theorem envelopeIsPerfect_of_eq_commutator (a b : E)
    (hw : w = ⁅a, b⁆) : Group.IsPerfect D.Envelope := by
  apply D.envelopeIsPerfect
  have hmap : D.embedding w = ⁅D.embedding a, D.embedding b⁆ := by
    calc
      D.embedding w = D.embedding ⁅a, b⁆ := congrArg D.embedding hw
      _ = ⁅D.embedding a, D.embedding b⁆ := map_commutatorElement D.embedding a b
  rw [hmap]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- MF invisibility is portable through the envelope embedding. -/
theorem embedding_mem_normMFResidual
    (hw : w ∈ normMFResidual E) :
    D.embedding w ∈ normMFResidual D.Envelope :=
  mem_normMFResidual_iff.mpr
    ((mem_normMFResidual_iff.mp hw).map D.embedding)

/-- The normally generated envelope has full norm-MF residual. -/
theorem envelope_normMFResidual_eq_top
    (hw : w ∈ normMFResidual E) :
    normMFResidual D.Envelope = ⊤ :=
  normMFResidual_eq_top_of_mem_normalClosure_eq_top
    (D.embedding_mem_normMFResidual hw) D.normally_generates

/-- Every homomorphism from the envelope to a residual-free group is
trivial. -/
theorem hom_eq_one_to_residualFree
    (hw : w ∈ normMFResidual E)
    {M : Type*} [Group M] (hM : normMFResidual M = ⊥)
    (f : D.Envelope →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_residual_eq_bot
    (D.envelope_normMFResidual_eq_top hw) hM f

/-- Every homomorphism from the envelope to an operator-MF group is
trivial, with no countability assumption on the target: its range is
countable and inherits operator-MF. -/
theorem hom_eq_one_to_isOperatorMF
    (hw : w ∈ normMFResidual E)
    {M : Type*} [Group M] (hM : IsOperatorMF M)
    (f : D.Envelope →* M) : f = 1 := by
  letI : Countable D.Envelope := D.envelopeCountable
  apply MonoidHom.ext
  intro g
  exact map_eq_one_of_normMFResidual_eq_top_to_isOperatorMF
    (D.envelope_normMFResidual_eq_top hw) hM f g

/-- The envelope itself is not operator-MF when the source mark is
nontrivial and invisible. -/
theorem not_isOperatorMF
    (hw : w ∈ normMFResidual E) (hw1 : w ≠ 1) :
    ¬ IsOperatorMF D.Envelope := by
  intro hMF
  have htrivial := D.hom_eq_one_to_isOperatorMF hw hMF
    (MonoidHom.id D.Envelope)
  have himage : D.embedding w = 1 := by
    simpa using DFunLike.congr_fun htrivial (D.embedding w)
  exact D.embedding_ne_one (hw := hw1) himage

/-- Every homomorphism from the envelope to a finite group is trivial. -/
theorem hom_eq_one_to_finite
    (hw : w ∈ normMFResidual E)
    (M : Type) [Group M] [Finite M] (f : D.Envelope →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_finite
    (D.envelope_normMFResidual_eq_top hw) M f

/-- Every homomorphism from the envelope to a countable residually finite
group is trivial. -/
theorem hom_eq_one_to_residuallyFinite
    (hw : w ∈ normMFResidual E)
    {M : Type*} [Group M] [Countable M] [Group.ResiduallyFinite M]
    (f : D.Envelope →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_residuallyFinite
    (D.envelope_normMFResidual_eq_top hw) f

/-- Formal consequence package: the supplied envelope is finitely presented,
Kazhdan, has full MF residual, and is not operator-MF. -/
theorem consequence_package
    (hw : w ∈ normMFResidual E) (hw1 : w ≠ 1) :
    Group.IsFinitelyPresented D.Envelope ∧
      HasKazhdanPropertyT.{v, 0} D.Envelope ∧
      normMFResidual D.Envelope = ⊤ ∧
      ¬ IsOperatorMF D.Envelope :=
  ⟨D.finitelyPresented, D.kazhdan,
    D.envelope_normMFResidual_eq_top hw,
    D.not_isOperatorMF hw hw1⟩

end NormallyGeneratedKazhdanEnvelopeData
end GroupApproximation
