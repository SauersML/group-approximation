import GroupApproximation.Sofic.MarkedGroupWordBall
import GroupApproximation.Sofic.OperatorMFLocalNormalization

/-!
# Operator-MF groups form a closed set in marked-group space

The proof is a finite-cylinder argument.  A failed normalized local model
for a marked quotient is witnessed on a finite subset.  Recording finitely
many multiplication and inequality words ensures that any nearby marked
quotient model pulls back to a model of the original finite subset.  Thus
failure is open, and normalized norm approximability—equivalently MF—is
closed.
-/

namespace GroupApproximation

open Filter Set Topology

noncomputable section

universe u

namespace MarkedGroupSpace

variable {k : ℕ}

private theorem freeGroupCountable : Countable (FreeGroup (Fin k)) := by
  have hsurj : Function.Surjective
      (FreeGroup.mk : List (Fin k × Bool) → FreeGroup (Fin k)) := by
    intro g
    obtain ⟨L, hL⟩ := Quot.exists_rep g
    exact ⟨L, by rw [← FreeGroup.quot_mk_eq_mk, hL]⟩
  exact hsurj.countable

/-- Every fixed-rank marked quotient is countable. -/
theorem quotientCountable (M : MarkedGroupSpace k) : Countable M.Quotient := by
  letI : Countable (FreeGroup (Fin k)) := freeGroupCountable
  exact (QuotientGroup.mk'_surjective M.relations).countable

/-- A fixed word representative for each element of a marked quotient. -/
def representative (M : MarkedGroupSpace k) (g : M.Quotient) :
    FreeGroup (Fin k) :=
  Classical.choose (QuotientGroup.mk'_surjective M.relations g)

@[simp]
theorem mk_representative (M : MarkedGroupSpace k) (g : M.Quotient) :
    QuotientGroup.mk (M.representative g) = g :=
  Classical.choose_spec (QuotientGroup.mk'_surjective M.relations g)

/-- The word which records multiplication of two chosen quotient
representatives. -/
def multiplicationWord (M : MarkedGroupSpace k)
    (g h : M.Quotient) : FreeGroup (Fin k) :=
  (M.representative (g * h))⁻¹ * M.representative g * M.representative h

/-- The word which records equality of two chosen quotient representatives. -/
def equalityWord (M : MarkedGroupSpace k)
    (g h : M.Quotient) : FreeGroup (Fin k) :=
  (M.representative g)⁻¹ * M.representative h

/-- The finite set of multiplication and equality tests needed to transfer a
local model on `K` across a marked-group cylinder. -/
def modelControlWords (M : MarkedGroupSpace k)
    (K : Finset M.Quotient) : Finset (FreeGroup (Fin k)) :=
  ((K ×ˢ K).image fun q ↦ M.multiplicationWord q.1 q.2) ∪
    ((K ×ˢ K).image fun q ↦ M.equalityWord q.1 q.2)

theorem multiplicationWord_mem_relations (M : MarkedGroupSpace k)
    (g h : M.Quotient) : M.multiplicationWord g h ∈ M.relations := by
  rw [← QuotientGroup.eq_one_iff]
  simp [multiplicationWord]

theorem equalityWord_mem_relations_iff (M : MarkedGroupSpace k)
    (g h : M.Quotient) :
    M.equalityWord g h ∈ M.relations ↔ g = h := by
  rw [← QuotientGroup.eq_one_iff]
  unfold equalityWord
  rw [← QuotientGroup.mk'_apply, map_mul, map_inv]
  simp only [QuotientGroup.mk'_apply, mk_representative]
  exact inv_mul_eq_one

/-- Send an element of one marked quotient to another by evaluating the
chosen representative word.  This is deliberately only a function; the
finite cylinder supplies exactly the multiplication identities needed on
the finite test set. -/
def projectRepresentative (M N : MarkedGroupSpace k) :
    M.Quotient → N.Quotient := fun g ↦
  QuotientGroup.mk (M.representative g)

theorem projectRepresentative_mul_of_mem_cylinder
    (M N : MarkedGroupSpace k) (K : Finset M.Quotient)
    (hN : N ∈ cylinder M (M.modelControlWords K))
    {g h : M.Quotient} (hg : g ∈ K) (hh : h ∈ K) :
    M.projectRepresentative N (g * h) =
      M.projectRepresentative N g * M.projectRepresentative N h := by
  have hwmem : M.multiplicationWord g h ∈ M.modelControlWords K := by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr
      ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩
  have hwM : M.multiplicationWord g h ∈ M.relations :=
    multiplicationWord_mem_relations M g h
  have hwN : M.multiplicationWord g h ∈ N.relations :=
    ((mem_cylinder_iff M N (M.modelControlWords K)).mp hN
      _ hwmem).mpr hwM
  rw [← QuotientGroup.eq_one_iff] at hwN
  rw [← QuotientGroup.mk'_apply] at hwN
  rw [← inv_mul_eq_one]
  unfold projectRepresentative
  unfold multiplicationWord at hwN
  rw [map_mul, map_mul, map_inv] at hwN
  simp only [QuotientGroup.mk'_apply] at hwN
  simpa only [mul_assoc] using hwN

theorem projectRepresentative_ne_of_mem_cylinder
    (M N : MarkedGroupSpace k) (K : Finset M.Quotient)
    (hN : N ∈ cylinder M (M.modelControlWords K))
    {g h : M.Quotient} (hg : g ∈ K) (hh : h ∈ K) (hgh : g ≠ h) :
    M.projectRepresentative N g ≠ M.projectRepresentative N h := by
  intro heq
  have hwmem : M.equalityWord g h ∈ M.modelControlWords K := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr
      ⟨(g, h), Finset.mem_product.mpr ⟨hg, hh⟩, rfl⟩
  have hwN : M.equalityWord g h ∈ N.relations := by
    rw [← QuotientGroup.eq_one_iff]
    change (M.projectRepresentative N g)⁻¹ *
      M.projectRepresentative N h = 1
    exact inv_mul_eq_one.mpr heq
  have hwM : M.equalityWord g h ∈ M.relations :=
    ((mem_cylinder_iff M N (M.modelControlWords K)).mp hN
      _ hwmem).mp hwN
  exact hgh ((equalityWord_mem_relations_iff M g h).mp hwM)

/-- A local norm model in a nearby marked quotient pulls back along chosen
word representatives once the control cylinder fixes the finite
multiplication table and inequalities. -/
def _root_.GroupApproximation.NormModel.ofMarkedCylinder
    (M N : MarkedGroupSpace k) [DecidableEq N.Quotient]
    (K : Finset M.Quotient)
    (hN : N ∈ cylinder M (M.modelControlWords K))
    {δ ε : ℝ}
    (A : NormModel N.Quotient
      (K.image (M.projectRepresentative N)) δ ε) :
    NormModel M.Quotient K δ ε where
  carrier := A.carrier
  nonempty := A.nonempty
  map := fun g ↦ A.map (M.projectRepresentative N g)
  isUnitary := fun g ↦ A.isUnitary _
  multiplicative := by
    intro g hg h hh
    rw [projectRepresentative_mul_of_mem_cylinder M N K hN hg hh]
    exact A.multiplicative _ (Finset.mem_image_of_mem _ hg)
      _ (Finset.mem_image_of_mem _ hh)
  separated := by
    classical
    intro g hg h hh hgh
    exact A.separated _ (Finset.mem_image_of_mem _ hg)
      _ (Finset.mem_image_of_mem _ hh)
      (projectRepresentative_ne_of_mem_cylinder M N K hN hg hh hgh)

/-- The locus of marked groups admitting normalized local operator-norm
models. -/
def normApproximableOneLocus (k : ℕ) : Set (MarkedGroupSpace k) :=
  {M | IsNormApproximable M.Quotient 1}

/-- Failure of normalized norm approximability has an explicit finite-word
cylinder certificate. -/
theorem exists_cylinder_subset_compl_normApproximableOneLocus
    (M : MarkedGroupSpace k) (hM : ¬ IsNormApproximable M.Quotient 1) :
    ∃ F : Finset (FreeGroup (Fin k)),
      cylinder M F ⊆ (normApproximableOneLocus k)ᶜ := by
  classical
  unfold IsNormApproximable at hM
  push Not at hM
  obtain ⟨K, ε, hε, hno⟩ := hM
  refine ⟨M.modelControlWords K, ?_⟩
  intro N hN hNapprox
  have happrox : IsNormApproximable N.Quotient 1 := hNapprox
  obtain ⟨A⟩ := happrox (K.image (M.projectRepresentative N)) ε hε
  exact @IsEmpty.false _ hno (A.ofMarkedCylinder M N K hN)

/-- Normalized local norm approximability is closed in fixed-rank
marked-group space. -/
theorem isClosed_normApproximableOneLocus :
    IsClosed (normApproximableOneLocus k) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro M hM
  obtain ⟨F, hF⟩ :=
    exists_cylinder_subset_compl_normApproximableOneLocus M hM
  exact mem_of_superset (cylinder_mem_nhds M F) hF

/-- The operator-MF locus in fixed-rank marked-group space. -/
def operatorMFLocus (k : ℕ) : Set (MarkedGroupSpace k) :=
  {M | IsOperatorMF M.Quotient}

theorem operatorMFLocus_eq_normApproximableOneLocus :
    operatorMFLocus k = normApproximableOneLocus k := by
  ext M
  letI : Countable M.Quotient := quotientCountable M
  exact OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one

/-- A non-MF marked group has a finite relation cylinder consisting entirely
of non-MF marked groups.  This is the explicit finite-word obstruction form
of marked-limit closure. -/
theorem exists_cylinder_subset_compl_operatorMFLocus
    (M : MarkedGroupSpace k) (hM : ¬ IsOperatorMF M.Quotient) :
    ∃ F : Finset (FreeGroup (Fin k)),
      cylinder M F ⊆ (operatorMFLocus k)ᶜ := by
  letI : Countable M.Quotient := quotientCountable M
  have hM' : ¬ IsNormApproximable M.Quotient 1 := by
    rwa [← OperatorMFLocalNormalization.isOperatorMF_iff_isNormApproximable_one]
  obtain ⟨F, hF⟩ :=
    exists_cylinder_subset_compl_normApproximableOneLocus M hM'
  refine ⟨F, ?_⟩
  rwa [operatorMFLocus_eq_normApproximableOneLocus]

/-- Strong finite-radius form: failure of MF is already forced by agreement
on one reduced-word ball. -/
theorem exists_wordBall_cylinder_subset_compl_operatorMFLocus
    (M : MarkedGroupSpace k) (hM : ¬ IsOperatorMF M.Quotient) :
    ∃ R : ℕ,
      cylinder M (wordBall k R) ⊆ (operatorMFLocus k)ᶜ := by
  obtain ⟨F, hF⟩ :=
    exists_cylinder_subset_compl_operatorMFLocus M hM
  obtain ⟨R, hFR⟩ := exists_subset_wordBall F
  exact ⟨R, (cylinder_wordBall_subset_cylinder M F R hFR).trans hF⟩

/-- **Marked-limit closure of MF.**  Operator-MF marked groups form a closed
subset of the space of `k`-marked groups. -/
theorem isClosed_operatorMFLocus : IsClosed (operatorMFLocus k) := by
  rw [operatorMFLocus_eq_normApproximableOneLocus]
  exact isClosed_normApproximableOneLocus

/-- Equivalently, non-MF marked groups form an open subset. -/
theorem isOpen_compl_operatorMFLocus : IsOpen (operatorMFLocus k)ᶜ :=
  isClosed_operatorMFLocus.isOpen_compl

/-- Filter form of marked-limit closure. -/
theorem isOperatorMF_of_tendsto
    {I : Type u} {l : Filter I} (hl : NeBot l)
    {f : I → MarkedGroupSpace k} {M : MarkedGroupSpace k}
    (hf : Tendsto f l (𝓝 M))
    (hMF : ∀ᶠ i in l, IsOperatorMF (f i).Quotient) :
    IsOperatorMF M.Quotient := by
  letI : NeBot l := hl
  exact isClosed_operatorMFLocus.mem_of_tendsto hf hMF

end MarkedGroupSpace

end

end GroupApproximation
