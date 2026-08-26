import GroupApproximation.Sofic.MarkedGroupWordBall
import GroupApproximation.Sofic.OperatorMFLocalNormalization
import Mathlib.GroupTheory.FinitelyPresentedGroup

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
theorem exists_wordBall_cylinder_subset_compl_operatorMFLocus :
    ∀ {k : ℕ} (M : MarkedGroupSpace k) (_hM : ¬ IsOperatorMF M.Quotient),
      ∃ R : ℕ,
        cylinder M (wordBall k R) ⊆ (operatorMFLocus k)ᶜ := by
  intro k M hM
  obtain ⟨F, hF⟩ :=
    exists_cylinder_subset_compl_operatorMFLocus M hM
  obtain ⟨R, hFR⟩ := exists_subset_wordBall F
  exact ⟨R, (cylinder_wordBall_subset_cylinder M F R hFR).trans hF⟩

/-- **Marked-limit closure of MF.**  Operator-MF marked groups form a closed
subset of the space of `k`-marked groups.

The rank is quantified inside the proposition rather than inherited from the
section `variable`: this is a cited manuscript endpoint, and its printed
header is what a reader is invited to check it against. -/
theorem isClosed_operatorMFLocus :
    ∀ {k : ℕ}, IsClosed (operatorMFLocus k) := by
  intro k
  rw [operatorMFLocus_eq_normApproximableOneLocus]
  exact isClosed_normApproximableOneLocus

/-- Equivalently, non-MF marked groups form an open subset. -/
theorem isOpen_compl_operatorMFLocus :
    ∀ {k : ℕ}, IsOpen (operatorMFLocus k)ᶜ := by
  intro k
  exact (isClosed_operatorMFLocus (k := k)).isOpen_compl

/-- Filter form of marked-limit closure. -/
theorem isOperatorMF_of_tendsto
    {I : Type u} {l : Filter I} (hl : NeBot l)
    {f : I → MarkedGroupSpace k} {M : MarkedGroupSpace k}
    (hf : Tendsto f l (𝓝 M))
    (hMF : ∀ᶠ i in l, IsOperatorMF (f i).Quotient) :
    IsOperatorMF M.Quotient := by
  letI : NeBot l := hl
  exact (isClosed_operatorMFLocus (k := k)).mem_of_tendsto hf hMF

/-- Every finitely generated non-operator-MF group is a quotient of a
finitely presented non-operator-MF group.

The group is presented on the same finite marking.  Starting from a finite
cylinder contained in the non-MF locus, retain exactly the relations from
that cylinder which hold in the original group and take their normal
closure.  The resulting finite presentation still lies in the cylinder, and
its relation subgroup is contained in the original relation subgroup, which
gives the displayed quotient map. -/
theorem exists_finitelyPresented_nonMF_cover
    (M : MarkedGroupSpace k) (hM : ¬ IsOperatorMF M.Quotient) :
    ∃ N : MarkedGroupSpace k,
      Group.IsFinitelyPresented N.Quotient ∧
        ¬ IsOperatorMF N.Quotient ∧
        ∃ q : N.Quotient →* M.Quotient, Function.Surjective q := by
  classical
  obtain ⟨F, hF⟩ := exists_cylinder_subset_compl_operatorMFLocus M hM
  let R : Finset (FreeGroup (Fin k)) := F.filter fun w ↦ w ∈ M.relations
  let N : MarkedGroupSpace k :=
    { relations := Subgroup.normalClosure (R : Set (FreeGroup (Fin k)))
      normal_relations := Subgroup.normalClosure_normal }
  have hrelations : N.relations ≤ M.relations := by
    apply Subgroup.normalClosure_le_normal
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hNcylinder : N ∈ cylinder M F := by
    rw [mem_cylinder_iff]
    intro w hwF
    constructor
    · exact fun hwN ↦ hrelations hwN
    · intro hwM
      apply Subgroup.subset_normalClosure
      exact Finset.mem_filter.mpr ⟨hwF, hwM⟩
  have hNnonMF : ¬ IsOperatorMF N.Quotient := by
    have houtside := hF hNcylinder
    change ¬ IsOperatorMF N.Quotient at houtside
    exact houtside
  haveI : Finite (R : Set (FreeGroup (Fin k))) := R.finite_toSet.to_subtype
  have hNfp : Group.IsFinitelyPresented N.Quotient := by
    change Group.IsFinitelyPresented
      (PresentedGroup (R : Set (FreeGroup (Fin k))))
    infer_instance
  have hker : N.relations ≤ (QuotientGroup.mk' M.relations).ker := by
    intro w hw
    exact MonoidHom.mem_ker.mpr
      ((QuotientGroup.eq_one_iff w).mpr (hrelations hw))
  let q : N.Quotient →* M.Quotient :=
    QuotientGroup.lift N.relations (QuotientGroup.mk' M.relations) hker
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective M.relations y
    refine ⟨QuotientGroup.mk' N.relations w, ?_⟩
    exact QuotientGroup.lift_mk' N.relations hker w
  exact ⟨N, hNfp, hNnonMF, q, hq⟩

/-- Every finitely generated non-operator-MF group is a quotient of a finitely
presented non-operator-MF group.

This is the unmarked form of `exists_finitelyPresented_nonMF_cover`.  A finite
generating set supplies a marking, the quotient by the kernel of the resulting
free-group evaluation is identified with the original group, and the marked
cover is then transported across that identification. -/
theorem exists_finitelyPresented_nonMF_cover_of_fg
    (G : Type) [Group G] [Group.FG G] (hG : ¬ IsOperatorMF G) :
    ∃ (H : Type) (_ : Group H),
      Group.IsFinitelyPresented H ∧
        ¬ IsOperatorMF H ∧
        ∃ q : H →* G, Function.Surjective q := by
  classical
  obtain ⟨S, hS, hSfinite⟩ :=
    Group.fg_iff.mp (inferInstance : Group.FG G)
  letI : Finite S := hSfinite.to_subtype
  letI : Fintype S := Fintype.ofFinite S
  let k := Fintype.card S
  let eS : Fin k ≃ S := (Fintype.equivFin S).symm
  let gen : Fin k → G := fun i ↦ eS i
  have hrange : Set.range gen = S := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (eS i).property
    · intro hg
      let s : S := ⟨g, hg⟩
      refine ⟨eS.symm s, ?_⟩
      exact congrArg Subtype.val (eS.apply_symm_apply s)
  let π : FreeGroup (Fin k) →* G := FreeGroup.lift gen
  have hrangeπ : π.range = Subgroup.closure (Set.range gen) := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨w, rfl⟩
      induction w using FreeGroup.induction_on with
      | C1 => simp
      | of i =>
          simpa [π, FreeGroup.lift_apply_of] using
            Subgroup.subset_closure (Set.mem_range_self i : gen i ∈ Set.range gen)
      | inv_of i _ =>
          simpa [π, FreeGroup.lift_apply_of] using
            Subgroup.inv_mem _
              (Subgroup.subset_closure
                (Set.mem_range_self i : gen i ∈ Set.range gen))
      | mul _ _ hw hv => simpa using Subgroup.mul_mem _ hw hv
    · refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨FreeGroup.of i, by simp [π, FreeGroup.lift_apply_of]⟩
  have hπ : Function.Surjective π := by
    rw [← MonoidHom.range_eq_top, hrangeπ, hrange, hS]
  let M : MarkedGroupSpace k :=
    { relations := π.ker
      normal_relations := MonoidHom.normal_ker π }
  let e : M.Quotient ≃* G :=
    QuotientGroup.quotientKerEquivOfSurjective π hπ
  have hM : ¬ IsOperatorMF M.Quotient := by
    intro hMF
    exact hG (hMF.comap e.symm.toMonoidHom e.symm.injective)
  obtain ⟨N, hNfp, hNnonMF, q, hq⟩ :=
    exists_finitelyPresented_nonMF_cover M hM
  exact ⟨N.Quotient, inferInstance, hNfp, hNnonMF,
    e.toMonoidHom.comp q, e.surjective.comp hq⟩

end MarkedGroupSpace

end

end GroupApproximation
