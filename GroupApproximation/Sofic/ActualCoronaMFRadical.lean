import GroupApproximation.Sofic.CDEOperatorMF
import GroupApproximation.Sofic.NormMFResidualExactQuotient
import GroupApproximation.Algebra.CountableInstances

/-!
# The actual C-star-corona MF radical

The manuscript defines its radical by intersecting the kernels of all
homomorphisms into unitary groups of genuine norm-matrix C-star coronas.  This
file gives that definition literally, for every positive sequence of finite
matrix coordinates.  Polar correction identifies it with the internal
unitary-sequence radical used by the analytic proof.
-/

namespace GroupApproximation

noncomputable section

universe u v

variable {G : Type u} [Group G]

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-- An element is invisible in every genuine norm-matrix C-star corona with
positive finite matrix coordinates. -/
def ActualCoronaMFInvisible (x : G) : Prop :=
  ∀ (X : ℕ → FiniteModel), ∀ hX : ∀ n, 0 < Fintype.card (X n),
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)), rho x = 1

/-- The literal intersection of the kernels of all genuine norm-matrix
C-star-corona representations. -/
def actualCoronaMFResidual (G : Type u) [Group G] : Subgroup G where
  carrier := {x | ActualCoronaMFInvisible x}
  one_mem' := by
    intro X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho
    exact map_one (f := rho)
  mul_mem' := by
    intro x y hx hy X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho
    rw [map_mul, hx X hX rho, hy X hX rho, one_mul]
  inv_mem' := by
    intro x hx X hX
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    intro rho
    rw [map_inv, hx X hX rho, inv_one]

@[simp] theorem mem_actualCoronaMFResidual_iff {x : G} :
    x ∈ actualCoronaMFResidual G ↔ ActualCoronaMFInvisible x :=
  Iff.rfl

/-- The manuscript's literal natural-dimension invisibility predicate. -/
def ManuscriptCoronaMFInvisible (x : G) : Prop :=
  ∀ (d : ℕ → ℕ), ∀ hd : ∀ n, 0 < d n,
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    ∀ rho : G →* unitary (NormMatrixCStarCorona
      (fun n ↦ naturalFiniteModel (d n))), rho x = 1

/-- The MF radical exactly as printed: intersect the kernels of all genuine
norm-matrix C-star-corona representations with coordinates `M_(d_n)(ℂ)`. -/
def manuscriptCoronaMFResidual (G : Type u) [Group G] : Subgroup G where
  carrier := {x | ManuscriptCoronaMFInvisible x}
  one_mem' := by
    intro d hd
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    intro rho
    exact map_one (f := rho)
  mul_mem' := by
    intro x y hx hy d hd
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    intro rho
    rw [map_mul, hx d hd rho, hy d hd rho, one_mul]
  inv_mem' := by
    intro x hx d hd
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    intro rho
    rw [map_inv, hx d hd rho, inv_one]

@[simp] theorem mem_manuscriptCoronaMFResidual_iff {x : G} :
    x ∈ manuscriptCoronaMFResidual G ↔ ManuscriptCoronaMFInvisible x :=
  Iff.rfl

/-- Genuine-C-star-corona invisibility and unitary-sequence-corona
invisibility are exactly equivalent, coordinate sequence by coordinate
sequence. -/
theorem actualCoronaMFInvisible_iff_coronaMFInvisible {x : G} :
    ActualCoronaMFInvisible x ↔ CoronaMFInvisible x := by
  constructor
  · intro hx X hX rho
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    let rhoActual : G →*
        unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
      (normMatrixCoronaUnitaryEquiv X).toMonoidHom.comp rho
    have h := hx X hX rhoActual
    apply (normMatrixCoronaUnitaryEquiv X).injective
    simpa [rhoActual] using h
  · intro hx X hX rho
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    let rhoSequence : G →* NormMatrixCoronaUnitary X :=
      (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho
    have h := hx X hX rhoSequence
    apply (normMatrixCoronaUnitaryEquiv X).symm.injective
    simpa [rhoSequence] using h

/-- Quantifying over arbitrary finite coordinate sets or literally over
natural matrix dimensions gives the same genuine-C-star-corona invisibility
predicate. -/
theorem manuscriptCoronaMFInvisible_iff_actualCoronaMFInvisible {x : G} :
    ManuscriptCoronaMFInvisible x ↔ ActualCoronaMFInvisible x := by
  constructor
  · intro hx X hX rho
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    let rhoNatural : G →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalizedModel X n)) :=
      (actualCoronaNaturalizeEquiv X).toMonoidHom.comp rho
    have hnat := hx (fun n ↦ Fintype.card (X n)) hX rhoNatural
    apply (actualCoronaNaturalizeEquiv X).injective
    simpa [rhoNatural] using hnat
  · intro hx d hd rho
    exact hx (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd) rho

/-- The public natural-dimension radical and the basis-free actual-corona
radical are propositionally equal. -/
theorem manuscriptCoronaMFResidual_eq_actualCoronaMFResidual :
    manuscriptCoronaMFResidual G = actualCoronaMFResidual G := by
  ext x
  exact manuscriptCoronaMFInvisible_iff_actualCoronaMFInvisible

/-- The literal genuine-C-star-corona radical equals the internal
unitary-sequence radical. -/
theorem actualCoronaMFResidual_eq_coronaMFResidual :
    actualCoronaMFResidual G = coronaMFResidual G := by
  ext x
  exact actualCoronaMFInvisible_iff_coronaMFInvisible

/-- The literal public radical equals the internal unitary-sequence
radical. -/
theorem manuscriptCoronaMFResidual_eq_coronaMFResidual :
    manuscriptCoronaMFResidual G = coronaMFResidual G := by
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual,
    actualCoronaMFResidual_eq_coronaMFResidual]

instance actualCoronaMFResidual_normal : (actualCoronaMFResidual G).Normal := by
  rw [actualCoronaMFResidual_eq_coronaMFResidual]
  infer_instance

instance manuscriptCoronaMFResidual_normal :
    (manuscriptCoronaMFResidual G).Normal := by
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  infer_instance

/-- The literal genuine-corona radical is functorial under arbitrary group
homomorphisms. -/
theorem map_actualCoronaMFResidual_le
    {H : Type v} [Group H] (f : G →* H) :
    (actualCoronaMFResidual G).map f ≤ actualCoronaMFResidual H := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  intro X hX
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  exact hx X hX (rho.comp f)

/-- Functoriality of the radical in the manuscript's literal
natural-dimension presentation. -/
theorem map_manuscriptCoronaMFResidual_le
    {H : Type v} [Group H] (f : G →* H) :
    (manuscriptCoronaMFResidual G).map f ≤ manuscriptCoronaMFResidual H := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  intro d hd
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  intro rho
  exact hx d hd (rho.comp f)

/-- The quotient by the literal genuine-corona radical is CDE-MF. -/
theorem actualCoronaMFQuotient_isCDEOperatorMF [Countable G] :
    IsCDEOperatorMF (G ⧸ actualCoronaMFResidual G) := by
  let e : (G ⧸ actualCoronaMFResidual G) ≃*
      (G ⧸ coronaMFResidual G) :=
    QuotientGroup.quotientMulEquivOfEq
      actualCoronaMFResidual_eq_coronaMFResidual
  obtain ⟨X, hX, rho, hrho⟩ := coronaMFQuotient_isOperatorMF (G := G)
  have hop : IsOperatorMF (G ⧸ actualCoronaMFResidual G) :=
    ⟨X, hX, rho.comp e.toMonoidHom, hrho.comp e.injective⟩
  exact (isCDEOperatorMF_iff_isOperatorMF _).2 hop

/-- The quotient by the manuscript's literal natural-dimension radical is
CDE-MF. -/
theorem manuscriptCoronaMFQuotient_isCDEOperatorMF [Countable G] :
    IsCDEOperatorMF (G ⧸ manuscriptCoronaMFResidual G) := by
  let e : (G ⧸ manuscriptCoronaMFResidual G) ≃*
      (G ⧸ actualCoronaMFResidual G) :=
    QuotientGroup.quotientMulEquivOfEq
      manuscriptCoronaMFResidual_eq_actualCoronaMFResidual
  obtain ⟨d, hd, hmono, rho, hrho⟩ :=
    actualCoronaMFQuotient_isCDEOperatorMF (G := G)
  exact ⟨d, hd, hmono, rho.comp e.toMonoidHom,
    hrho.comp e.injective⟩

/-- A countable group is CDE-MF exactly when its literal genuine-corona
radical is trivial. -/
theorem isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot [Countable G] :
    IsCDEOperatorMF G ↔ actualCoronaMFResidual G = ⊥ := by
  rw [actualCoronaMFResidual_eq_coronaMFResidual,
    isCDEOperatorMF_iff_isOperatorMF]
  exact isOperatorMF_iff_coronaMFResidual_eq_bot

/-- Literal natural-dimension radical criterion for CDE-MF. -/
theorem isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot [Countable G] :
    IsCDEOperatorMF G ↔ manuscriptCoronaMFResidual G = ⊥ := by
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual]
  exact isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot

/-- The literal radical is the kernel of one representation into one genuine
norm-matrix C-star corona. -/
theorem exists_actualCoronaRepresentation_ker_eq_actualCoronaMFResidual
    [Countable G] :
    ∃ (X : ℕ → FiniteModel), ∃ hX : ∀ n, 0 < Fintype.card (X n),
      letI : ∀ n, Nonempty (X n) :=
        fun n ↦ Fintype.card_pos_iff.mp (hX n)
      ∃ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
        rho.ker = actualCoronaMFResidual G := by
  obtain ⟨X, hX, rho, hker⟩ :=
    exists_normMatrixCoronaRepresentation_ker_eq_coronaMFResidual (G := G)
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  let rhoActual : G →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    (normMatrixCoronaUnitaryEquiv X).toMonoidHom.comp rho
  refine ⟨X, hX, rhoActual, ?_⟩
  ext x
  change rhoActual x = 1 ↔ x ∈ actualCoronaMFResidual G
  rw [actualCoronaMFResidual_eq_coronaMFResidual, ← hker]
  change rhoActual x = 1 ↔ rho x = 1
  constructor
  · intro h
    apply (normMatrixCoronaUnitaryEquiv X).injective
    simpa [rhoActual] using h
  · intro h
    simp [rhoActual, h]

/-- The manuscript's literal radical is the kernel of one representation in
one genuine natural-dimension norm-matrix C-star corona. -/
theorem exists_manuscriptCoronaRepresentation_ker_eq_manuscriptCoronaMFResidual
    [Countable G] :
    ∃ (d : ℕ → ℕ), ∃ hd : ∀ n, 0 < d n,
      letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
        fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
      ∃ rho : G →* unitary (NormMatrixCStarCorona
          (fun n ↦ naturalFiniteModel (d n))),
        rho.ker = manuscriptCoronaMFResidual G := by
  obtain ⟨X, hX, rho, hker⟩ :=
    exists_actualCoronaRepresentation_ker_eq_actualCoronaMFResidual (G := G)
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  let rhoNatural : G →* unitary (NormMatrixCStarCorona
      (fun n ↦ naturalizedModel X n)) :=
    (actualCoronaNaturalizeEquiv X).toMonoidHom.comp rho
  refine ⟨fun n ↦ Fintype.card (X n), hX, rhoNatural, ?_⟩
  ext x
  change rhoNatural x = 1 ↔ x ∈ manuscriptCoronaMFResidual G
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual, ← hker]
  change rhoNatural x = 1 ↔ rho x = 1
  constructor
  · intro h
    apply (actualCoronaNaturalizeEquiv X).injective
    simpa [rhoNatural] using h
  · intro h
    simp [rhoNatural, h]

/-- Every map to a countable CDE-MF group factors uniquely through the
universal literal MF quotient. -/
theorem existsUnique_actualCoronaMFQuotient_factorization_to_isCDEOperatorMF
    {H : Type v} [Group H] [Countable H]
    (f : G →* H) (hH : IsCDEOperatorMF H) :
    ∃! fBar : (G ⧸ actualCoronaMFResidual G) →* H,
      fBar.comp (QuotientGroup.mk' (actualCoronaMFResidual G)) = f := by
  have hker : actualCoronaMFResidual G ≤ f.ker := by
    intro x hx
    have hfx : f x ∈ actualCoronaMFResidual H :=
      map_actualCoronaMFResidual_le f ⟨x, hx, rfl⟩
    have hbot : actualCoronaMFResidual H = ⊥ :=
      isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hH
    rw [hbot] at hfx
    exact Subgroup.mem_bot.mp hfx
  let fBar : (G ⧸ actualCoronaMFResidual G) →* H :=
    QuotientGroup.lift (actualCoronaMFResidual G) f hker
  have hcomp :
      fBar.comp (QuotientGroup.mk' (actualCoronaMFResidual G)) = f :=
    QuotientGroup.lift_comp_mk' (actualCoronaMFResidual G) f hker
  refine ⟨fBar, hcomp, ?_⟩
  intro candidate hc
  apply MonoidHom.ext
  intro q
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (actualCoronaMFResidual G) q
  exact DFunLike.congr_fun (hc.trans hcomp.symm) g

/-- Literal natural-dimension universal-quotient factorization. -/
theorem existsUnique_manuscriptCoronaMFQuotient_factorization_to_isCDEOperatorMF
    {H : Type v} [Group H] [Countable H]
    (f : G →* H) (hH : IsCDEOperatorMF H) :
    ∃! fBar : (G ⧸ manuscriptCoronaMFResidual G) →* H,
      fBar.comp (QuotientGroup.mk' (manuscriptCoronaMFResidual G)) = f := by
  have hker : manuscriptCoronaMFResidual G ≤ f.ker := by
    intro x hx
    have hfx : f x ∈ manuscriptCoronaMFResidual H :=
      map_manuscriptCoronaMFResidual_le f ⟨x, hx, rfl⟩
    have hbot : manuscriptCoronaMFResidual H = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp hH
    rw [hbot] at hfx
    exact Subgroup.mem_bot.mp hfx
  let fBar : (G ⧸ manuscriptCoronaMFResidual G) →* H :=
    QuotientGroup.lift (manuscriptCoronaMFResidual G) f hker
  have hcomp :
      fBar.comp (QuotientGroup.mk' (manuscriptCoronaMFResidual G)) = f :=
    QuotientGroup.lift_comp_mk' (manuscriptCoronaMFResidual G) f hker
  refine ⟨fBar, hcomp, ?_⟩
  intro candidate hc
  apply MonoidHom.ext
  intro q
  obtain ⟨g, rfl⟩ :=
    QuotientGroup.mk'_surjective (manuscriptCoronaMFResidual G) q
  exact DFunLike.congr_fun (hc.trans hcomp.symm) g

/-- Every genuine-corona representation factors uniquely through a normal
subgroup contained in the literal radical. -/
theorem existsUnique_quotient_factorization_to_actualCorona
    (N : Subgroup G) [N.Normal] (hN : N ≤ actualCoronaMFResidual G)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n)) :
    letI : ∀ n, Nonempty (X n) :=
      fun n ↦ Fintype.card_pos_iff.mp (hX n)
    ∀ rho : G →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
    ∃! rhoBar : (G ⧸ N) →*
        unitary (NormMatrixCStarCorona (fun n ↦ X n)),
      rhoBar.comp (QuotientGroup.mk' N) = rho := by
  letI : ∀ n, Nonempty (X n) :=
    fun n ↦ Fintype.card_pos_iff.mp (hX n)
  intro rho
  have hker : N ≤ rho.ker := by
    intro x hx
    exact hN hx X hX rho
  let rhoBar : (G ⧸ N) →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n)) :=
    QuotientGroup.lift N rho hker
  have hcomp : rhoBar.comp (QuotientGroup.mk' N) = rho :=
    QuotientGroup.lift_comp_mk' N rho hker
  refine ⟨rhoBar, hcomp, ?_⟩
  intro candidate hc
  apply MonoidHom.ext
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
  exact DFunLike.congr_fun (hc.trans hcomp.symm) g

/-- Every literal natural-dimension corona representation factors uniquely
through a normal subgroup contained in the manuscript radical. -/
theorem existsUnique_quotient_factorization_to_manuscriptCorona
    (N : Subgroup G) [N.Normal] (hN : N ≤ manuscriptCoronaMFResidual G)
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    ∀ rho : G →* unitary (NormMatrixCStarCorona
      (fun n ↦ naturalFiniteModel (d n))),
    ∃! rhoBar : (G ⧸ N) →* unitary (NormMatrixCStarCorona
        (fun n ↦ naturalFiniteModel (d n))),
      rhoBar.comp (QuotientGroup.mk' N) = rho := by
  letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
    fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
  intro rho
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual] at hN
  exact existsUnique_quotient_factorization_to_actualCorona
    N hN (fun n ↦ naturalFiniteModel (d n)) (by simpa using hd) rho

/-- A normal subgroup contained in the literal radical is the entire radical
as soon as its quotient is CDE-MF. -/
theorem actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF
    [Countable G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ actualCoronaMFResidual G)
    (hquot : IsCDEOperatorMF (G ⧸ N)) :
    actualCoronaMFResidual G = N := by
  rw [actualCoronaMFResidual_eq_coronaMFResidual] at hN ⊢
  exact coronaMFResidual_eq_of_le_and_quotient_isOperatorMF N hN
    ((isCDEOperatorMF_iff_isOperatorMF _).1 hquot)

/-- Exact candidate-radical criterion in the manuscript's literal
natural-dimension presentation. -/
theorem manuscriptCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF
    [Countable G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ manuscriptCoronaMFResidual G)
    (hquot : IsCDEOperatorMF (G ⧸ N)) :
    manuscriptCoronaMFResidual G = N := by
  rw [manuscriptCoronaMFResidual_eq_actualCoronaMFResidual] at hN ⊢
  exact actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF
    N hN hquot

end

end GroupApproximation
