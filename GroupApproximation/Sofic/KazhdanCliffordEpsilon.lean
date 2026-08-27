import GroupApproximation.Sofic.KazhdanCliffordConstruction
import GroupApproximation.Algebra.PresentedGroupEvaluation

/-!
# The redundant central sign: the `ε` presentation

`GroupApproximation.Sofic.KazhdanCliffordConstruction` presents the
Kazhdan--Clifford extension on the generators of `Γ` together with a stable
letter `t` and a root involution `c`, and imposes centrality of the marked word

`w = ⁅t c t⁻¹, a (t c t⁻¹) a⁻¹⁆`

directly.  The manuscript prefers a pedagogically better presentation of the
*same* group: adjoin one further generator `ε`, declare it a central
involution, and impose

`ε = u²`,  where  `u = ⁅t c t⁻¹, a⁆`

is the pointwise compression defect at `a`.  No relator mentions the marked
word at all; centrality of the marked word becomes a *theorem*
(`markEps_central`), because `c² = 1` forces `w = u² = ε`, and `ε` is central
by fiat.

This file carries out that Tietze move formally.  `ε` is a genuine extra
generator: the raw group is the free product `RawEps Γ = Raw Γ ∗ F(ε)` and `ε`
is the image of the new free generator, not an abbreviation for a word.  The
elimination `epsTietzeEquiv` is an isomorphism onto the original extension
sending `ε` to the marked word, built from the universal property of both
presented quotients; the headline theorem `kazhdanCliffordConstructionEps` is
the transport of `kazhdanCliffordConstruction` along it.
-/

namespace GroupApproximation
namespace KazhdanCliffordEpsilon

open KazhdanCliffordConstruction

open scoped commutatorElement

noncomputable section

universe w

variable {Γ : Type} [Group Γ] [Group.IsFinitelyPresented Γ]

/-! ## The raw group with one redundant generator -/

/-- The raw group of the `ε` presentation: the raw group of the plain
presentation with one further *free* generator adjoined.  Being a free product
`(Γ ∗ F(t,c)) ∗ F(ε)`, this is the free product of the base with the free group
on the three letters `t`, `c`, `ε`; in particular `ε` is a generator and not a
word in the others. -/
abbrev RawEps (Γ : Type) [Group Γ] : Type :=
  Monoid.Coprod (Raw Γ) (FreeGroup (Fin 1))

/-- The inclusion of the plain raw group into the raw group of the `ε`
presentation. -/
noncomputable abbrev rawEpsIncl : Raw Γ →* RawEps Γ := Monoid.Coprod.inl

/-- The redundant generator `ε`, as a raw word. -/
noncomputable abbrev rawEpsSign : RawEps Γ :=
  Monoid.Coprod.inr (FreeGroup.of 0)

/-- The pointwise compression defect `u = ⁅t c t⁻¹, a⁆`, as a raw word.
Unlike the marked word it involves only one conjugate of the root
involution. -/
noncomputable def rawDefect (a : Γ) : Raw Γ :=
  ⁅(rawStable * rawLamp * rawStable⁻¹ : Raw Γ), (rawBase a : Raw Γ)⁆

/-! ## The relators of the `ε` presentation -/

/-- The stable-letter relators, transported into the `ε` raw group. -/
noncomputable def stableRelatorsEps (alpha : Γ →* Γ) : Finset (RawEps Γ) := by
  classical
  exact Finset.univ.image
    (fun i : Fin (generatorCount Γ) ↦ rawEpsIncl (stableRelator alpha i))

/-- The root-involution relators, transported into the `ε` raw group. -/
noncomputable def lampRelatorsEps : Finset (RawEps Γ) := by
  classical
  exact insert ((rawEpsIncl (rawLamp : Raw Γ) : RawEps Γ) ^ 2)
    (Finset.univ.image (fun i : Fin (generatorCount Γ) ↦
      ⁅(rawEpsIncl (rawLamp : Raw Γ) : RawEps Γ),
        (rawEpsIncl (rawBase (baseEval (Γ := Γ) (FreeGroup.of i))) :
          RawEps Γ)⁆))

/-- The relators governing the redundant sign: `ε` is an involution, `ε`
commutes with every generator, and `ε` *is* the square of the pointwise
compression defect at `a`.  There is deliberately no relator mentioning the
marked word. -/
noncomputable def epsRelators (a : Γ) : Finset (RawEps Γ) := by
  classical
  exact insert ((rawEpsSign : RawEps Γ) ^ 2)
    (insert ⁅(rawEpsSign : RawEps Γ),
        (rawEpsIncl (rawStable : Raw Γ) : RawEps Γ)⁆
      (insert ⁅(rawEpsSign : RawEps Γ),
          (rawEpsIncl (rawLamp : Raw Γ) : RawEps Γ)⁆
        (insert ((rawEpsSign : RawEps Γ)⁻¹ * rawEpsIncl (rawDefect a) ^ 2)
          (Finset.univ.image (fun i : Fin (generatorCount Γ) ↦
            ⁅(rawEpsSign : RawEps Γ),
              (rawEpsIncl (rawBase (baseEval (Γ := Γ) (FreeGroup.of i))) :
                RawEps Γ)⁆)))))

/-- The finite relator set of the `ε` presentation. -/
noncomputable def relatorsEps (alpha : Γ →* Γ) (a : Γ) : Finset (RawEps Γ) := by
  classical
  exact stableRelatorsEps alpha ∪ lampRelatorsEps ∪ epsRelators a

noncomputable def relationsEps (alpha : Γ →* Γ) (a : Γ) :
    Subgroup (RawEps Γ) :=
  Subgroup.normalClosure (relatorsEps alpha a : Set (RawEps Γ))

instance relationsEps_normal (alpha : Γ →* Γ) (a : Γ) :
    (relationsEps alpha a).Normal := Subgroup.normalClosure_normal

/-- The Kazhdan--Clifford extension in its `ε` presentation. -/
noncomputable abbrev ExtensionEps (alpha : Γ →* Γ) (a : Γ) : Type :=
  RawEps Γ ⧸ relationsEps alpha a

instance extensionEps_group (alpha : Γ →* Γ) (a : Γ) :
    Group (ExtensionEps alpha a) := inferInstance

theorem relationsEps_finitelyNormallyGenerated (alpha : Γ →* Γ) (a : Γ) :
    (relationsEps alpha a).IsFinitelyNormallyGenerated :=
  ⟨(relatorsEps alpha a : Set (RawEps Γ)), Set.toFinite _, rfl⟩

instance extensionEps_finitelyPresented (alpha : Γ →* Γ) (a : Γ) :
    Group.IsFinitelyPresented (ExtensionEps alpha a) :=
  Group.IsFinitelyPresented.quotient (relationsEps alpha a)
    (relationsEps_finitelyNormallyGenerated alpha a)

/-! ## Generators of the presented group -/

noncomputable abbrev quotientMapEps (alpha : Γ →* Γ) (a : Γ) :
    RawEps Γ →* ExtensionEps alpha a := QuotientGroup.mk' (relationsEps alpha a)

/-- Evaluation of a plain raw word in the `ε` presentation. -/
noncomputable def rawToEps (alpha : Γ →* Γ) (a : Γ) :
    Raw Γ →* ExtensionEps alpha a :=
  (quotientMapEps alpha a).comp (rawEpsIncl : Raw Γ →* RawEps Γ)

noncomputable def iotaEps (alpha : Γ →* Γ) (a : Γ) : Γ →* ExtensionEps alpha a :=
  (rawToEps alpha a).comp (Monoid.Coprod.inl : Γ →* Raw Γ)

noncomputable def stableEps (alpha : Γ →* Γ) (a : Γ) : ExtensionEps alpha a :=
  rawToEps alpha a rawStable

noncomputable def lampEps (alpha : Γ →* Γ) (a : Γ) : ExtensionEps alpha a :=
  rawToEps alpha a rawLamp

/-- **The redundant central sign.**  It is the image of the extra free
generator of `RawEps Γ`, hence a generator of the presentation in its own
right. -/
noncomputable def epsilon (alpha : Γ →* Γ) (a : Γ) : ExtensionEps alpha a :=
  quotientMapEps alpha a rawEpsSign

/-- The pointwise compression defect `u = ⁅t c t⁻¹, a⁆`. -/
noncomputable def defectEps (alpha : Γ →* Γ) (a : Γ) : ExtensionEps alpha a :=
  rawToEps alpha a (rawDefect a)

/-- The marked word of the plain presentation, read in the `ε`
presentation. -/
noncomputable def markEps (alpha : Γ →* Γ) (a : Γ) : ExtensionEps alpha a :=
  rawToEps alpha a (rawMark a)

@[simp] theorem rawToEps_rawBase (alpha : Γ →* Γ) (a g : Γ) :
    rawToEps alpha a (rawBase g) = iotaEps alpha a g := rfl

@[simp] theorem rawToEps_rawStable (alpha : Γ →* Γ) (a : Γ) :
    rawToEps alpha a rawStable = stableEps alpha a := rfl

@[simp] theorem rawToEps_rawLamp (alpha : Γ →* Γ) (a : Γ) :
    rawToEps alpha a rawLamp = lampEps alpha a := rfl

@[simp] theorem quotientMapEps_rawEpsSign (alpha : Γ →* Γ) (a : Γ) :
    quotientMapEps alpha a rawEpsSign = epsilon alpha a := rfl

theorem quotientMapEps_relator_eq_one {alpha : Γ →* Γ} {a : Γ} {r : RawEps Γ}
    (hr : r ∈ relatorsEps alpha a) : quotientMapEps alpha a r = 1 :=
  (QuotientGroup.eq_one_iff r).mpr (Subgroup.subset_normalClosure hr)

/-! ## Membership of the individual relators -/

theorem stableRelatorEps_mem (alpha : Γ →* Γ) (a : Γ)
    (i : Fin (generatorCount Γ)) :
    rawEpsIncl (stableRelator alpha i) ∈ relatorsEps alpha a := by
  classical
  refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

theorem lampSqEps_mem (alpha : Γ →* Γ) (a : Γ) :
    (rawEpsIncl (rawLamp : Raw Γ) : RawEps Γ) ^ 2 ∈ relatorsEps alpha a := by
  classical
  exact Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_insert_self _ _))

theorem lampCommEps_mem (alpha : Γ →* Γ) (a : Γ)
    (i : Fin (generatorCount Γ)) :
    ⁅(rawEpsIncl (rawLamp : Raw Γ) : RawEps Γ),
      (rawEpsIncl (rawBase (baseEval (Γ := Γ) (FreeGroup.of i))) :
        RawEps Γ)⁆ ∈ relatorsEps alpha a := by
  classical
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_insert_of_mem
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem epsSq_mem (alpha : Γ →* Γ) (a : Γ) :
    (rawEpsSign : RawEps Γ) ^ 2 ∈ relatorsEps alpha a := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_insert_self _ _)

theorem epsCommStable_mem (alpha : Γ →* Γ) (a : Γ) :
    ⁅(rawEpsSign : RawEps Γ), (rawEpsIncl (rawStable : Raw Γ) : RawEps Γ)⁆ ∈
      relatorsEps alpha a := by
  classical
  exact Finset.mem_union_right _
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))

theorem epsCommLamp_mem (alpha : Γ →* Γ) (a : Γ) :
    ⁅(rawEpsSign : RawEps Γ), (rawEpsIncl (rawLamp : Raw Γ) : RawEps Γ)⁆ ∈
      relatorsEps alpha a := by
  classical
  exact Finset.mem_union_right _
    (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))

theorem epsDefect_mem (alpha : Γ →* Γ) (a : Γ) :
    (rawEpsSign : RawEps Γ)⁻¹ * rawEpsIncl (rawDefect a) ^ 2 ∈
      relatorsEps alpha a := by
  classical
  exact Finset.mem_union_right _
    (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))))

theorem epsCommBase_mem (alpha : Γ →* Γ) (a : Γ)
    (i : Fin (generatorCount Γ)) :
    ⁅(rawEpsSign : RawEps Γ),
      (rawEpsIncl (rawBase (baseEval (Γ := Γ) (FreeGroup.of i))) :
        RawEps Γ)⁆ ∈ relatorsEps alpha a := by
  classical
  refine Finset.mem_union_right _ ?_
  refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ?_)))
  exact Finset.mem_image_of_mem _ (Finset.mem_univ i)

/-! ## Exact consequences of the relators -/

theorem stableEps_compresses_generator (alpha : Γ →* Γ) (a : Γ)
    (i : Fin (generatorCount Γ)) :
    stableEps alpha a * iotaEps alpha a (baseEval (Γ := Γ) (FreeGroup.of i)) *
        (stableEps alpha a)⁻¹ =
      iotaEps alpha a (alpha (baseEval (Γ := Γ) (FreeGroup.of i))) := by
  have h := quotientMapEps_relator_eq_one (stableRelatorEps_mem alpha a i)
  simp only [stableRelator, map_mul, map_inv] at h
  exact mul_inv_eq_one.mp h

theorem lampEps_sq (alpha : Γ →* Γ) (a : Γ) : lampEps alpha a ^ 2 = 1 := by
  have h := quotientMapEps_relator_eq_one (lampSqEps_mem alpha a)
  rw [map_pow] at h
  exact h

theorem lampEps_commutes_generator (alpha : Γ →* Γ) (a : Γ)
    (i : Fin (generatorCount Γ)) :
    Commute (lampEps alpha a)
      (iotaEps alpha a (baseEval (Γ := Γ) (FreeGroup.of i))) := by
  have h := quotientMapEps_relator_eq_one (lampCommEps_mem alpha a i)
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

theorem epsilon_sq (alpha : Γ →* Γ) (a : Γ) : epsilon alpha a ^ 2 = 1 := by
  have h := quotientMapEps_relator_eq_one (epsSq_mem alpha a)
  rw [map_pow] at h
  exact h

/-- The defining relator of the redundant generator: `ε = u²`. -/
theorem epsilon_eq_defectEps_sq (alpha : Γ →* Γ) (a : Γ) :
    epsilon alpha a = defectEps alpha a ^ 2 := by
  have h := quotientMapEps_relator_eq_one (epsDefect_mem alpha a)
  rw [map_mul, map_inv, map_pow] at h
  exact inv_mul_eq_one.mp h

theorem epsilon_commutes_stable (alpha : Γ →* Γ) (a : Γ) :
    Commute (epsilon alpha a) (stableEps alpha a) := by
  have h := quotientMapEps_relator_eq_one (epsCommStable_mem alpha a)
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

theorem epsilon_commutes_lamp (alpha : Γ →* Γ) (a : Γ) :
    Commute (epsilon alpha a) (lampEps alpha a) := by
  have h := quotientMapEps_relator_eq_one (epsCommLamp_mem alpha a)
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

theorem epsilon_commutes_base_generator (alpha : Γ →* Γ) (a : Γ)
    (i : Fin (generatorCount Γ)) :
    Commute (epsilon alpha a)
      (iotaEps alpha a (baseEval (Γ := Γ) (FreeGroup.of i))) := by
  have h := quotientMapEps_relator_eq_one (epsCommBase_mem alpha a i)
  rw [map_commutatorElement] at h
  exact commutatorElement_eq_one_iff_commute.mp h

/-- The redundant generator centralizes the whole base. -/
theorem epsilon_commutes_base (alpha : Γ →* Γ) (a g : Γ) :
    Commute (epsilon alpha a) (iotaEps alpha a g) := by
  obtain ⟨v, rfl⟩ := baseEval_surjective (Γ := Γ) g
  induction v using FreeGroup.induction_on with
  | C1 => simp
  | of i => exact epsilon_commutes_base_generator alpha a i
  | inv_of i hi => simpa using hi.inv_right
  | mul x y hx hy => simpa using hx.mul_right hy

theorem epsilon_commutes_free (alpha : Γ →* Γ) (a : Γ)
    (v : FreeGroup (Fin 2)) :
    Commute (epsilon alpha a) (rawToEps alpha a (Monoid.Coprod.inr v)) := by
  induction v using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      · exact epsilon_commutes_stable alpha a
      · exact epsilon_commutes_lamp alpha a
  | inv_of i hi => simpa using hi.inv_right
  | mul x y hx hy => simpa using hx.mul_right hy

theorem epsilon_commutes_raw (alpha : Γ →* Γ) (a : Γ) (r : Raw Γ) :
    Commute (epsilon alpha a) (rawToEps alpha a r) := by
  induction r using Monoid.Coprod.induction_on with
  | inl g => exact epsilon_commutes_base alpha a g
  | inr v => exact epsilon_commutes_free alpha a v
  | mul x y hx hy => simpa using hx.mul_right hy

theorem epsilon_commutes_sign (alpha : Γ →* Γ) (a : Γ)
    (v : FreeGroup (Fin 1)) :
    Commute (epsilon alpha a)
      (quotientMapEps alpha a (Monoid.Coprod.inr v)) := by
  induction v using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i
      exact Commute.refl _
  | inv_of i hi => simpa using hi.inv_right
  | mul x y hx hy => simpa using hx.mul_right hy

theorem epsilon_commutes_rawEps (alpha : Γ →* Γ) (a : Γ) (s : RawEps Γ) :
    Commute (epsilon alpha a) (quotientMapEps alpha a s) := by
  induction s using Monoid.Coprod.induction_on with
  | inl r => exact epsilon_commutes_raw alpha a r
  | inr v => exact epsilon_commutes_sign alpha a v
  | mul x y hx hy => simpa using hx.mul_right hy

/-- **The redundant generator is central**, by fiat: this is one of the
relators, propagated to the whole presented group. -/
theorem epsilon_central (alpha : Γ →* Γ) (a : Γ) (x : ExtensionEps alpha a) :
    Commute (epsilon alpha a) x := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (relationsEps alpha a) x
  exact epsilon_commutes_rawEps alpha a s

/-! ## The marked word is the redundant sign -/

theorem defectEps_eq (alpha : Γ →* Γ) (a : Γ) :
    defectEps alpha a =
      ⁅stableEps alpha a * lampEps alpha a * (stableEps alpha a)⁻¹,
        iotaEps alpha a a⁆ := by
  show rawToEps alpha a ⁅(rawStable * rawLamp * rawStable⁻¹ : Raw Γ),
      (rawBase a : Raw Γ)⁆ =
    ⁅rawToEps alpha a rawStable * rawToEps alpha a rawLamp *
      (rawToEps alpha a rawStable)⁻¹, rawToEps alpha a (rawBase a)⁆
  rw [map_commutatorElement, map_mul, map_mul, map_inv]

theorem markEps_eq (alpha : Γ →* Γ) (a : Γ) :
    markEps alpha a =
      markedCompressionWord (stableEps alpha a) (iotaEps alpha a a)
        (lampEps alpha a) :=
  map_markedCompressionWord (rawToEps alpha a) rawStable (rawBase a) rawLamp

theorem displacedEps_sq (alpha : Γ →* Γ) (a : Γ) :
    (stableEps alpha a * lampEps alpha a * (stableEps alpha a)⁻¹) ^ 2 = 1 := by
  have hc := lampEps_sq alpha a
  rw [pow_two] at hc
  simp only [pow_two]
  calc
    (stableEps alpha a * lampEps alpha a * (stableEps alpha a)⁻¹) *
          (stableEps alpha a * lampEps alpha a * (stableEps alpha a)⁻¹) =
        stableEps alpha a * (lampEps alpha a * lampEps alpha a) *
          (stableEps alpha a)⁻¹ := by group
    _ = 1 := by rw [hc]; group

/-- Because the root involution really is an involution, the marked word is
the square of the pointwise compression defect. -/
theorem markEps_eq_defectEps_sq (alpha : Γ →* Γ) (a : Γ) :
    markEps alpha a = defectEps alpha a ^ 2 := by
  rw [markEps_eq, defectEps_eq]
  exact commutator_conjugate_eq_commutator_sq_of_sq_eq_one
    (stableEps alpha a * lampEps alpha a * (stableEps alpha a)⁻¹)
    (iotaEps alpha a a) (displacedEps_sq alpha a)

/-- **The point of the `ε` presentation.**  No relator mentions the marked
word, yet the marked word *is* the redundant generator. -/
theorem markEps_eq_epsilon (alpha : Γ →* Γ) (a : Γ) :
    markEps alpha a = epsilon alpha a := by
  rw [markEps_eq_defectEps_sq, epsilon_eq_defectEps_sq]

/-- Centrality of the marked word is a theorem in the `ε` presentation, not a
relator. -/
theorem markEps_central (alpha : Γ →* Γ) (a : Γ) (x : ExtensionEps alpha a) :
    Commute (markEps alpha a) x := by
  rw [markEps_eq_epsilon]
  exact epsilon_central alpha a x

/-! ## Introducing the redundant generator -/

theorem relations_le_rawToEps_ker (alpha : Γ →* Γ) (a : Γ) :
    relations alpha a ≤ (rawToEps alpha a).ker := by
  classical
  apply Subgroup.normalClosure_le_normal
  intro r hr
  change r ∈ relators alpha a at hr
  simp only [relators, Finset.mem_union] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    apply MonoidHom.mem_ker.mpr
    simp only [stableRelator, map_mul, map_inv]
    exact mul_inv_eq_one.mpr (stableEps_compresses_generator alpha a i)
  · rw [lampRelators, Finset.mem_union] at hr
    rcases hr with hsquare | hcomm
    · have hr : r = rawLamp ^ 2 := Finset.mem_singleton.mp hsquare
      subst r
      apply MonoidHom.mem_ker.mpr
      rw [map_pow]
      exact lampEps_sq alpha a
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcomm
      apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr
        (lampEps_commutes_generator alpha a i)
  · simp only [centralRelators, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_image] at hr
    rcases hr with (rfl | rfl) | ⟨i, -, rfl⟩
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr
        (markEps_central alpha a (rawToEps alpha a rawStable))
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr
        (markEps_central alpha a (rawToEps alpha a rawLamp))
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr
        (markEps_central alpha a
          (rawToEps alpha a (rawBase (baseEval (Γ := Γ) (FreeGroup.of i)))))

/-- Introduction of the redundant generator: the plain presentation maps to
the `ε` presentation. -/
noncomputable def toExtensionEps (alpha : Γ →* Γ) (a : Γ) :
    Extension alpha a →* ExtensionEps alpha a :=
  QuotientGroup.lift (relations alpha a) (rawToEps alpha a)
    (relations_le_rawToEps_ker alpha a)

@[simp] theorem toExtensionEps_quotientMap (alpha : Γ →* Γ) (a : Γ)
    (r : Raw Γ) :
    toExtensionEps alpha a (quotientMap alpha a r) = rawToEps alpha a r :=
  QuotientGroup.lift_mk' _ _ r

@[simp] theorem toExtensionEps_mark (alpha : Γ →* Γ) (a : Γ) :
    toExtensionEps alpha a (mark alpha a) = epsilon alpha a := by
  rw [← quotientMap_rawMark, toExtensionEps_quotientMap]
  exact markEps_eq_epsilon alpha a

/-! ## Eliminating the redundant generator -/

/-- The raw evaluation of the `ε` presentation that sends `ε` to the marked
word. -/
noncomputable def rawEpsToExtension (alpha : Γ →* Γ) (a : Γ) :
    RawEps Γ →* Extension alpha a :=
  Monoid.Coprod.lift (quotientMap alpha a)
    (FreeGroup.lift (fun _ : Fin 1 ↦ mark alpha a))

@[simp] theorem rawEpsToExtension_incl (alpha : Γ →* Γ) (a : Γ) (r : Raw Γ) :
    rawEpsToExtension alpha a (rawEpsIncl r) = quotientMap alpha a r := rfl

@[simp] theorem rawEpsToExtension_sign (alpha : Γ →* Γ) (a : Γ) :
    rawEpsToExtension alpha a rawEpsSign = mark alpha a := by
  show Monoid.Coprod.lift (quotientMap alpha a)
      (FreeGroup.lift (fun _ : Fin 1 ↦ mark alpha a))
      (Monoid.Coprod.inr (FreeGroup.of 0)) = mark alpha a
  rw [Monoid.Coprod.lift_apply_inr, FreeGroup.lift_apply_of]

/-- In the plain presentation the marked word is also the square of the
pointwise compression defect: this is what makes the `ε` relator consistent
with the original relators. -/
theorem mark_eq_rawDefect_sq (alpha : Γ →* Γ) (a : Γ) :
    mark alpha a = quotientMap alpha a (rawDefect a) ^ 2 := by
  have hq : quotientMap alpha a (rawDefect a) =
      ⁅stable alpha a * lamp alpha a * (stable alpha a)⁻¹, iota alpha a a⁆ := by
    show quotientMap alpha a ⁅(rawStable * rawLamp * rawStable⁻¹ : Raw Γ),
        (rawBase a : Raw Γ)⁆ =
      ⁅quotientMap alpha a rawStable * quotientMap alpha a rawLamp *
        (quotientMap alpha a rawStable)⁻¹, quotientMap alpha a (rawBase a)⁆
    rw [map_commutatorElement, map_mul, map_mul, map_inv]
  rw [hq]
  exact commutator_conjugate_eq_commutator_sq_of_sq_eq_one
    (stable alpha a * lamp alpha a * (stable alpha a)⁻¹) (iota alpha a a)
    (displaced_sq alpha a)

theorem relationsEps_le_rawEpsToExtension_ker (alpha : Γ →* Γ) (a : Γ) :
    relationsEps alpha a ≤ (rawEpsToExtension alpha a).ker := by
  classical
  apply Subgroup.normalClosure_le_normal
  intro r hr
  change r ∈ relatorsEps alpha a at hr
  simp only [relatorsEps, Finset.mem_union] at hr
  rcases hr with (hr | hr) | hr
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hr
    apply MonoidHom.mem_ker.mpr
    rw [rawEpsToExtension_incl]
    exact quotientMap_relator_eq_one (by simp [relators, stableRelators])
  · rw [lampRelatorsEps, Finset.mem_insert] at hr
    rcases hr with rfl | hcomm
    · apply MonoidHom.mem_ker.mpr
      rw [map_pow, rawEpsToExtension_incl]
      exact lamp_sq alpha a
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hcomm
      apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, rawEpsToExtension_incl,
        rawEpsToExtension_incl]
      exact commutatorElement_eq_one_iff_commute.mpr
        (lamp_commutes alpha a (baseEval (Γ := Γ) (FreeGroup.of i)))
  · rw [epsRelators, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert] at hr
    rcases hr with rfl | rfl | rfl | rfl | hbase
    · apply MonoidHom.mem_ker.mpr
      rw [map_pow, rawEpsToExtension_sign]
      exact mark_sq alpha a
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, rawEpsToExtension_sign,
        rawEpsToExtension_incl]
      exact commutatorElement_eq_one_iff_commute.mpr
        (mark_commutes_stable alpha a)
    · apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, rawEpsToExtension_sign,
        rawEpsToExtension_incl]
      exact commutatorElement_eq_one_iff_commute.mpr
        (mark_commutes_lamp alpha a)
    · apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, map_pow, rawEpsToExtension_sign,
        rawEpsToExtension_incl, inv_mul_eq_one]
      exact mark_eq_rawDefect_sq alpha a
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hbase
      apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, rawEpsToExtension_sign,
        rawEpsToExtension_incl]
      exact commutatorElement_eq_one_iff_commute.mpr
        (mark_commutes_base alpha a (baseEval (Γ := Γ) (FreeGroup.of i)))

/-- Elimination of the redundant generator: `ε` is sent to the marked word. -/
noncomputable def toExtension (alpha : Γ →* Γ) (a : Γ) :
    ExtensionEps alpha a →* Extension alpha a :=
  QuotientGroup.lift (relationsEps alpha a) (rawEpsToExtension alpha a)
    (relationsEps_le_rawEpsToExtension_ker alpha a)

@[simp] theorem toExtension_quotientMapEps (alpha : Γ →* Γ) (a : Γ)
    (s : RawEps Γ) :
    toExtension alpha a (quotientMapEps alpha a s) =
      rawEpsToExtension alpha a s :=
  QuotientGroup.lift_mk' _ _ s

@[simp] theorem toExtension_epsilon (alpha : Γ →* Γ) (a : Γ) :
    toExtension alpha a (epsilon alpha a) = mark alpha a :=
  (toExtension_quotientMapEps alpha a rawEpsSign).trans
    (rawEpsToExtension_sign alpha a)

@[simp] theorem toExtension_iotaEps (alpha : Γ →* Γ) (a : Γ) (g : Γ) :
    toExtension alpha a (iotaEps alpha a g) = iota alpha a g :=
  toExtension_quotientMapEps alpha a (rawEpsIncl (rawBase g))

/-! ## The two maps are mutually inverse -/

theorem toExtension_toExtensionEps (alpha : Γ →* Γ) (a : Γ)
    (x : Extension alpha a) :
    toExtension alpha a (toExtensionEps alpha a x) = x := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (relations alpha a) x
  calc toExtension alpha a (toExtensionEps alpha a (quotientMap alpha a r))
      = toExtension alpha a (rawToEps alpha a r) := by
        rw [toExtensionEps_quotientMap]
    _ = rawEpsToExtension alpha a (rawEpsIncl r) :=
        toExtension_quotientMapEps alpha a (rawEpsIncl r)
    _ = quotientMap alpha a r := rfl

theorem toExtensionEps_toExtension_rawEps (alpha : Γ →* Γ) (a : Γ)
    (s : RawEps Γ) :
    toExtensionEps alpha a (toExtension alpha a (quotientMapEps alpha a s)) =
      quotientMapEps alpha a s := by
  induction s using Monoid.Coprod.induction_on with
  | inl r =>
      have h1 : toExtension alpha a
          (quotientMapEps alpha a (Monoid.Coprod.inl r)) =
            quotientMap alpha a r :=
        toExtension_quotientMapEps alpha a (Monoid.Coprod.inl r)
      rw [h1]
      exact toExtensionEps_quotientMap alpha a r
  | inr v =>
      refine freeGroup_hom_eq_on_generators
        (f := (toExtensionEps alpha a).comp ((toExtension alpha a).comp
          ((quotientMapEps alpha a).comp
            (Monoid.Coprod.inr : FreeGroup (Fin 1) →* RawEps Γ))))
        (g := (quotientMapEps alpha a).comp
          (Monoid.Coprod.inr : FreeGroup (Fin 1) →* RawEps Γ)) ?_ v
      intro i
      fin_cases i
      show toExtensionEps alpha a (toExtension alpha a
        (quotientMapEps alpha a (rawEpsSign : RawEps Γ))) = epsilon alpha a
      rw [quotientMapEps_rawEpsSign, toExtension_epsilon, toExtensionEps_mark]
  | mul x y hx hy => simp only [map_mul, hx, hy]

theorem toExtensionEps_toExtension (alpha : Γ →* Γ) (a : Γ)
    (y : ExtensionEps alpha a) :
    toExtensionEps alpha a (toExtension alpha a y) = y := by
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (relationsEps alpha a) y
  exact toExtensionEps_toExtension_rawEps alpha a s

theorem toExtension_injective (alpha : Γ →* Γ) (a : Γ) :
    Function.Injective (toExtension alpha a) :=
  Function.LeftInverse.injective (toExtensionEps_toExtension alpha a)

theorem toExtensionEps_injective (alpha : Γ →* Γ) (a : Γ) :
    Function.Injective (toExtensionEps alpha a) :=
  Function.LeftInverse.injective (toExtension_toExtensionEps alpha a)

/-- **The Tietze elimination of the redundant generator.**  The `ε`
presentation and the plain presentation define the same group, and the
isomorphism carries `ε` to the marked word (`epsTietzeEquiv_epsilon`). -/
noncomputable def epsTietzeEquiv (alpha : Γ →* Γ) (a : Γ) :
    ExtensionEps alpha a ≃* Extension alpha a where
  toFun := toExtension alpha a
  invFun := toExtensionEps alpha a
  left_inv := toExtensionEps_toExtension alpha a
  right_inv := toExtension_toExtensionEps alpha a
  map_mul' := map_mul (toExtension alpha a)

@[simp] theorem epsTietzeEquiv_apply (alpha : Γ →* Γ) (a : Γ)
    (y : ExtensionEps alpha a) :
    epsTietzeEquiv alpha a y = toExtension alpha a y := rfl

@[simp] theorem epsTietzeEquiv_symm_apply (alpha : Γ →* Γ) (a : Γ)
    (x : Extension alpha a) :
    (epsTietzeEquiv alpha a).symm x = toExtensionEps alpha a x := rfl

theorem epsTietzeEquiv_epsilon (alpha : Γ →* Γ) (a : Γ) :
    epsTietzeEquiv alpha a (epsilon alpha a) = mark alpha a :=
  toExtension_epsilon alpha a

theorem epsTietzeEquiv_symm_mark (alpha : Γ →* Γ) (a : Γ) :
    (epsTietzeEquiv alpha a).symm (mark alpha a) = epsilon alpha a :=
  toExtensionEps_mark alpha a

theorem iotaEps_injective (alpha : Γ →* Γ) (hAlpha : Function.Injective alpha)
    (a : Γ) (ha : a ∉ Set.range alpha) :
    Function.Injective (iotaEps alpha a) := by
  intro x y hxy
  apply iota_injective alpha hAlpha a ha
  rw [← toExtension_iotaEps alpha a x, ← toExtension_iotaEps alpha a y, hxy]

instance extensionEps_countable (alpha : Γ →* Γ) (a : Γ) :
    Countable (ExtensionEps alpha a) :=
  (toExtension_injective alpha a).countable

/-! ## The headline theorem in the `ε` presentation -/

/-- The `ε` form of the Kazhdan--Clifford construction as one closed
proposition.  As in the plain form, all construction data and hypotheses are
quantified inside the proposition, so the advertised theorem itself has no
declaration inputs. -/
def KazhdanCliffordEpsConstructionStatement : Prop :=
  ∀ {Γ₀ : Type} [Group Γ₀] [Group.IsFinitelyPresented Γ₀]
    (alpha : Γ₀ →* Γ₀) (hAlpha : Function.Injective alpha) (a : Γ₀)
    (hTTextbook : HasKazhdanPropertyTComplex.{0, w} Γ₀)
    (ha : a ∉ Set.range alpha),
    Group.IsFinitelyPresented (ExtensionEps alpha a) ∧
      Function.Injective (iotaEps alpha a) ∧
      epsilon alpha a ≠ 1 ∧
      epsilon alpha a ^ 2 = 1 ∧
      (∀ g : ExtensionEps alpha a, Commute (epsilon alpha a) g) ∧
      (∀ (d : ℕ → ℕ) (hd : ∀ n, 0 < d n),
        letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
          fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
        ∀ rho : ExtensionEps alpha a →* unitary (NormMatrixCStarCorona
            (fun n ↦ naturalFiniteModel (d n))),
          rho (epsilon alpha a) = 1) ∧
      ¬ IsCDEOperatorMF (ExtensionEps alpha a)

/-- **Kazhdan--Clifford construction, `ε` presentation (formal headline
theorem).**  The redundant central sign is a genuine extra generator of the
presentation: it is declared to be a central involution and to be the square
of the pointwise compression defect, and nothing whatever is imposed on the
marked word.  The group so presented is the group of the plain construction,
and `ε` inherits every property of the marked word -- nontrivial, of order
two, central, and killed by every norm-matrix-corona representation. -/
theorem kazhdanCliffordConstructionEps :
    KazhdanCliffordEpsConstructionStatement := by
  intro Γ₀ _ _ alpha hAlpha a hTTextbook ha
  obtain ⟨-, -, hne, -, -, hcorona, hMF⟩ :=
    kazhdanCliffordConstruction alpha hAlpha a hTTextbook ha
  refine ⟨inferInstance, iotaEps_injective alpha hAlpha a ha, ?_,
    epsilon_sq alpha a, epsilon_central alpha a, ?_, ?_⟩
  · intro h
    apply hne
    rw [← toExtension_epsilon alpha a, h, map_one]
  · intro d hd
    letI : ∀ n, Nonempty (naturalFiniteModel (d n)) :=
      fun n ↦ Fintype.card_pos_iff.mp (by simpa using hd n)
    intro rho
    have h := hcorona d hd (rho.comp (toExtensionEps alpha a))
    rw [MonoidHom.comp_apply, toExtensionEps_mark] at h
    exact h
  · intro hEps
    apply hMF
    obtain ⟨d, hd, hmono, rho, hrho⟩ := hEps
    refine ⟨d, hd, hmono, rho.comp (toExtensionEps alpha a), ?_⟩
    intro x y hxy
    exact toExtensionEps_injective alpha a (hrho hxy)

end

end KazhdanCliffordEpsilon
end GroupApproximation
