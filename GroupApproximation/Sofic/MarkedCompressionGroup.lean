import GroupApproximation.Algebra.MappingTelescope
import GroupApproximation.Sofic.CliffordLampGroup
import GroupApproximation.Sofic.ExplicitNonMFBase
import GroupApproximation.Sofic.NormMFResidualDetector
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The marked-compression witness group

From an injective endomorphism `α : Γ →* Γ` this file assembles the group
carrying the marked compression word:

* `Vertical`: the mapping telescope of `α` extended by the shift — the
  standard model of the ascending HNN extension `⟨Γ, t ∣ tγt⁻¹ = α(γ)⟩`,
  with no normal-form theory: the one non-membership needed downstream is the
  telescope range characterisation.
* `Cosets`: the left coset space of the level-zero copy of `Γ`, a
  `Vertical`-set.
* `Ambient`: the Clifford lamp group over `Cosets`, extended by `Vertical`
  acting through coset permutations.

Inside `Ambient` the distinguished elements `tAmbient`, `cAmbient` and the
image of any `a₀ ∉ range α` satisfy exactly the marked-compression
relations: `compress`, `comm_c`, `word_sq`, `word_central`, and — because
the two relevant cosets are distinct — `marked_word_eq_sign` with
`word_ne_one`.  The final section instantiates everything with the
repository's internal Kazhdan base `ExplicitNonMFBase`.
-/

namespace GroupApproximation
namespace MarkedCompression

open MappingTelescope CliffordLamp SemidirectProduct

universe u

variable {Γ : Type u} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-! ## The vertical group: telescope ⋊ shift -/

/-- The integer powers of the telescope shift. -/
def shiftHom : Multiplicative ℤ →* MulAut (Telescope α hα) :=
  MonoidHom.mk'
    (fun k => (shift α hα : MulAut (Telescope α hα)) ^ k.toAdd)
    (fun a b => by rw [toAdd_mul, zpow_add])

@[simp] theorem shiftHom_ofAdd_one :
    shiftHom α hα (Multiplicative.ofAdd 1) =
      (shift α hα : MulAut (Telescope α hα)) := by
  show (shift α hα : MulAut (Telescope α hα)) ^
    (Multiplicative.ofAdd (1 : ℤ)).toAdd = _
  rfl

/-- The ascending-HNN model: telescope extended by the shift. -/
abbrev Vertical : Type u :=
  (Telescope α hα) ⋊[shiftHom α hα] Multiplicative ℤ

instance : Group (Vertical α hα) :=
  inferInstanceAs (Group ((Telescope α hα) ⋊[shiftHom α hα] Multiplicative ℤ))

/-- The copy of `Γ` at telescope level zero. -/
def iotaVertical : Γ →* Vertical α hα :=
  (inl : Telescope α hα →* Vertical α hα).comp (level α hα 0)

/-- The stable letter. -/
def tVertical : Vertical α hα := inr (Multiplicative.ofAdd 1)

theorem iotaVertical_injective : Function.Injective (iotaVertical α hα) :=
  inl_injective.comp (level_injective α hα 0)

/-- The ascending-HNN conjugation relation, realised. -/
theorem vertical_compress (γ : Γ) :
    tVertical α hα * iotaVertical α hα γ * (tVertical α hα)⁻¹ =
      iotaVertical α hα (α γ) := by
  show inr (Multiplicative.ofAdd 1) * inl (level α hα 0 γ) *
      (inr (Multiplicative.ofAdd 1))⁻¹ = inl (level α hα 0 (α γ))
  rw [← map_inv, ← inl_aut, shiftHom_ofAdd_one]
  exact congrArg _ (shift_level α hα 0 γ)

/-- Conjugating an element of the base copy by the *inverse* stable letter
moves it one telescope level up. -/
theorem tVertical_inv_conj (x : Γ) :
    (tVertical α hα)⁻¹ * iotaVertical α hα x * tVertical α hα =
      inl (level α hα 1 x) := by
  show (inr (Multiplicative.ofAdd 1))⁻¹ * inl (level α hα 0 x) *
      inr (Multiplicative.ofAdd 1) = inl (level α hα 1 x)
  rw [← map_inv, ← inl_aut_inv, shiftHom_ofAdd_one]
  exact congrArg _ (shift_symm_apply_mk α hα 0 x)

include hα in
/-- The moved copy escapes the base copy exactly off the range of `α`. -/
theorem tVertical_inv_conj_not_mem {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    (tVertical α hα)⁻¹ * iotaVertical α hα a₀ * tVertical α hα ∉
      (iotaVertical α hα).range := by
  rw [tVertical_inv_conj]
  rintro ⟨γ, hγ⟩
  have hlevel : level α hα 0 γ = level α hα 1 a₀ := inl_injective hγ
  have hmem : level α hα (0 + 1) a₀ ∈ (level α hα 0).range := ⟨γ, hlevel⟩
  obtain ⟨y, hy⟩ := (level_succ_mem_range_level_iff α hα 0 a₀).mp hmem
  exact ha₀ ⟨y, hy⟩

/-! ## The coset space -/

/-- The left cosets of the level-zero copy of `Γ`. -/
abbrev Cosets : Type u := Vertical α hα ⧸ (iotaVertical α hα).range

instance : MulAction (Vertical α hα) (Cosets α hα) :=
  inferInstanceAs (MulAction (Vertical α hα)
    (Vertical α hα ⧸ (iotaVertical α hα).range))

/-- The root coset. -/
def rootCoset : Cosets α hα := QuotientGroup.mk 1

theorem smul_rootCoset (v : Vertical α hα) :
    v • rootCoset α hα = QuotientGroup.mk v := by
  show v • (QuotientGroup.mk 1 : Vertical α hα ⧸ (iotaVertical α hα).range) =
    QuotientGroup.mk v
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]

/-- The base copy of `Γ` fixes the root coset. -/
theorem iotaVertical_smul_rootCoset (γ : Γ) :
    iotaVertical α hα γ • rootCoset α hα = rootCoset α hα := by
  rw [smul_rootCoset]
  show QuotientGroup.mk (iotaVertical α hα γ) =
    (QuotientGroup.mk 1 : Vertical α hα ⧸ (iotaVertical α hα).range)
  rw [QuotientGroup.eq]
  rw [mul_one]
  apply Subgroup.inv_mem
  exact ⟨γ, rfl⟩

include hα in
/-- The two cosets carrying the marked word are distinct. -/
theorem moved_cosets_ne {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    tVertical α hα • rootCoset α hα ≠
      (iotaVertical α hα a₀ * tVertical α hα) • rootCoset α hα := by
  rw [smul_rootCoset, smul_rootCoset]
  intro h
  rw [QuotientGroup.eq] at h
  apply tVertical_inv_conj_not_mem α hα ha₀
  simpa [mul_assoc] using h

/-! ## The ambient group -/

/-- The coset permutation action composed with the lamp action. -/
def lampAction : Vertical α hα →* MulAut (CliffordLamp (Cosets α hα)) :=
  (permHom (Cosets α hα)).comp
    (MulAction.toPermHom (Vertical α hα) (Cosets α hα))

theorem lampAction_apply_lamp (v : Vertical α hα) (x : Cosets α hα) :
    lampAction α hα v (lamp (Cosets α hα) x) =
      lamp (Cosets α hα) (v • x) := by
  show permHom (Cosets α hα)
    (MulAction.toPermHom (Vertical α hα) (Cosets α hα) v)
      (lamp (Cosets α hα) x) = lamp (Cosets α hα) (v • x)
  rw [permHom_apply_lamp]
  congr 1

theorem lampAction_apply_sign (v : Vertical α hα) :
    lampAction α hα v (sign (Cosets α hα)) = sign (Cosets α hα) := by
  show permHom (Cosets α hα)
    (MulAction.toPermHom (Vertical α hα) (Cosets α hα) v)
      (sign (Cosets α hα)) = sign (Cosets α hα)
  rw [permHom_apply_sign]

/-- The marked-compression ambient group. -/
abbrev Ambient : Type u :=
  CliffordLamp (Cosets α hα) ⋊[lampAction α hα] Vertical α hα

instance : Group (Ambient α hα) :=
  inferInstanceAs (Group
    (CliffordLamp (Cosets α hα) ⋊[lampAction α hα] Vertical α hα))

/-- The copy of `Γ` in the ambient group. -/
def iotaAmbient : Γ →* Ambient α hα :=
  (inr : Vertical α hα →* Ambient α hα).comp (iotaVertical α hα)

/-- The stable letter in the ambient group. -/
def tAmbient : Ambient α hα := inr (tVertical α hα)

/-- The root lamp in the ambient group. -/
def cAmbient : Ambient α hα := inl (lamp (Cosets α hα) (rootCoset α hα))

/-- The image of the central Clifford sign in the ambient group. -/
def signAmbient : Ambient α hα := inl (sign (Cosets α hα))

/-- The root lamp remains an involution in the ambient semidirect product. -/
theorem cAmbient_sq : cAmbient α hα ^ 2 = 1 := by
  show (inl (lamp (Cosets α hα) (rootCoset α hα)) : Ambient α hα) ^ 2 = 1
  rw [← map_pow, lamp_sq, map_one]

/-- Conjugation of a lamp by a vertical element moves its coset. -/
theorem conj_inl_lamp (v : Vertical α hα) (x : Cosets α hα) :
    (inr v : Ambient α hα) * inl (lamp (Cosets α hα) x) * (inr v)⁻¹ =
      inl (lamp (Cosets α hα) (v • x)) := by
  rw [← map_inv, ← inl_aut, lampAction_apply_lamp]

/-- The compression relation in the ambient group. -/
theorem compress (γ : Γ) :
    tAmbient α hα * iotaAmbient α hα γ * (tAmbient α hα)⁻¹ =
      iotaAmbient α hα (α γ) := by
  show inr (tVertical α hα) * inr (iotaVertical α hα γ) *
      (inr (tVertical α hα))⁻¹ = inr (iotaVertical α hα (α γ))
  rw [← map_inv, ← map_mul, ← map_mul, vertical_compress]

/-- The root lamp centralises the copy of `Γ`. -/
theorem comm_c (γ : Γ) : Commute (cAmbient α hα) (iotaAmbient α hα γ) := by
  have h : iotaAmbient α hα γ * cAmbient α hα * (iotaAmbient α hα γ)⁻¹ =
      cAmbient α hα := by
    show inr (iotaVertical α hα γ) *
        inl (lamp (Cosets α hα) (rootCoset α hα)) *
        (inr (iotaVertical α hα γ))⁻¹ = cAmbient α hα
    rw [conj_inl_lamp, iotaVertical_smul_rootCoset]
    rfl
  have h' : iotaAmbient α hα γ * cAmbient α hα =
      cAmbient α hα * iotaAmbient α hα γ :=
    mul_inv_eq_iff_eq_mul.mp h
  exact h'.symm

include hα in
/-- **The marked compression word is the Clifford sign.** -/
theorem marked_word_eq_sign {a₀ : Γ} (ha₀ : a₀ ∉ Set.range α) :
    markedCompressionWord (tAmbient α hα) (iotaAmbient α hα a₀)
      (cAmbient α hα) = signAmbient α hα := by
  have hd : tAmbient α hα * cAmbient α hα * (tAmbient α hα)⁻¹ =
      inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) :=
    conj_inl_lamp α hα _ _
  have had : iotaAmbient α hα a₀ *
      inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) *
      (iotaAmbient α hα a₀)⁻¹ =
      inl (lamp (Cosets α hα)
        ((iotaVertical α hα a₀ * tVertical α hα) • rootCoset α hα)) := by
    show inr (iotaVertical α hα a₀) *
        inl (lamp (Cosets α hα) (tVertical α hα • rootCoset α hα)) *
        (inr (iotaVertical α hα a₀))⁻¹ = _
    rw [conj_inl_lamp, smul_smul]
  rw [markedCompressionWord, hd, had, ← map_commutatorElement]
  rw [commutator_lamp_lamp (Cosets α hα) (moved_cosets_ne α hα ha₀)]
  rfl

/-- The sign squares to one in the ambient group. -/
theorem signAmbient_sq : signAmbient α hα ^ 2 = 1 := by
  show (inl (sign (Cosets α hα)) : Ambient α hα) ^ 2 = 1
  rw [← map_pow, sign_sq, map_one]

/-- The sign is central in the ambient group. -/
theorem signAmbient_central (g : Ambient α hα) :
    Commute (signAmbient α hα) g := by
  obtain ⟨n, v⟩ := g
  show signAmbient α hα * ⟨n, v⟩ = ⟨n, v⟩ * signAmbient α hα
  show (⟨sign (Cosets α hα), 1⟩ : Ambient α hα) * ⟨n, v⟩ =
    ⟨n, v⟩ * ⟨sign (Cosets α hα), 1⟩
  rw [SemidirectProduct.mul_def, SemidirectProduct.mul_def]
  apply SemidirectProduct.ext
  · show sign (Cosets α hα) * lampAction α hα 1 n =
      n * lampAction α hα v (sign (Cosets α hα))
    rw [map_one, lampAction_apply_sign]
    show sign (Cosets α hα) * n = n * sign (Cosets α hα)
    exact (sign_commute (Cosets α hα) n).eq
  · change (1 : Vertical α hα) * v = v
    exact one_mul v

include hα in
/-- The sign survives in the ambient group. -/
theorem signAmbient_ne_one : signAmbient α hα ≠ 1 := by
  intro h
  have h1 : sign (Cosets α hα) = 1 := by
    apply (inl_injective (N := CliffordLamp (Cosets α hα))
      (G := Vertical α hα))
    change (inl (sign (Cosets α hα)) : Ambient α hα) = inl 1
    change signAmbient α hα = inl 1
    rw [h, map_one]
  exact sign_ne_one (Cosets α hα) h1

/-! ## Countability -/

instance semidirectProductCountable {N : Type*} {G : Type*}
    [Group N] [Group G] {φ : G →* MulAut N} [Countable N] [Countable G] :
    Countable (N ⋊[φ] G) := by
  apply Countable.of_equiv (N × G)
  exact ⟨fun p => ⟨p.1, p.2⟩, fun s => (s.left, s.right), fun _ => rfl,
    fun _ => rfl⟩

instance [Countable Γ] : Countable (Vertical α hα) :=
  letI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.toAdd
  semidirectProductCountable

instance [Countable Γ] : Countable (Cosets α hα) :=
  Function.Surjective.countable
    (Quotient.mk_surjective (α := Vertical α hα))

instance [Countable Γ] : Countable (Ambient α hα) :=
  inferInstanceAs (Countable
    (CliffordLamp (Cosets α hα) ⋊[lampAction α hα] Vertical α hα))

/-! ## The explicit instantiation -/

namespace Explicit

open ExplicitNonMFBase

/-- The explicit marked-compression group over the internal Kazhdan base. -/
noncomputable def theGroup : Type :=
  Ambient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective

noncomputable instance : Group theGroup :=
  inferInstanceAs (Group
    (Ambient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective))

instance : Countable theGroup :=
  inferInstanceAs (Countable
    (Ambient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective))

/-- The embedding data of the base. -/
noncomputable def theIota : Base →* theGroup :=
  iotaAmbient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective

/-- The stable letter. -/
noncomputable def theT : theGroup :=
  tAmbient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective

/-- The root lamp. -/
noncomputable def theC : theGroup :=
  cAmbient (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective

/-- The compression relation. -/
theorem theCompress (γ : Base) :
    theT * theIota γ * theT⁻¹ = theIota (compression γ) :=
  compress (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective γ

/-- The root lamp centralises the base. -/
theorem theCommC (γ : Base) : Commute theC (theIota γ) :=
  comm_c (BinaryLeavitt.elementaryShift (ZMod 2)) compression_injective γ

/-- The root lamp is an involution. -/
theorem theCSq : theC ^ 2 = 1 := by
  exact cAmbient_sq _ _

/-- The marked word squares to one. -/
theorem theWordSq :
    markedCompressionWord theT (theIota omitted) theC ^ 2 = 1 := by
  change markedCompressionWord
    (tAmbient compression compression_injective)
    (iotaAmbient compression compression_injective omitted)
    (cAmbient compression compression_injective) ^ 2 = 1
  rw [marked_word_eq_sign _ _ omitted_not_mem_range]
  exact signAmbient_sq _ _

/-- The marked word is central. -/
theorem theWordCentral (g : theGroup) :
    Commute (markedCompressionWord theT (theIota omitted) theC) g := by
  change Commute (markedCompressionWord
    (tAmbient compression compression_injective)
    (iotaAmbient compression compression_injective omitted)
    (cAmbient compression compression_injective)) g
  rw [marked_word_eq_sign _ _ omitted_not_mem_range]
  exact signAmbient_central _ _ g

/-- The marked word is the surviving Clifford sign. -/
theorem theWordNeOne :
    markedCompressionWord theT (theIota omitted) theC ≠ 1 := by
  change markedCompressionWord
    (tAmbient compression compression_injective)
    (iotaAmbient compression compression_injective omitted)
    (cAmbient compression compression_injective) ≠ 1
  rw [marked_word_eq_sign _ _ omitted_not_mem_range]
  exact signAmbient_ne_one _ _

end Explicit
end MarkedCompression
end GroupApproximation
