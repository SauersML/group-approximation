import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Commute.Basic
import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.KMSPresentation

/-!
# The operations `f * a` and `f * A` on an abelian normal subgroup

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex` (Kharlampovich's
finitely presented solvable group with undecidable word problem), forward direction of
Kharlampovich--Myasnikov--Sapir (arXiv:1204.6506) Theorem `tmm`(b), equation `(e000)`.

Let `T` be a normal subgroup of a group `G` whose elements commute pairwise.  On `T` the
operations
* `f ↦ khStar f a a' = f⁻¹ f^{a} (f^{a⁻¹})⁻¹ f^{(a')⁻¹}`,
* `f ↦ khComm f A = f⁻¹ f^{A}`
are multiplicative, and two such operations commute when the letters involved commute
(`khStar_khStar_of_commute`, `khComm_khStar_of_commute`, `khComm_khComm_of_commute`).
This is the "stars by letters from different blocks commute on `T`" step of the source.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

namespace Forward

variable {G : Type*} [Group G]

/-- A map `G → G` preserving the subgroup `T` and multiplicative on `T`. -/
structure IsTMap (T : Subgroup G) (F : G → G) : Prop where
  /-- `F` maps `T` into `T`. -/
  mem : ∀ f ∈ T, F f ∈ T
  /-- `F` is multiplicative on `T`. -/
  mul : ∀ f ∈ T, ∀ h ∈ T, F (f * h) = F f * F h

/-- Conjugation as a monoid endomorphism, `x ↦ khConj x g = g⁻¹ x g`. -/
def conjHom (g : G) : G →* G where
  toFun x := khConj x g
  map_one' := by simp only [khConj, mul_one, inv_mul_cancel]
  map_mul' x y := by simp only [khConj, mul_assoc, mul_inv_cancel_left]

theorem conjHom_apply (g x : G) : conjHom g x = khConj x g := rfl

theorem khConj_mul (f h g : G) : khConj (f * h) g = khConj f g * khConj h g :=
  map_mul (conjHom g) f h

theorem khConj_eq_self {a g : G} (h : Commute a g) : khConj a g = a := by
  show g⁻¹ * a * g = a
  rw [mul_assoc, h.eq, inv_mul_cancel_left]

theorem khComm_eq_inv_mul_khConj (u v : G) : khComm u v = u⁻¹ * khConj u v := by
  simp only [khComm, khConj, mul_assoc]

theorem khConj_khStar {a a' g : G} (ha : Commute a g) (ha' : Commute a' g) (f : G) :
    khConj (khStar f a a') g = khStar (khConj f g) a a' := by
  have h := map_khStar (conjHom g) f a a'
  rw [conjHom_apply, conjHom_apply, conjHom_apply, conjHom_apply, khConj_eq_self ha,
    khConj_eq_self ha'] at h
  exact h

theorem khConj_khComm {A g : G} (hA : Commute A g) (f : G) :
    khConj (khComm f A) g = khComm (khConj f g) A := by
  have h := map_khComm (conjHom g) f A
  rw [conjHom_apply, conjHom_apply, conjHom_apply, khConj_eq_self hA] at h
  exact h

section Abelian

variable {T : Subgroup G}

theorem khConj_mem [hN : T.Normal] {f : G} (hf : f ∈ T) (g : G) : khConj f g ∈ T :=
  hN.conj_mem' f hf g

theorem isTMap_id : IsTMap T (fun f ↦ f) :=
  ⟨fun _ hf ↦ hf, fun _ _ _ _ ↦ rfl⟩

theorem isTMap_conj [T.Normal] (g : G) : IsTMap T (fun f ↦ khConj f g) :=
  ⟨fun _ hf ↦ khConj_mem hf g, fun f _ h _ ↦ khConj_mul f h g⟩

variable (hT : ∀ u ∈ T, ∀ v ∈ T, Commute u v)
include hT

theorem isTMap_mul {F E : G → G} (hF : IsTMap T F) (hE : IsTMap T E) :
    IsTMap T (fun f ↦ F f * E f) := by
  refine ⟨fun f hf ↦ ?_, fun f hf h hh ↦ ?_⟩
  · exact T.mul_mem (hF.mem f hf) (hE.mem f hf)
  · show F (f * h) * E (f * h) = F f * E f * (F h * E h)
    rw [hF.mul f hf h hh, hE.mul f hf h hh]
    exact (hT _ (hF.mem h hh) _ (hE.mem f hf)).mul_mul_mul_comm _ _

theorem isTMap_inv {F : G → G} (hF : IsTMap T F) : IsTMap T (fun f ↦ (F f)⁻¹) := by
  refine ⟨fun f hf ↦ ?_, fun f hf h hh ↦ ?_⟩
  · exact T.inv_mem (hF.mem f hf)
  · show (F (f * h))⁻¹ = (F f)⁻¹ * (F h)⁻¹
    rw [hF.mul f hf h hh, mul_inv_rev]
    exact (hT _ (T.inv_mem (hF.mem h hh)) _ (T.inv_mem (hF.mem f hf))).eq

theorem isTMap_khStar [T.Normal] (a a' : G) : IsTMap T (fun f ↦ khStar f a a') := by
  have h1 := isTMap_mul hT (isTMap_inv hT (isTMap_id (T := T))) (isTMap_conj (T := T) a)
  have h2 := isTMap_mul hT h1 (isTMap_inv hT (isTMap_conj (T := T) a⁻¹))
  have h3 := isTMap_mul hT h2 (isTMap_conj (T := T) a'⁻¹)
  exact h3

theorem isTMap_khComm [T.Normal] (A : G) : IsTMap T (fun f ↦ khComm f A) := by
  have h := isTMap_mul hT (isTMap_inv hT (isTMap_id (T := T))) (isTMap_conj (T := T) A)
  refine ⟨fun f hf ↦ ?_, fun f hf g hg ↦ ?_⟩
  · show khComm f A ∈ T
    rw [khComm_eq_inv_mul_khConj]
    exact h.mem f hf
  · show khComm (f * g) A = khComm f A * khComm g A
    rw [khComm_eq_inv_mul_khConj, khComm_eq_inv_mul_khConj, khComm_eq_inv_mul_khConj]
    exact h.mul f hf g hg

omit hT in
theorem IsTMap.map_one' {F : G → G} (hF : IsTMap T F) : F 1 = 1 := by
  have h := hF.mul 1 T.one_mem 1 T.one_mem
  rw [mul_one] at h
  have h2 : F 1 * 1 = F 1 * F 1 := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel h2).symm

omit hT in
theorem IsTMap.apply_inv {F : G → G} (hF : IsTMap T F) {f : G} (hf : f ∈ T) :
    F f⁻¹ = (F f)⁻¹ := by
  have h := hF.mul f hf f⁻¹ (T.inv_mem hf)
  rw [mul_inv_cancel, hF.map_one'] at h
  exact eq_inv_of_mul_eq_one_right h.symm

omit hT in
/-- A `T`-multiplicative map commuting with conjugation by `b`, `b⁻¹`, `(b')⁻¹` commutes
with `f ↦ f * b`. -/
theorem khStar_apply_of_conj [T.Normal] {F : G → G} (hF : IsTMap T F) {b b' : G}
    (h1 : ∀ f ∈ T, F (khConj f b) = khConj (F f) b)
    (h2 : ∀ f ∈ T, F (khConj f b⁻¹) = khConj (F f) b⁻¹)
    (h3 : ∀ f ∈ T, F (khConj f b'⁻¹) = khConj (F f) b'⁻¹) {f : G} (hf : f ∈ T) :
    khStar (F f) b b' = F (khStar f b b') := by
  have m1 : f⁻¹ ∈ T := T.inv_mem hf
  have m2 : khConj f b ∈ T := khConj_mem hf b
  have m3 : (khConj f b⁻¹)⁻¹ ∈ T := T.inv_mem (khConj_mem hf b⁻¹)
  have m4 : khConj f b'⁻¹ ∈ T := khConj_mem hf b'⁻¹
  have m12 : f⁻¹ * khConj f b ∈ T := T.mul_mem m1 m2
  have m123 : f⁻¹ * khConj f b * (khConj f b⁻¹)⁻¹ ∈ T := T.mul_mem m12 m3
  show khStar (F f) b b' = F (f⁻¹ * khConj f b * (khConj f b⁻¹)⁻¹ * khConj f b'⁻¹)
  rw [hF.mul _ m123 _ m4, hF.mul _ m12 _ m3, hF.mul _ m1 _ m2, hF.apply_inv hf,
    hF.apply_inv (khConj_mem hf b⁻¹), h1 f hf, h2 f hf, h3 f hf]
  rfl

omit hT in
/-- A `T`-multiplicative map commuting with conjugation by `A` commutes with `f ↦ f * A`. -/
theorem khComm_apply_of_conj [T.Normal] {F : G → G} (hF : IsTMap T F) {A : G}
    (hA : ∀ f ∈ T, F (khConj f A) = khConj (F f) A) {f : G} (hf : f ∈ T) :
    khComm (F f) A = F (khComm f A) := by
  rw [khComm_eq_inv_mul_khConj, khComm_eq_inv_mul_khConj,
    hF.mul _ (T.inv_mem hf) _ (khConj_mem hf A), hF.apply_inv hf, hA f hf]

/-- Stars by pairwise commuting letters commute on `T`. -/
theorem khStar_khStar_of_commute [T.Normal] {a a' b b' : G} (hab : Commute a b)
    (hab' : Commute a b') (ha'b : Commute a' b) (ha'b' : Commute a' b') {f : G} (hf : f ∈ T) :
    khStar (khStar f a a') b b' = khStar (khStar f b b') a a' :=
  khStar_apply_of_conj (isTMap_khStar hT a a')
    (fun f _ ↦ (khConj_khStar hab ha'b f).symm)
    (fun f _ ↦ (khConj_khStar hab.inv_right ha'b.inv_right f).symm)
    (fun f _ ↦ (khConj_khStar hab'.inv_right ha'b'.inv_right f).symm) hf

/-- `f ↦ f * A` commutes on `T` with a star by letters commuting with `A`. -/
theorem khComm_khStar_of_commute [T.Normal] {A b b' : G} (hb : Commute A b)
    (hb' : Commute A b') {f : G} (hf : f ∈ T) :
    khComm (khStar f b b') A = khStar (khComm f A) b b' :=
  (khStar_apply_of_conj (isTMap_khComm hT A)
    (fun f _ ↦ (khConj_khComm hb f).symm)
    (fun f _ ↦ (khConj_khComm hb.inv_right f).symm)
    (fun f _ ↦ (khConj_khComm hb'.inv_right f).symm) hf).symm

/-- `f ↦ f * A` and `f ↦ f * B` commute on `T` when `A` and `B` commute. -/
theorem khComm_khComm_of_commute [T.Normal] {A B : G} (hAB : Commute A B) {f : G}
    (hf : f ∈ T) : khComm (khComm f A) B = khComm (khComm f B) A :=
  khComm_apply_of_conj (isTMap_khComm hT A) (fun f _ ↦ (khConj_khComm hAB f).symm) hf

end Abelian

end Forward

end KMS

end GroupApproximation.Full.Kharlampovich
