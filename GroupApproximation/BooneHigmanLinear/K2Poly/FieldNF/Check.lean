import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNagao
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegSpans
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: the van der Waerden check modulo the constant `K₂`

k2-poly piece A5.2 (lane k2-field-a). This is the field-generic framework for the Nagao
normal-form chain of bh-met-92c/92h, which was written over `ZMod p`. Notation of
`K2Poly.FieldNagao`: `R = F[X]`, `K` a finset, `L ∉ K`, and `S_K = fnS F K`,
`V = fnV F K L`, `Z = fnZ F = C(K₂(I, F))`, inside `St_I(R)`.

Over `F_p` the coset target is `Q = S_K ⊔ V`. Over an arbitrary field, Euclid's algorithm
produces symbol factors in the constant `K₂`. So the target here is `Z ⊔ Q` (`fnZQ`). A join
of subgroups is a subgroup, so the closure lemmas (`fnGood` is closed under products,
inverses and commutators) go through unchanged, with no centrality hypothesis.

* `fnCheck`, `fnGood`: the coset check of `g` against a set map `σ` on the orbit
  `S_{K ∪ {L}} e_L`, with target `Z ⊔ Q`.
* `fn_good_mul`, `fn_good_inv`, `fn_good_comm`, and `fn_closure` (the check on the
  generating roots gives it on all of `S_{K ∪ {L}}`).
* `fn_good_all`: the small generating set `x_im(1)`, `x_mi(1)` (`i ∈ K \ {m}`), `x_mL(1)` and
  the family `x_Lm(f)` makes every root good (a copy of lane 92h's generation argument; it
  uses only the Steinberg relations).
* `FieldCosetAt F` (the van der Waerden criterion over `F`) and `FieldZCentralAt F` (A5.1:
  the constant `K₂` is central in `St_I(F[X])`).
* **`fieldStab_of_coset`**: `FieldZCentralAt F → FieldCosetAt F → FieldStabAt F`.
  Centrality is used only in this last step, to write an element of `Z ⊔ Q` as `z · q`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open scoped commutatorElement
open scoped Pointwise
open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic (K2)
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnV fnZ fnC FieldStabAt)
open GroupApproximation.BooneHigman.Metabelian.ElemFP (k2PolyDeg_le_normalizer
  k2PolyDeg_w_conj_self_symm_eq)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w x_congr conj_of_commute
  conj_x_right)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  x_mem_rootSpan rootSpan_induction rootSpan_normalizes act unitVec unitVec_apply act_mul
  act_one)

variable {I : Type} [Fintype I] [DecidableEq I]

section Defs

variable (F : Type) [Field F]

/-- `Q = S_K ⊔ V`, the stabilizer of `e_L` expected over `F_p`. -/
noncomputable def fnQ (K : Finset I) (L : I) : Subgroup (SteinbergGroup I (Polynomial F)) :=
  fnS F K ⊔ fnV F K L

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnQ

/-- The target over a field: `Z ⊔ Q`, with `Z = C(K₂(I, F))` the constant `K₂`. -/
noncomputable def fnZQ (K : Finset I) (L : I) : Subgroup (SteinbergGroup I (Polynomial F)) :=
  fnZ F ⊔ fnQ F K L

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnZQ

/-- The coset check of `g` against `σ`, on the whole orbit `S_{K ∪ {L}} e_L`. -/
def fnCheck (K : Finset I) (L : I) (σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F))
    (g : SteinbergGroup I (Polynomial F)) : Prop :=
  ∀ v : I → Polynomial F, (∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) →
    (σ (act g v))⁻¹ * g * σ v ∈ fnZQ F K L

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnCheck

/-- `g` is *good*: it lies in `S_{K ∪ {L}}` and passes the coset check. -/
def fnGood (K : Finset I) (L : I) (σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F))
    (g : SteinbergGroup I (Polynomial F)) : Prop :=
  g ∈ fnS F (insert L K) ∧ fnCheck F K L σ g

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnGood

end Defs

/-- **The van der Waerden criterion over `F`.** A set section `σ` of the orbit, with
`σ(e_L) ∈ Z ⊔ Q`, passing the check at every root of `S_{K ∪ {L}}`. -/
def FieldCosetAt (F : Type) [Field F] : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (L : I), L ∉ K → K.Nonempty →
    (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ s ∈ fnS F K, s ∈ K2 I (Polynomial F) → s ∈ fnC F) →
    ∃ σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F),
      σ (unitVec L) ∈ fnZQ F K L ∧
      ∀ (i j : I) (hij : i ≠ j) (a : Polynomial F), i ∈ insert L K → j ∈ insert L K →
        fnCheck F K L σ (x i j hij a)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.FieldCosetAt

/-- **A5.1.** The constant `K₂` is central in `St_I(F[X])` (for `|I| ≥ 3`). -/
def FieldZCentralAt (F : Type) [Field F] : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I], (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    ∀ z ∈ fnZ (I := I) F, ∀ g : SteinbergGroup I (Polynomial F), z * g = g * z

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.FieldZCentralAt

/-- The hypothesis bundle of the small generating set, at a fixed `m ∈ K`. -/
def fnGenGood (F : Type) [Field F] (K : Finset I) (L m : I) (hmL : m ≠ L)
    (σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)) : Prop :=
  (∀ (i : I) (him : i ≠ m), i ∈ K →
      fnGood F K L σ (x i m him (1 : Polynomial F)) ∧
        fnGood F K L σ (x m i him.symm (1 : Polynomial F))) ∧
    fnGood F K L σ (x m L hmL (1 : Polynomial F)) ∧
    ∀ f : Polynomial F, fnGood F K L σ (x L m hmL.symm f)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnGenGood

variable {F : Type} [Field F]

/-- The orbit `S_{K ∪ {L}} e_L` is stable under `S_{K ∪ {L}}`. -/
theorem fn_orbit_act {K : Finset I} {L : I} {g : SteinbergGroup I (Polynomial F)}
    (hg : g ∈ fnS F (insert L K)) {v : I → Polynomial F}
    (hv : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) :
    ∃ y ∈ fnS F (insert L K), act y (unitVec L) = act g v := by
  obtain ⟨y, hy, rfl⟩ := hv
  exact ⟨g * y, Subgroup.mul_mem _ hg hy, act_mul g y (unitVec L)⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_orbit_act

/-- Good elements are closed under products. -/
theorem fn_good_mul {K : Finset I} {L : I}
    {σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)}
    {g k : SteinbergGroup I (Polynomial F)} (hg : fnGood F K L σ g)
    (hk : fnGood F K L σ k) : fnGood F K L σ (g * k) := by
  refine ⟨Subgroup.mul_mem _ hg.1 hk.1, fun v hv => ?_⟩
  have e : (σ (act (g * k) v))⁻¹ * (g * k) * σ v =
      ((σ (act g (act k v)))⁻¹ * g * σ (act k v)) * ((σ (act k v))⁻¹ * k * σ v) := by
    rw [act_mul]
    group
  rw [e]
  exact Subgroup.mul_mem _ (hg.2 (act k v) (fn_orbit_act hk.1 hv)) (hk.2 v hv)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_good_mul

/-- Good elements are closed under inverses. -/
theorem fn_good_inv {K : Finset I} {L : I}
    {σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)}
    {g : SteinbergGroup I (Polynomial F)} (hg : fnGood F K L σ g) :
    fnGood F K L σ g⁻¹ := by
  refine ⟨Subgroup.inv_mem _ hg.1, fun v hv => ?_⟩
  have h := hg.2 (act g⁻¹ v) (fn_orbit_act (Subgroup.inv_mem _ hg.1) hv)
  have e1 : act g (act g⁻¹ v) = v := by
    rw [← act_mul, mul_inv_cancel, act_one]
  rw [e1] at h
  have e2 : (σ (act g⁻¹ v))⁻¹ * g⁻¹ * σ v = ((σ v)⁻¹ * g * σ (act g⁻¹ v))⁻¹ := by
    group
  rw [e2]
  exact Subgroup.inv_mem _ h

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_good_inv

/-- Good elements are closed under commutators. -/
theorem fn_good_comm {K : Finset I} {L : I}
    {σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)}
    {g k : SteinbergGroup I (Polynomial F)} (hg : fnGood F K L σ g)
    (hk : fnGood F K L σ k) : fnGood F K L σ ⁅g, k⁆ := by
  rw [commutatorElement_def]
  exact fn_good_mul (fn_good_mul (fn_good_mul hg hk) (fn_good_inv hg)) (fn_good_inv hk)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_good_comm

/-- **Closure.** The check at every generating root gives it at every `g ∈ S_{K ∪ {L}}`. -/
theorem fn_closure {K : Finset I} {L : I}
    (σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F))
    (hgen : ∀ (i j : I) (hij : i ≠ j) (a : Polynomial F), i ∈ insert L K →
      j ∈ insert L K → fnCheck F K L σ (x i j hij a))
    {g : SteinbergGroup I (Polynomial F)} (hg : g ∈ fnS F (insert L K)) :
    fnCheck F K L σ g := by
  refine rootSpan_induction (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K)
    (Q := fun g => fnCheck F K L σ g) ?_ ?_ ?_ hg
  · intro i j hij a hq
    have hq' : i ∈ insert L K ∧ j ∈ insert L K := hq
    exact hgen i j hij a hq'.1 hq'.2
  · intro v _
    show (σ (act 1 v))⁻¹ * 1 * σ v ∈ fnZQ F K L
    rw [act_one, mul_one, inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro g k _ hk hg' hk' v hv
    show (σ (act (g * k) v))⁻¹ * (g * k) * σ v ∈ fnZQ F K L
    have hkG : k ∈ fnS F (insert L K) := hk
    have hkv := fn_orbit_act hkG hv
    have e : (σ (act (g * k) v))⁻¹ * (g * k) * σ v =
        ((σ (act g (act k v)))⁻¹ * g * σ (act k v)) * ((σ (act k v))⁻¹ * k * σ v) := by
      rw [act_mul]
      group
    rw [e]
    exact Subgroup.mul_mem _ (hg' (act k v) hkv) (hk' v hv)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_closure

/-- `S_K` normalizes `V` (lane 91c's argument, over `F`). -/
theorem fn_S_le_normalizer_V {K : Finset I} {L : I} (hLK : L ∉ K) :
    fnS F K ≤ Subgroup.normalizer (fnV F K L : Set (SteinbergGroup I (Polynomial F))) := by
  refine k2PolyDeg_le_normalizer fun s hs v hv => rootSpan_normalizes
    (p := fun i j => i ∈ K ∧ j ∈ K) (q := fun i j => i = L ∧ j ∈ K) ?_ hs hv
  intro i j hij a hp k l hkl b hq
  obtain ⟨hi, hj⟩ := hp
  obtain ⟨hk, hl⟩ := hq
  have hiL : i ≠ L := fun e => hLK (e ▸ hi)
  have hjL : j ≠ L := fun e => hLK (e ▸ hj)
  by_cases hli : l = i
  · have e : x k l hkl b = x L i hiL.symm b := x_congr _ _ hk hli rfl
    rw [e, conj_x_right L i j hiL.symm hij hjL.symm b a]
    exact Subgroup.mul_mem _ (x_mem_rootSpan _ _ ⟨rfl, hi⟩) (x_mem_rootSpan _ _ ⟨rfl, hj⟩)
  · have hjk : j ≠ k := fun e => hjL (e.trans hk)
    rw [conj_of_commute (x_commute_of_ne i j k l hij hkl hjk hli a b)]
    exact x_mem_rootSpan hkl b ⟨hk, hl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_S_le_normalizer_V

/-- Every element of `Q = S_K ⊔ V` is `s v`. -/
theorem fn_SV_decomp {K : Finset I} {L : I} (hLK : L ∉ K)
    {g : SteinbergGroup I (Polynomial F)} (hg : g ∈ fnQ F K L) :
    ∃ s ∈ fnS F K, ∃ v ∈ fnV F K L, s * v = g := by
  have hg' : g ∈ (fnS F K : Set (SteinbergGroup I (Polynomial F))) *
      (fnV F K L : Set (SteinbergGroup I (Polynomial F))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (fn_S_le_normalizer_V hLK)]
    exact hg
  exact Set.mem_mul.mp hg'

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_SV_decomp

/-- A central `Z` normalizes every subgroup. -/
theorem fn_Z_le_normalizer
    (hZ : ∀ z ∈ fnZ (I := I) F, ∀ g : SteinbergGroup I (Polynomial F), z * g = g * z)
    (H : Subgroup (SteinbergGroup I (Polynomial F))) :
    fnZ (I := I) F ≤ Subgroup.normalizer (H : Set (SteinbergGroup I (Polynomial F))) :=
  k2PolyDeg_le_normalizer fun z hz h hh => by
    rw [hZ z hz h, mul_inv_cancel_right]
    exact hh

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_Z_le_normalizer

/-- With `Z` central, every element of `Z ⊔ Q` is `z q`. -/
theorem fn_ZQ_decomp
    (hZ : ∀ z ∈ fnZ (I := I) F, ∀ g : SteinbergGroup I (Polynomial F), z * g = g * z)
    {K : Finset I} {L : I} {g : SteinbergGroup I (Polynomial F)} (hg : g ∈ fnZQ F K L) :
    ∃ z ∈ fnZ (I := I) F, ∃ q ∈ fnQ F K L, z * q = g := by
  have hg' : g ∈ (fnZ (I := I) F : Set (SteinbergGroup I (Polynomial F))) *
      (fnQ F K L : Set (SteinbergGroup I (Polynomial F))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ (fn_Z_le_normalizer hZ (fnQ F K L))]
    exact hg
  exact Set.mem_mul.mp hg'

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_ZQ_decomp

/-- **The criterion gives the residual `FieldStabAt F`**, given A5.1. -/
theorem fieldStab_of_coset (hZ : FieldZCentralAt F) (hC : FieldCosetAt F) : FieldStabAt F := by
  intro I _ _ K L hLK hK hthird ih g hg hfix
  obtain ⟨σ, hσ, hgen⟩ := hC K L hLK hK hthird ih
  have h1 := fn_closure σ hgen hg (unitVec L) ⟨1, Subgroup.one_mem _, act_one _⟩
  rw [hfix] at h1
  have hmem : g ∈ fnZQ F K L := by
    have e : g = σ (unitVec L) * ((σ (unitVec L))⁻¹ * g * σ (unitVec L)) *
        (σ (unitVec L))⁻¹ := by
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ h1) (Subgroup.inv_mem _ hσ)
  obtain ⟨z, hz, q, hq, rfl⟩ := fn_ZQ_decomp (hZ hthird) hmem
  obtain ⟨s, hs, v, hv, rfl⟩ := fn_SV_decomp hLK hq
  exact ⟨z, hz, s, hs, v, hv, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fieldStab_of_coset

/-- The Weyl element `W = w_mL(1)` is good. -/
theorem fn_good_W {K : Finset I} {L m : I}
    {σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)} (hmL : m ≠ L)
    (hy : fnGood F K L σ (x m L hmL (1 : Polynomial F)))
    (hLm : ∀ f : Polynomial F, fnGood F K L σ (x L m hmL.symm f)) :
    fnGood F K L σ (w m L hmL (1 : (Polynomial F)ˣ)) := by
  have e1 : ((1 : (Polynomial F)ˣ) : Polynomial F) = 1 := Units.val_one
  have e2 : (((1 : (Polynomial F)ˣ)⁻¹ : (Polynomial F)ˣ) : Polynomial F) = 1 := by
    rw [inv_one, Units.val_one]
  rw [w, e1, e2]
  exact fn_good_mul (fn_good_mul hy (hLm (-1))) hy

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_good_W

/-- `x_mL(f) = W x_Lm(-f) W⁻¹` is good. -/
theorem fn_good_mL {K : Finset I} {L m n : I}
    {σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n)
    (hy : fnGood F K L σ (x m L hmL (1 : Polynomial F)))
    (hLm : ∀ f : Polynomial F, fnGood F K L σ (x L m hmL.symm f))
    (f : Polynomial F) : fnGood F K L σ (x m L hmL f) := by
  have e : x m L hmL f = w m L hmL (1 : (Polynomial F)ˣ) * x L m hmL.symm (-f) *
      (w m L hmL (1 : (Polynomial F)ˣ))⁻¹ := by
    rw [k2PolyDeg_w_conj_self_symm_eq m L n hmL hmn hLn (1 : (Polynomial F)ˣ) (-f)]
    simp only [Units.val_one, one_mul, mul_one, neg_neg]
  rw [e]
  exact fn_good_mul (fn_good_mul (fn_good_W hmL hy hLm) (hLm (-f)))
    (fn_good_inv (fn_good_W hmL hy hLm))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_good_mL

/-- **Generation.** The small generating set being good makes every root good. -/
theorem fn_good_all {K : Finset I} {L m n : I} (hLK : L ∉ K)
    {σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n) (hG : fnGenGood F K L m hmL σ)
    (i j : I) (hij : i ≠ j) (a : Polynomial F) (hi : i ∈ insert L K)
    (hj : j ∈ insert L K) : fnGood F K L σ (x i j hij a) := by
  obtain ⟨hS, hy, hLm⟩ := hG
  have good_iL : ∀ {i : I}, i ∈ K → ∀ (hiL : i ≠ L) (f : Polynomial F),
      fnGood F K L σ (x i L hiL f) := by
    intro i hiK hiL f
    by_cases him : i = m
    · rw [x_congr hiL hmL him rfl (rfl : f = f)]
      exact fn_good_mL hmL hmn hLn hy hLm f
    · have e : x i L hiL f = ⁅x i m him (1 : Polynomial F), x m L hmL f⁆ := by
        rw [x_commutator i m L him hmL hiL, one_mul]
      rw [e]
      exact fn_good_comm (hS i him hiK).1 (fn_good_mL hmL hmn hLn hy hLm f)
  have good_Lj : ∀ {j : I}, j ∈ K → ∀ (hLj : L ≠ j) (f : Polynomial F),
      fnGood F K L σ (x L j hLj f) := by
    intro j hjK hLj f
    by_cases hjm : j = m
    · rw [x_congr hLj hmL.symm rfl hjm (rfl : f = f)]
      exact hLm f
    · have e : x L j hLj f = ⁅x L m hmL.symm f, x m j (Ne.symm hjm) (1 : Polynomial F)⁆ := by
        rw [x_commutator L m j hmL.symm (Ne.symm hjm) hLj, mul_one]
      rw [e]
      exact fn_good_comm (hLm f) (hS j hjm hjK).2
  by_cases hiL : i = L
  · have hjK : j ∈ K :=
      (Finset.mem_insert.1 hj).resolve_left (fun h => hij (hiL.trans h.symm))
    have hLj : L ≠ j := fun e => hij (hiL.trans e)
    rw [x_congr hij hLj hiL rfl (rfl : a = a)]
    exact good_Lj hjK hLj a
  · have hiK : i ∈ K := (Finset.mem_insert.1 hi).resolve_left hiL
    by_cases hjL : j = L
    · rw [x_congr hij (Ne.intro hiL) rfl hjL (rfl : a = a)]
      exact good_iL hiK (Ne.intro hiL) a
    · have hjK : j ∈ K := (Finset.mem_insert.1 hj).resolve_left hjL
      have hLj : L ≠ j := fun e => hLK (e ▸ hjK)
      have e : x i j hij a = ⁅x i L hiL a, x L j hLj (1 : Polynomial F)⁆ := by
        rw [x_commutator i L j hiL hLj hij, mul_one]
      rw [e]
      exact fn_good_comm (good_iL hiK hiL a) (good_Lj hjK hLj 1)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_good_all

/-- **The generating-set form of the criterion.** A `σ` with `σ(e_L) ∈ Z ⊔ Q` that is good on
the small generating set (for some `m ∈ K` and third index `n`) passes the check at every root. -/
theorem fn_coset_of_gen {K : Finset I} {L m n : I} (hLK : L ∉ K)
    {σ : (I → Polynomial F) → SteinbergGroup I (Polynomial F)} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n) (hG : fnGenGood F K L m hmL σ) :
    ∀ (i j : I) (hij : i ≠ j) (a : Polynomial F), i ∈ insert L K → j ∈ insert L K →
      fnCheck F K L σ (x i j hij a) := fun i j hij a hi hj =>
  (fn_good_all hLK hmL hmn hLn hG i j hij a hi hj).2

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_coset_of_gen

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
