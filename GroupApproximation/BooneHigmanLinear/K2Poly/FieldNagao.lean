import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyFieldConst
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoInjective
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over an arbitrary field: the induction, with the stabilizer as residual

k2-poly piece A5 (owner bh-pal-wire). The target `FieldNKStatement` asks for
`ElemFP.k2PolyField_ConstStatement F N` for every field `F` and `N ≥ 5`: every element of
`K₂(N, F[X])` is `C y` for some `y ∈ St(N, F)`. This is Rehmann's theorem, of Nagao type.

The `F_p` proof on main (the bh-met-92c/94e chain, van der Waerden's stabilizer method) uses
`K₂(N, F_p) = 1`. For an infinite field that is false, and the torus `c ↦ h_mL(c)` is no
longer multiplicative. This module redoes the INDUCTION for an arbitrary field `F`, with every
conclusion "`= 1`" weakened to "is a constant, `∈ C(St(F))`". It isolates what remains as one
residual, the stabilizer statement `FieldStabAt F`.

Notation. `R = F[X]`, `K` a finset, `L ∉ K`. Inside `St_I(R)`:
* `S_K = ⟨x_ij(f) : i, j ∈ K⟩`;
* `V = ⟨x_Lj(f) : j ∈ K⟩`;
* `G = S_{K ∪ {L}}`;
* `Z = C(K₂(I, F))`, the constant `K₂`, which contains every symbol;
* `C = C(St_I(F))`, the constants.

* **Residual `FieldStabAt F`.** Assume `S_K ∩ K₂ ⊆ C` (the induction hypothesis). Then every
  `g ∈ G` fixing `e_L` is `z · s · v` with `z ∈ Z`, `s ∈ S_K` and `v ∈ V`. Over `F_p`, `Z = 1`,
  and this is the chain's `k2PolyNF_StabStatement`. Over a general field, the symbol factors that
  Euclid's algorithm produces land in `Z`.
* **Kernel lemma** `fn_mem_C_of_decomp`. Let `g = z s v ∈ K₂`. Then `s v ∈ K₂`, because
  `Z ≤ K₂`. Row `L` of `v` vanishes off the diagonal, so `v = 1`. Hence `s ∈ S_K ∩ K₂ ⊆ C`, and
  `g ∈ C`.
* **Induction** `fn_S_mem_C`: `S_K ∩ K₂ ⊆ C` for every `K`, from the residual.
* **Endpoint** `fieldConst_of_fieldStab`: the residual gives `k2PolyField_ConstStatement F N`
  for every `N ≥ 3`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan
  rootSpan_induction rootSpan_mono mem_rootSpan_true act unitVec unitVec_apply act_mul
  act_of_projection_eq_one act_apply_of_rootSpan act_eq_self_of_rootSpan
  eq_one_of_row_zero_finset)

section Defs

variable {I : Type} [Fintype I] [DecidableEq I] (F : Type) [Field F]

/-- `S_K = ⟨x_ij(f) : i, j ∈ K⟩ ≤ St_I(F[X])`. -/
noncomputable def fnS (K : Finset I) : Subgroup (SteinbergGroup I (Polynomial F)) :=
  rootSpan (R := Polynomial F) fun i j => i ∈ K ∧ j ∈ K

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fnS

/-- `V = ⟨x_Lj(f) : j ∈ K⟩ ≤ St_I(F[X])`. -/
noncomputable def fnV (K : Finset I) (L : I) : Subgroup (SteinbergGroup I (Polynomial F)) :=
  rootSpan (R := Polynomial F) fun i j => i = L ∧ j ∈ K

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fnV

/-- The constants `C(St_I(F)) ≤ St_I(F[X])`. -/
noncomputable def fnC : Subgroup (SteinbergGroup I (Polynomial F)) :=
  (ringMap (I := I) (Polynomial.C : F →+* Polynomial F)).range

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fnC

/-- The constant `K₂`: `Z = C(K₂(I, F)) ≤ St_I(F[X])`. -/
noncomputable def fnZ : Subgroup (SteinbergGroup I (Polynomial F)) :=
  (K2 I F).map (ringMap (I := I) (Polynomial.C : F →+* Polynomial F))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fnZ

end Defs

/-- **The residual (the stabilizer of `e_L`, up to constant `K₂`).**  Given the induction
hypothesis `S_K ∩ K₂ ⊆ C`, every `g ∈ S_{K ∪ {L}}` fixing `e_L` is `z (s v)` with `z ∈ Z`,
`s ∈ S_K` and `v ∈ V`. -/
def FieldStabAt (F : Type) [Field F] : Prop :=
  ∀ {I : Type} [Fintype I] [DecidableEq I] (K : Finset I) (L : I), L ∉ K → K.Nonempty →
    (∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k) →
    (∀ s ∈ fnS F K, s ∈ K2 I (Polynomial F) → s ∈ fnC F) →
    ∀ g ∈ fnS F (insert L K), act g (unitVec L) = unitVec L →
      ∃ z ∈ fnZ F, ∃ s ∈ fnS F K, ∃ v ∈ fnV F K L, z * (s * v) = g

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldStabAt

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

/-- The constant `K₂` lies in `K₂` and in the constants. -/
theorem fnZ_le_K2 : fnZ (I := I) F ≤ K2 I (Polynomial F) := by
  rintro _ ⟨k, hk, rfl⟩
  exact ringMap_mem_K2 _ hk

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fnZ_le_K2

theorem fnZ_le_C : fnZ (I := I) F ≤ fnC F := by
  rintro _ ⟨k, _, rfl⟩
  exact ⟨k, rfl⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fnZ_le_C

/-- **Kernel lemma.**  If `S_K ∩ K₂ ⊆ C` and `g = z (s v) ∈ K₂` with `z ∈ Z`, `s ∈ S_K` and
`v ∈ V`, then `g ∈ C`. -/
theorem fn_mem_C_of_decomp {K : Finset I} {L : I} (hLK : L ∉ K)
    (ih : ∀ s ∈ fnS F K, s ∈ K2 I (Polynomial F) → s ∈ fnC F)
    {z s v : SteinbergGroup I (Polynomial F)} (hz : z ∈ fnZ F) (hs : s ∈ fnS F K)
    (hv : v ∈ fnV F K L) (hK2 : z * (s * v) ∈ K2 I (Polynomial F)) : z * (s * v) ∈ fnC F := by
  have hsv : s * v ∈ K2 I (Polynomial F) := by
    have h := (K2 I (Polynomial F)).mul_mem ((K2 I (Polynomial F)).inv_mem (fnZ_le_K2 hz)) hK2
    rwa [inv_mul_cancel_left] at h
  have hproj := (mem_K2_iff _).mp hsv
  have hrow : ∀ k : I, k ≠ L → act v (unitVec k) L = 0 := fun k hk =>
    calc act v (unitVec k) L = act (s⁻¹ * (s * v)) (unitVec k) L := by
          rw [inv_mul_cancel_left]
      _ = act s⁻¹ (act (s * v) (unitVec k)) L := by rw [act_mul]
      _ = act s⁻¹ (unitVec k) L := by rw [act_of_projection_eq_one hproj]
      _ = unitVec k L :=
          act_apply_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (k := L)
            (fun _ _ hij e => hLK (e ▸ hij.1)) ((fnS F K).inv_mem hs) _
      _ = 0 := by rw [unitVec_apply, if_neg (Ne.symm hk)]
  have hv1 : v = 1 := eq_one_of_row_zero_finset L K hLK v hv hrow
  subst hv1
  rw [mul_one] at hsv ⊢
  exact (fnC F).mul_mem (fnZ_le_C hz) (ih s hs hsv)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fn_mem_C_of_decomp

/-- A root span with no roots (every root excluded) is trivial. -/
theorem fn_eq_one_of_no_roots {q : I → I → Prop} (hq : ∀ i j, i ≠ j → ¬ q i j)
    {g : SteinbergGroup I (Polynomial F)} (hg : g ∈ rootSpan (R := Polynomial F) q) : g = 1 :=
  rootSpan_induction (p := q) (Q := fun z => z = 1)
    (fun i j hij _ h => absurd h (hq i j hij)) rfl
    (fun a b _ _ ha hb => show a * b = 1 by rw [show a = 1 from ha, show b = 1 from hb, one_mul])
    hg

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fn_eq_one_of_no_roots

/-- **The induction.**  From the residual, `S_K ∩ K₂ ⊆ C` for every finset `K` (`|I| ≥ 3`). -/
theorem fn_S_mem_C (hS : FieldStabAt F) (hthird : ∀ a b : I, ∃ k, a ≠ k ∧ b ≠ k)
    (K : Finset I) : ∀ s ∈ fnS F K, s ∈ K2 I (Polynomial F) → s ∈ fnC F := by
  induction K using Finset.induction_on with
  | empty =>
    intro s hs _
    rw [fn_eq_one_of_no_roots (q := fun i j => i ∈ (∅ : Finset I) ∧ j ∈ (∅ : Finset I))
      (fun i _ _ h => Finset.notMem_empty i h.1) hs]
    exact (fnC F).one_mem
  | insert L K hLK ih =>
    intro s hs hK2
    rcases Finset.eq_empty_or_nonempty K with hK0 | hKne
    · subst hK0
      have key : ∀ k : I, k ∈ insert L (∅ : Finset I) → k = L := fun k hk =>
        (Finset.mem_insert.mp hk).resolve_right (Finset.notMem_empty k)
      rw [fn_eq_one_of_no_roots
        (q := fun i j => i ∈ insert L (∅ : Finset I) ∧ j ∈ insert L (∅ : Finset I))
        (fun i j hij h => hij ((key i h.1).trans (key j h.2).symm)) hs]
      exact (fnC F).one_mem
    · have hfix : act s (unitVec L) = unitVec L :=
        act_of_projection_eq_one ((mem_K2_iff s).mp hK2) (unitVec L)
      obtain ⟨z, hz, t, ht, v, hv, rfl⟩ := hS K L hLK hKne hthird ih s hs hfix
      exact fn_mem_C_of_decomp hLK ih hz ht hv hK2

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fn_S_mem_C

/-- **Endpoint.**  The residual gives `k2PolyField_ConstStatement F N` for every `N ≥ 3`. -/
theorem fieldConst_of_fieldStab (hS : FieldStabAt F) {N : ℕ} (hN : 3 ≤ N) :
    Metabelian.ElemFP.k2PolyField_ConstStatement F N := by
  intro g hg
  have hthird : ∀ a b : Fin N, ∃ k, a ≠ k ∧ b ≠ k :=
    Metabelian.ElemFP.FieldK2.bruhatBigCell_third (by rw [Fintype.card_fin]; omega)
  have hSK : g ∈ fnS F (Finset.univ : Finset (Fin N)) :=
    rootSpan_mono (p := fun _ _ : Fin N => True)
      (q := fun i j =>
        i ∈ (Finset.univ : Finset (Fin N)) ∧ j ∈ (Finset.univ : Finset (Fin N)))
      (fun i j _ _ => ⟨Finset.mem_univ i, Finset.mem_univ j⟩) (mem_rootSpan_true g)
  exact fn_S_mem_C hS hthird Finset.univ g hSK hg

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.fieldConst_of_fieldStab

end GroupApproximation.BooneHigmanLinear.K2Poly
