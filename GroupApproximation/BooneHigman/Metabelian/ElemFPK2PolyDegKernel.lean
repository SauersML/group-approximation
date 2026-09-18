import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegSpans
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatAct
import GroupApproximation.BooneHigman.SteinbergBasic.Kernel
import GroupApproximation.Meta.AxiomGuard

/-!
# Degree reduction for `K₂(F_p[X])`, part 3: the parabolic meets `K₂` trivially

Lane `bh-met-91c`.  Notation of `ElemFPK2PolyDegSpans`.  Main result
(`k2PolyDeg_eq_one_of_mem_P`): if `S ∩ K₂ = 1` (the induction hypothesis on the Levi block),
then `P ∩ K₂ = 1`.

Truth check (paper).  By `k2PolyDeg_P_decomp` write `g = t s v`, where `t = h_mL(C c)`,
`s ∈ S` and `v ∈ V`.  Both `S` and `V` fix `e_L`, because their generating roots have column in
`K ∌ L`.  So `g e_L = t e_L = c⁻¹ e_L`, and `g ∈ K₂` forces `c = 1`.  Then `s v ∈ K₂`, so
`v e_k = s⁻¹ e_k` for every `k`.  Row `L` of that vector is `(e_k)_L`, since `S` has no root
with row `L`, and this is `0` for `k ≠ L`.  Hence row `L` of `v` is trivial off the diagonal,
and `v = 1` by the corpus lemma `FieldTwo.eq_one_of_row_zero_finset`.  Finally `s ∈ S ∩ K₂`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open scoped Pointwise
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act unitVec
  unitVec_apply act_mul act_of_projection_eq_one act_apply_of_rootSpan act_eq_self_of_rootSpan
  eq_one_of_row_zero_finset)

/-- Conjugation distributes over a product of two elements. -/
theorem k2PolyDeg_conj_mul {G : Type*} [Group G] (t s v : G) :
    t * (s * v) * t⁻¹ = t * s * t⁻¹ * (t * v * t⁻¹) := by
  group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_conj_mul

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- The torus normalizes `S ⊔ V`. -/
theorem k2PolyDeg_torus_le_normalizer_SV {K : Finset I} {m L n : I} (hmL : m ≠ L)
    (hmn : m ≠ n) (hLn : L ≠ n) (hLK : L ∉ K) :
    (k2PolyDeg_torus p m L n hmL hmn hLn).range ≤ Subgroup.normalizer
      ((k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L :
        Subgroup (SteinbergGroup I (Polynomial (ZMod p)))) :
          Set (SteinbergGroup I (Polynomial (ZMod p)))) := by
  refine k2PolyDeg_le_normalizer fun t ht y hy => ?_
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp ht
  obtain ⟨s, hs, v, hv, rfl⟩ := k2PolyDeg_SV_decomp hLK hy
  rw [k2PolyDeg_conj_mul]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (k2PolyDeg_torus_conj_rootSpan m L n hmL hmn hLn
      (fun i j => i ∈ K ∧ j ∈ K) c hs))
    (Subgroup.mem_sup_right (k2PolyDeg_torus_conj_rootSpan m L n hmL hmn hLn
      (fun i j => i = L ∧ j ∈ K) c hv))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_torus_le_normalizer_SV

/-- Every element of `P` is `t (s v)` with `t` in the torus, `s ∈ S` and `v ∈ V`. -/
theorem k2PolyDeg_P_decomp {K : Finset I} {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n)
    (hLn : L ≠ n) (hLK : L ∉ K) {g : SteinbergGroup I (Polynomial (ZMod p))}
    (hg : g ∈ k2PolyDeg_P p K m L n hmL hmn hLn) :
    ∃ c : (ZMod p)ˣ, ∃ s ∈ k2PolyDeg_S p K, ∃ v ∈ k2PolyDeg_V p K L,
      k2PolyDeg_torus p m L n hmL hmn hLn c * (s * v) = g := by
  have hg' : g ∈ ((k2PolyDeg_torus p m L n hmL hmn hLn).range :
      Set (SteinbergGroup I (Polynomial (ZMod p)))) *
      ((k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L :
        Subgroup (SteinbergGroup I (Polynomial (ZMod p)))) :
          Set (SteinbergGroup I (Polynomial (ZMod p)))) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (k2PolyDeg_torus_le_normalizer_SV hmL hmn hLn hLK)]
    exact hg
  obtain ⟨t, ht, y, hy, rfl⟩ := Set.mem_mul.mp hg'
  obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp
    (show t ∈ (k2PolyDeg_torus p m L n hmL hmn hLn).range from ht)
  obtain ⟨s, hs, v, hv, rfl⟩ := k2PolyDeg_SV_decomp hLK
    (show y ∈ k2PolyDeg_S p K ⊔ k2PolyDeg_V p K L from hy)
  exact ⟨c, s, hs, v, hv, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_P_decomp

/-- **Kernel lemma.** If `S ∩ K₂ = 1`, then `P ∩ K₂ = 1`. -/
theorem k2PolyDeg_eq_one_of_mem_P {K : Finset I} {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n)
    (hLn : L ≠ n) (hLK : L ∉ K)
    (ih : ∀ s ∈ k2PolyDeg_S p K, s ∈ K2 I (Polynomial (ZMod p)) → s = 1)
    {g : SteinbergGroup I (Polynomial (ZMod p))} (hg : g ∈ k2PolyDeg_P p K m L n hmL hmn hLn)
    (hK2 : g ∈ K2 I (Polynomial (ZMod p))) : g = 1 := by
  obtain ⟨c, s, hs, v, hv, rfl⟩ := k2PolyDeg_P_decomp hmL hmn hLn hLK hg
  have hproj := (mem_K2_iff _).mp hK2
  have hfix : ∀ j : I, j ∈ K → unitVec (R := Polynomial (ZMod p)) L j = 0 := fun j hj => by
    rw [unitVec_apply, if_neg (fun e => hLK (e ▸ hj))]
  have hS : act s (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (fun _ j hij => hfix j hij.2) hs
  have hV : act v (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K) (fun _ j hij => hfix j hij.2) hv
  have e := congrFun (act_of_projection_eq_one hproj (unitVec L)) L
  rw [act_mul, act_mul, hV, hS, k2PolyDeg_torus_apply, FieldK2.bruhat_act_h_unitVec,
    if_pos rfl, unitVec_apply, if_pos rfl] at e
  have e' : (Polynomial.C : ZMod p →+* Polynomial (ZMod p)) ((c⁻¹ : (ZMod p)ˣ) : ZMod p) =
      Polynomial.C 1 := by
    rw [map_one]
    exact e
  have hc : c = 1 :=
    inv_eq_one.mp (Units.ext (by rw [Units.val_one]; exact Polynomial.C_injective e'))
  subst hc
  have ht : k2PolyDeg_torus p m L n hmL hmn hLn 1 = 1 := map_one _
  rw [ht, one_mul] at hproj
  have hrow : ∀ k : I, k ≠ L → act v (unitVec k) L = 0 := fun k hk =>
    calc act v (unitVec k) L = act (s⁻¹ * (s * v)) (unitVec k) L := by
          rw [inv_mul_cancel_left]
      _ = act s⁻¹ (act (s * v) (unitVec k)) L := by rw [act_mul]
      _ = act s⁻¹ (unitVec k) L := by rw [act_of_projection_eq_one hproj]
      _ = unitVec k L :=
          act_apply_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (k := L)
            (fun _ _ hij e => hLK (e ▸ hij.1)) ((k2PolyDeg_S p K).inv_mem hs) _
      _ = 0 := by rw [unitVec_apply, if_neg (Ne.symm hk)]
  have hv1 : v = 1 := eq_one_of_row_zero_finset L K hLK v hv hrow
  subst hv1
  rw [ht, one_mul, mul_one]
  rw [mul_one] at hproj
  exact ih s hs ((mem_K2_iff s).mpr hproj)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyDeg_eq_one_of_mem_P

end GroupApproximation.BooneHigman.Metabelian.ElemFP
