import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegAmalgam
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyDegKernel
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2DilateProj
import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatAct
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyAmalPushout
import GroupApproximation.Manuscript.SimpleKazhdanSofic.SkRows.SteinbergWeyl.Projection
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwoAction
import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Meta.AxiomGuard

/-!
# `k2PolyDeg_AmalgamStatement` is FALSE (for `|K| ≥ 2`)

Lane `bh-met-91r`.  Notation of `ElemFPK2PolyDegSpans`; bars denote images under
`projection : St_I(F_p[X]) → E_I(F_p[X])`.  Endpoint: `k2PolyAmal_not_amalgamStatement`.

**Truth check (paper): the target is false.**  Take `k, m ∈ K` with `k ≠ m` and `L ∉ K`.
Steinberg relation (C1) (`conj_x_left k L m`) gives
`x_kL(1) x_Lm(X) x_kL(1)⁻¹ = x_km(X) x_Lm(X)`.  Put
* `a = x̄_kL(1)`: it lies in `Ā` (a constant), but not in `P̄`: every element of `P̄` sends `e_L`
  to a multiple of `e_L`, while `a e_L = e_L + e_k`;
* `g = x̄_Lm(X)`: it lies in `P̄` (via `V`), but not in `Ā`: its `(L, m)` entry is `X`;
* `s = x̄_km(X) x̄_Lm(X) ∈ P̄` (via `S` and `V`).

All three lie in `Ḡ`, and `a g a⁻¹ = s`.  So in `Ā *_{Ā ∩ P̄} P̄` the word `a · g · a⁻¹ · s⁻¹` is
reduced of length 4 and hence not `1` (`k2PolyAmal_no_extension`).  Taking `H` to be this
pushout, `φ₁, φ₂` the canonical maps, no `Φ` exists.  The smallest instance is `p = 2`,
`I = Fin 3`, `K = {0, 1}`, `m = 0`, `L = 2`, `n = 1`, `k = 1`.

The same computation refutes the folklore claim `SL_n(k[t]) = SL_n(k) *_{B(k)} B(k[t])` for
`n ≥ 3`.  Soulé's theorem is a colimit over all face stabilisers of a sector, not a two-group
amalgam.  Only the case `|K| = 1` (Nagao, rank 2) has the amalgam form, and the `bh-met-91c`
induction needs every `K`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigman.SteinbergBasic
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (conj_x_left projection_x_val)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act unitVec
  unitVec_apply act_mul act_x_apply act_eq_self_of_rootSpan x_mem_rootSpan)

/-- The action depends only on the projection. -/
theorem k2PolyAmal_act_congr {J R : Type*} [Fintype J] [DecidableEq J] [Ring R]
    {g g' : SteinbergGroup J R} (hgg : projection g = projection g') (v : J → R) :
    act g v = act g' v := by
  simp only [act, hgg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_act_congr

variable {I : Type} [Fintype I] [DecidableEq I] {p : ℕ} [Fact p.Prime]

/-- `a = x̄_kL(1)` is a constant. -/
theorem k2PolyAmal_a_mem {K : Finset I} {k L : I} (hkL : k ≠ L) (hkK : k ∈ K) :
    projection (x k L hkL (Polynomial.C (1 : ZMod p))) ∈ (k2PolyDeg_A p K L).map projection :=
  Subgroup.mem_map_of_mem projection (Subgroup.mem_map.mpr ⟨x k L hkL 1,
    x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K) hkL 1
      ⟨Finset.mem_insert_of_mem hkK, Finset.mem_insert_self L K⟩, ringMap_x _ _ _ _ _⟩)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_a_mem

/-- `a = x̄_kL(1)` is not in `P̄`: it moves `e_L` off the line `R e_L`. -/
theorem k2PolyAmal_a_not_mem {K : Finset I} {m L n k : I} (hmL : m ≠ L) (hmn : m ≠ n)
    (hLn : L ≠ n) (hLK : L ∉ K) (hkL : k ≠ L) :
    projection (x k L hkL (Polynomial.C (1 : ZMod p))) ∉
      (k2PolyDeg_P p K m L n hmL hmn hLn).map projection := by
  intro hmem
  obtain ⟨g, hg, hproj⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨c, s, hs, v, hv, rfl⟩ := k2PolyDeg_P_decomp hmL hmn hLn hLK hg
  have hfix : ∀ j : I, j ∈ K → unitVec (R := Polynomial (ZMod p)) L j = 0 := fun j hj => by
    rw [unitVec_apply, if_neg (fun e => hLK (e ▸ hj))]
  have hS : act s (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (fun _ j hij => hfix j hij.2) hs
  have hV : act v (unitVec L) = unitVec L :=
    act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K) (fun _ j hij => hfix j hij.2) hv
  have e := congrFun (k2PolyAmal_act_congr hproj (unitVec L)) k
  rw [act_mul, act_mul, hV, hS, k2PolyDeg_torus_apply, FieldK2.bruhat_act_h_unitVec,
    act_x_apply] at e
  simp [unitVec_apply, hkL] at e

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_a_not_mem

/-- `g = x̄_Lm(X)` is not a constant: its `(L, m)` entry is `X`. -/
theorem k2PolyAmal_g_not_mem {K : Finset I} {L m : I} (hLm : L ≠ m) :
    projection (x L m hLm (Polynomial.X : Polynomial (ZMod p))) ∉
      (k2PolyDeg_A p K L).map projection := by
  intro hmem
  obtain ⟨w, hw, hwe⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hw
  have e : ((projection (ringMap (Polynomial.C : ZMod p →+* Polynomial (ZMod p)) y) :
      (Matrix I I (Polynomial (ZMod p)))ˣ) : Matrix I I (Polynomial (ZMod p))) L m =
      ((projection (x L m hLm (Polynomial.X : Polynomial (ZMod p))) :
      (Matrix I I (Polynomial (ZMod p)))ˣ) : Matrix I I (Polynomial (ZMod p))) L m := by
    rw [hwe]
  rw [k2Dilate_coe_projection_ringMap, projection_x_val, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.add_apply, Matrix.one_apply_ne hLm, Matrix.single_apply_same,
    zero_add] at e
  exact Polynomial.X_ne_C _ e.symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_g_not_mem

/-- `g = x̄_Lm(X) ∈ P̄` (via `V`). -/
theorem k2PolyAmal_g_mem_P {K : Finset I} {m L n : I} (hmL : m ≠ L) (hmn : m ≠ n)
    (hLn : L ≠ n) (hmK : m ∈ K) :
    projection (x L m hmL.symm (Polynomial.X : Polynomial (ZMod p))) ∈
      (k2PolyDeg_P p K m L n hmL hmn hLn).map projection := by
  refine Subgroup.mem_map_of_mem _ ?_
  unfold k2PolyDeg_P
  exact Subgroup.mem_sup_right (Subgroup.mem_sup_right
    (x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K) hmL.symm _ ⟨rfl, hmK⟩))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_g_mem_P

/-- `s = x̄_km(X) x̄_Lm(X) ∈ P̄` (via `S` and `V`). -/
theorem k2PolyAmal_s_mem_P {K : Finset I} {m L n k : I} (hmL : m ≠ L) (hmn : m ≠ n)
    (hLn : L ≠ n) (hmK : m ∈ K) (hkK : k ∈ K) (hkm : k ≠ m) :
    projection (x k m hkm (Polynomial.C (1 : ZMod p) * Polynomial.X) *
        x L m hmL.symm Polynomial.X) ∈ (k2PolyDeg_P p K m L n hmL hmn hLn).map projection := by
  refine Subgroup.mem_map_of_mem _ ?_
  unfold k2PolyDeg_P
  exact Subgroup.mem_sup_right (Subgroup.mul_mem _
    (Subgroup.mem_sup_left (x_mem_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) hkm _ ⟨hkK, hmK⟩))
    (Subgroup.mem_sup_right
      (x_mem_rootSpan (p := fun i j => i = L ∧ j ∈ K) hmL.symm _ ⟨rfl, hmK⟩)))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_s_mem_P

/-- `a, g, s ∈ Ḡ`. -/
theorem k2PolyAmal_mem_G {K : Finset I} {m L k : I} (hmL : m ≠ L) (hmK : m ∈ K) (hkK : k ∈ K)
    (hkm : k ≠ m) (hkL : k ≠ L) :
    projection (x k L hkL (Polynomial.C (1 : ZMod p))) ∈ (k2PolyDeg_G p K L).map projection ∧
      projection (x L m hmL.symm (Polynomial.X : Polynomial (ZMod p))) ∈
        (k2PolyDeg_G p K L).map projection ∧
      projection (x k m hkm (Polynomial.C (1 : ZMod p) * Polynomial.X) *
        x L m hmL.symm Polynomial.X) ∈ (k2PolyDeg_G p K L).map projection := by
  have hL : L ∈ insert L K := Finset.mem_insert_self L K
  have hm : m ∈ insert L K := Finset.mem_insert_of_mem hmK
  have hk : k ∈ insert L K := Finset.mem_insert_of_mem hkK
  have hxLm : x L m hmL.symm (Polynomial.X : Polynomial (ZMod p)) ∈ k2PolyDeg_G p K L :=
    x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K) hmL.symm _ ⟨hL, hm⟩
  refine ⟨Subgroup.mem_map_of_mem _ ?_, Subgroup.mem_map_of_mem _ hxLm,
    Subgroup.mem_map_of_mem _ (Subgroup.mul_mem _ ?_ hxLm)⟩
  · exact x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K) hkL _ ⟨hk, hL⟩
  · exact x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K) hkm _ ⟨hk, hm⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_mem_G

omit [Fact p.Prime] in
/-- Relation (C1): `a g a⁻¹ = s`. -/
theorem k2PolyAmal_rel {k L m : I} (hkL : k ≠ L) (hLm : L ≠ m) (hkm : k ≠ m) :
    projection (x k L hkL (Polynomial.C (1 : ZMod p))) *
        projection (x L m hLm (Polynomial.X : Polynomial (ZMod p))) *
        (projection (x k L hkL (Polynomial.C (1 : ZMod p))))⁻¹ =
      projection (x k m hkm (Polynomial.C (1 : ZMod p) * Polynomial.X) *
        x L m hLm Polynomial.X) := by
  rw [← conj_x_left k L m hkL hLm hkm, map_mul, map_mul, map_inv]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_rel

include p in
/-- **The amalgam statement fails as soon as `K` has two elements `k ≠ m`.** -/
theorem k2PolyAmal_false_of_two (hAm : k2PolyDeg_AmalgamStatement) (K : Finset I)
    (m L n k : I) (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) (hLK : L ∉ K) (hmK : m ∈ K)
    (hkK : k ∈ K) (hkm : k ≠ m) : False := by
  have hkL : k ≠ L := fun e => hLK (e ▸ hkK)
  obtain ⟨Φ, hΦ₁, hΦ₂⟩ := hAm p K m L n hmL hmn hLn hLK hmK
    (Monoid.PushoutI (k2PolyAmal_incl ((k2PolyDeg_A p K L).map projection)
      ((k2PolyDeg_P p K m L n hmL hmn hLn).map projection)))
    (Monoid.PushoutI.of (φ := k2PolyAmal_incl ((k2PolyDeg_A p K L).map projection)
      ((k2PolyDeg_P p K m L n hmL hmn hLn).map projection)) true)
    (Monoid.PushoutI.of (φ := k2PolyAmal_incl ((k2PolyDeg_A p K L).map projection)
      ((k2PolyDeg_P p K m L n hmL hmn hLn).map projection)) false)
    (fun z h₁ h₂ => k2PolyAmal_compat _ _ z h₁ h₂)
  obtain ⟨haG, hgG, hsG⟩ := k2PolyAmal_mem_G (p := p) hmL hmK hkK hkm hkL
  exact k2PolyAmal_no_extension ((k2PolyDeg_A p K L).map projection)
    ((k2PolyDeg_P p K m L n hmL hmn hLn).map projection) ((k2PolyDeg_G p K L).map projection)
    (k2PolyAmal_a_mem hkL hkK) (k2PolyAmal_a_not_mem hmL hmn hLn hLK hkL)
    (k2PolyAmal_g_mem_P hmL hmn hLn hmK) (k2PolyAmal_g_not_mem hmL.symm)
    (k2PolyAmal_s_mem_P hmL hmn hLn hmK hkK hkm) (k2PolyAmal_rel hkL hmL.symm hkm)
    haG hgG hsG Φ (fun z h₁ h => hΦ₁ z h₁ h) (fun z h₂ h => hΦ₂ z h₂ h)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_false_of_two

/-- **Endpoint.**  `k2PolyDeg_AmalgamStatement` is false: it fails for `p = 2`, `I = Fin 3`,
`K = {0, 1}`, `m = 0`, `L = 2`, `n = 1` (witness `k = 1`). -/
theorem k2PolyAmal_not_amalgamStatement : ¬ k2PolyDeg_AmalgamStatement := fun hAm =>
  k2PolyAmal_false_of_two (p := 2) (I := Fin 3) hAm {0, 1} 0 2 1 1 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.k2PolyAmal_not_amalgamStatement

end GroupApproximation.BooneHigman.Metabelian.ElemFP
