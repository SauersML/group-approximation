import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.Sigma
import GroupApproximation.BooneHigmanLinear.K2Poly.FieldTorusK2
import GroupApproximation.BooneHigman.Metabelian.ElemFPK2PolyNagaoWeylTorus
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: Euclidean algebra, the constant torus, and torus equivariance

k2-poly piece A5.2 (lane k2-field-a). The field port of lane 93d's `ElemFPK2PolyNagaoWeylAlg`,
`…WeylTorus` and `…WeylEquiv`. The ring-generic conjugation identities of
`ElemFPK2PolyNagaoWeylConj`, and the field identity `k2PolyNagaoWeyl_field_w_conj_h`, are reused
as they are. `t(γ) = fieldTorus F m L hmL γ = C(h_mL(γ))`, and `W = w_mL(-1)`.

* Division algebra in `F[X]`: `fnWeyl_divmod_unique`, `_neg_right`, `_neg_left`, `_scale`,
  `_small`, `fnWeyl_coprime_step`, and `fnWeyl_coprime_orbit` (for `K = {m}` every orbit vector
  has coprime `(m, L)` coordinates).
* Single torus elements, EXACT (no symbol factor): `fnWeyl_torus_eq`, `fnWeyl_torus_one`,
  `fnWeyl_W_conj_torus` (`W⁻¹ t(γ) W = t(γ⁻¹)`), `fnWeyl_W_mul_W` (`W W = t(-1)`),
  `fnWeyl_torus_mul_x` (`t(δ) x'(f) = x'(δ⁻¹ f δ⁻¹) t(δ)`), and `fnWeyl_tau_C` (`τ(C β) = t(β)⁻¹`).
* Products, up to the constant `K₂`: `fnWeyl_torus_mul_comm_mem`, `t(c') t(c) = z · t(c c')` with
  `z ∈ Z = fnZ F`.
* **`fnWeyl_torus_mul_pair`** (torus equivariance of the Euclidean word): for coprime `(a, b)`,
  `t(δ) · pair a b = pair (δ a) (δ⁻¹ b) · z` for some `z ∈ Z`. The factor is on the RIGHT, so the
  recursion step needs no centrality. Over `F_p` it is `1`.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnZ fieldTorus fieldTorus_apply
  fieldTorus_mul_mem)
open GroupApproximation.BooneHigman.Metabelian.ElemFP (k2PolyNagaoWeyl_isCoprime_of_comb
  k2PolyNagaoWeyl_h_conj k2PolyNagaoWeyl_field_w_conj_h k2PolyDeg_ringMap_w)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w h w_inv)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan_induction
  act act_mul act_one act_x_apply unitVec unitVec_apply)

section Alg

variable {F : Type} [Field F]

/-- Uniqueness of Euclidean division in `F[X]`. -/
theorem fnWeyl_divmod_unique {a b q r : Polynomial F} (ha : a ≠ 0)
    (h : b = a * q + r) (hr : r.degree < a.degree) : b / a = q ∧ b % a = r := by
  have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
  have hq : b / a = q := by
    by_contra hne
    have e : a * (b / a - q) = r - b % a := by linear_combination h1 + h
    have hd : a.degree ≤ (r - b % a).degree := by
      rw [← e]
      exact Polynomial.degree_le_mul_left a (sub_ne_zero.2 hne)
    have hlt : (r - b % a).degree < a.degree :=
      lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt hr (Polynomial.degree_mod_lt b ha))
    exact absurd hd (not_le.2 hlt)
  refine ⟨hq, ?_⟩
  rw [hq] at h1
  linear_combination h1 + h

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_divmod_unique

/-- `a / (-b) = -(a / b)` and `a % (-b) = a % b`. -/
theorem fnWeyl_divmod_neg_right (a : Polynomial F) {b : Polynomial F} (hb : b ≠ 0) :
    a / -b = -(a / b) ∧ a % -b = a % b := by
  have h1 : b * (a / b) + a % b = a := EuclideanDomain.div_add_mod a b
  refine fnWeyl_divmod_unique (neg_ne_zero.2 hb) (by linear_combination -h1) ?_
  rw [Polynomial.degree_neg]
  exact Polynomial.degree_mod_lt a hb

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_divmod_neg_right

/-- `(-a) / b = -(a / b)` and `(-a) % b = -(a % b)`. -/
theorem fnWeyl_divmod_neg_left (a : Polynomial F) {b : Polynomial F} (hb : b ≠ 0) :
    -a / b = -(a / b) ∧ -a % b = -(a % b) := by
  have h1 : b * (a / b) + a % b = a := EuclideanDomain.div_add_mod a b
  refine fnWeyl_divmod_unique hb (by linear_combination h1) ?_
  rw [Polynomial.degree_neg]
  exact Polynomial.degree_mod_lt a hb

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_divmod_neg_left

/-- Scaling the column `(a, b)` to `(δ a, δ⁻¹ b)` by a constant unit `δ`. -/
theorem fnWeyl_divmod_scale (δ : Fˣ) {a : Polynomial F} (ha : a ≠ 0) (b : Polynomial F) :
    (Polynomial.C ((δ⁻¹ : Fˣ) : F) * b) / (Polynomial.C (δ : F) * a) =
        Polynomial.C ((δ⁻¹ : Fˣ) : F) * Polynomial.C ((δ⁻¹ : Fˣ) : F) * (b / a) ∧
      (Polynomial.C ((δ⁻¹ : Fˣ) : F) * b) % (Polynomial.C (δ : F) * a) =
        Polynomial.C ((δ⁻¹ : Fˣ) : F) * (b % a) := by
  have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
  have hu : Polynomial.C (δ : F) * Polynomial.C ((δ⁻¹ : Fˣ) : F) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have ha' : Polynomial.C (δ : F) * a ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.2 δ.ne_zero) ha
  refine fnWeyl_divmod_unique ha' (by
    linear_combination -Polynomial.C ((δ⁻¹ : Fˣ) : F) * h1 -
      Polynomial.C ((δ⁻¹ : Fˣ) : F) * a * (b / a) * hu) ?_
  rw [Polynomial.degree_C_mul δ⁻¹.ne_zero, Polynomial.degree_C_mul δ.ne_zero]
  exact Polynomial.degree_mod_lt b ha

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_divmod_scale

/-- `deg b < deg a` gives `b / a = 0` and `b % a = b`. -/
theorem fnWeyl_divmod_small {a b : Polynomial F} (ha : a ≠ 0) (h : b.degree < a.degree) :
    b / a = 0 ∧ b % a = b :=
  fnWeyl_divmod_unique ha (by ring) h

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_divmod_small

/-- One Euclidean step keeps a coprime column coprime: `(a, b)` to `(b % a, -a)`. -/
theorem fnWeyl_coprime_step {a b : Polynomial F} (h : IsCoprime a b) :
    IsCoprime (b % a) (-a) := by
  have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
  exact k2PolyNagaoWeyl_isCoprime_of_comb h (x1 := 0) (y1 := -1) (x2 := 1) (y2 := -(b / a))
    (by ring) (by linear_combination -h1)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_coprime_step

variable {I : Type} [Fintype I] [DecidableEq I]

/-- For `K = {m}`, every element of `S_{K ∪ {L}}` preserves coprimality of the `(m, L)`
coordinates. -/
theorem fnWeyl_coprime_act {K : Finset I} {m L : I} (hmL : m ≠ L)
    (hKm : ∀ i ∈ K, i = m) {y : SteinbergGroup I (Polynomial F)}
    (hy : y ∈ fnS F (insert L K)) :
    ∀ v : I → Polynomial F, IsCoprime (v m) (v L) → IsCoprime (act y v m) (act y v L) := by
  unfold GroupApproximation.BooneHigmanLinear.K2Poly.fnS at hy
  refine rootSpan_induction (Q := fun y => ∀ v : I → Polynomial F,
    IsCoprime (v m) (v L) → IsCoprime (act y v m) (act y v L)) ?_ ?_ ?_ hy
  · intro i j hij a hq v hv
    have hi : i = L ∨ i = m := (Finset.mem_insert.1 hq.1).imp id (hKm i)
    have hj : j = L ∨ j = m := (Finset.mem_insert.1 hq.2).imp id (hKm j)
    rw [act_x_apply, act_x_apply]
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · exact absurd (hi.trans hj.symm) hij
    · rw [if_neg (fun h : m = i => hmL (h.trans hi)), if_pos hi.symm, hj, add_zero]
      exact k2PolyNagaoWeyl_isCoprime_of_comb hv (x1 := 1) (y1 := 0) (x2 := -a) (y2 := 1)
        (by ring) (by ring)
    · rw [if_pos hi.symm, if_neg (fun h : L = i => hmL (h.trans hi).symm), hj, add_zero]
      exact k2PolyNagaoWeyl_isCoprime_of_comb hv (x1 := 1) (y1 := -a) (x2 := 0) (y2 := 1)
        (by ring) (by ring)
    · exact absurd (hi.trans hj.symm) hij
  · intro v hv
    rw [act_one]
    exact hv
  · intro g k _ _ hg hk v hv
    rw [act_mul]
    exact hg _ (hk v hv)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_coprime_act

/-- Every vector of the orbit of `e_L` (`K = {m}`) has coprime `(m, L)` coordinates. -/
theorem fnWeyl_coprime_orbit {K : Finset I} {m L : I} (hmL : m ≠ L)
    (hKm : ∀ i ∈ K, i = m) {v : I → Polynomial F}
    (hv : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) : IsCoprime (v m) (v L) := by
  obtain ⟨y, hy, rfl⟩ := hv
  refine fnWeyl_coprime_act hmL hKm hy (unitVec L) ?_
  rw [unitVec_apply, unitVec_apply, if_neg hmL, if_pos rfl]
  exact isCoprime_one_right

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_coprime_orbit

end Alg

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F] {m L n : I}

/-- `C` sends the unit `-1` to `-1`. -/
theorem fnWeyl_units_map_neg_one :
    Units.map (Polynomial.C : F →+* Polynomial F).toMonoidHom (-1) = -1 :=
  Units.ext (show Polynomial.C (-(1 : F)) = -(1 : Polynomial F) by rw [map_neg, map_one])

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_units_map_neg_one

/-- Every unit of `F[X]` is a constant `C β`. -/
theorem fnWeyl_exists_C_of_isUnit {b : Polynomial F} (hb : IsUnit b) :
    ∃ β : Fˣ, b = Polynomial.C (β : F) := by
  obtain ⟨r, hr, hrb⟩ := Polynomial.isUnit_iff.1 hb
  exact ⟨hr.unit, by rw [hr.unit_spec, hrb]⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_exists_C_of_isUnit

/-- The torus is `C ∘ h_mL` on the nose. -/
theorem fnWeyl_torus_eq (hmL : m ≠ L) (γ : Fˣ) :
    fieldTorus F m L hmL γ = ringMap (Polynomial.C : F →+* Polynomial F) (h m L hmL γ) := rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_torus_eq

/-- `t(1) = 1`. -/
theorem fnWeyl_torus_one (hmL : m ≠ L) : fieldTorus (I := I) F m L hmL 1 = 1 := by
  have e : h m L hmL (1 : Fˣ) = 1 := by
    rw [show h m L hmL (1 : Fˣ) = w m L hmL (1 : Fˣ) * w m L hmL (-1 : Fˣ) from rfl,
      ← w_inv, mul_inv_cancel]
  rw [fnWeyl_torus_eq, e, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_torus_one

/-- `W⁻¹ t(γ) W = t(γ⁻¹)`: EXACT over any field. -/
theorem fnWeyl_W_conj_torus (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) (γ : Fˣ) :
    (w m L hmL (-1 : (Polynomial F)ˣ))⁻¹ * fieldTorus F m L hmL γ *
      w m L hmL (-1 : (Polynomial F)ˣ) = fieldTorus F m L hmL γ⁻¹ := by
  have hW : ringMap (Polynomial.C : F →+* Polynomial F) (w m L hmL (1 : Fˣ)) =
      (w m L hmL (-1 : (Polynomial F)ˣ))⁻¹ := by
    rw [k2PolyDeg_ringMap_w, map_one, w_inv, neg_neg]
  have hW' : w m L hmL (-1 : (Polynomial F)ˣ) =
      (ringMap (Polynomial.C : F →+* Polynomial F) (w m L hmL (1 : Fˣ)))⁻¹ := by
    rw [hW, inv_inv]
  rw [fnWeyl_torus_eq, fnWeyl_torus_eq, ← hW, hW', ← map_inv, ← map_mul, ← map_mul,
    k2PolyNagaoWeyl_field_w_conj_h m L n hmL hmn hLn γ]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_W_conj_torus

/-- `W W = t(-1)`. -/
theorem fnWeyl_W_mul_W (hmL : m ≠ L) :
    w m L hmL (-1 : (Polynomial F)ˣ) * w m L hmL (-1 : (Polynomial F)ˣ) =
      fieldTorus (I := I) F m L hmL (-1) := by
  rw [fieldTorus_apply, fnWeyl_units_map_neg_one]
  rfl

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_W_mul_W

/-- `t(δ) x'(f) = x'(δ⁻¹ f δ⁻¹) t(δ)`. -/
theorem fnWeyl_torus_mul_x (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) (δ : Fˣ)
    (f : Polynomial F) :
    fieldTorus F m L hmL δ * x L m hmL.symm f =
      x L m hmL.symm (Polynomial.C ((δ⁻¹ : Fˣ) : F) * f * Polynomial.C ((δ⁻¹ : Fˣ) : F)) *
        fieldTorus F m L hmL δ := by
  have e : fieldTorus F m L hmL δ * x L m hmL.symm f * (fieldTorus F m L hmL δ)⁻¹ =
      x L m hmL.symm (Polynomial.C ((δ⁻¹ : Fˣ) : F) * f * Polynomial.C ((δ⁻¹ : Fˣ) : F)) := by
    rw [fieldTorus_apply]
    exact k2PolyNagaoWeyl_h_conj hmL hmn hLn _ f
  rw [← e]
  group

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_torus_mul_x

/-- `τ(C β) = t(β)⁻¹`. -/
theorem fnWeyl_tau_C (hmL : m ≠ L) (β : Fˣ) :
    fnSigma_tau F m L hmL (Polynomial.C (β : F)) = (fieldTorus (I := I) F m L hmL β)⁻¹ := by
  by_cases h1 : Polynomial.C (β : F) = 1
  · have hβ : β = 1 := Units.ext (Polynomial.C_injective (h1.trans Polynomial.C_1.symm))
    rw [fnSigma_tau, if_pos h1, hβ, fnWeyl_torus_one hmL, inv_one]
  · have hu : IsUnit (Polynomial.C (β : F)) := β.isUnit.map Polynomial.C
    have e : hu.unit = Units.map (Polynomial.C : F →+* Polynomial F).toMonoidHom β :=
      Units.ext hu.unit_spec
    rw [fnSigma_tau, if_neg h1, dif_pos hu, fieldTorus_apply, e]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_tau_C

/-- **Products up to the constant `K₂`.** `t(c') t(c) = z · t(c c')` with `z ∈ Z`. -/
theorem fnWeyl_torus_mul_comm_mem (hmL : m ≠ L) (c c' : Fˣ) :
    ∃ z ∈ fnZ (I := I) F,
      fieldTorus F m L hmL c' * fieldTorus F m L hmL c = z * fieldTorus F m L hmL (c * c') := by
  obtain ⟨z, hz, e⟩ := fieldTorus_mul_mem (I := I) (F := F) m L hmL c c'
  exact ⟨z⁻¹, Subgroup.inv_mem (fnZ F) hz, by rw [e]; group⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_torus_mul_comm_mem

/-- **Torus equivariance, up to the constant `K₂` on the right.** For a coprime column `(a, b)`
and `δ ∈ Fˣ`, `t(δ) · pair a b = pair (δ a) (δ⁻¹ b) · z` for some `z ∈ Z`. -/
theorem fnWeyl_torus_mul_pair (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) (a : Polynomial F) :
    ∀ (δ : Fˣ) (b : Polynomial F), IsCoprime a b →
      ∃ z ∈ fnZ (I := I) F,
        fieldTorus F m L hmL δ * fnSigma_pair F m L hmL a b =
          fnSigma_pair F m L hmL (Polynomial.C (δ : F) * a)
            (Polynomial.C ((δ⁻¹ : Fˣ) : F) * b) * z := by
  induction a using (Polynomial.degree_lt_wf (R := F)).induction with
  | _ a ih =>
    intro δ b hab
    by_cases ha : a = 0
    · subst ha
      obtain ⟨β, rfl⟩ := fnWeyl_exists_C_of_isUnit (isCoprime_zero_left.1 hab)
      rw [mul_zero (Polynomial.C (δ : F)), fnSigma_pair_zero, fnSigma_pair_zero,
        ← map_mul Polynomial.C, ← Units.val_mul, fnWeyl_tau_C hmL, fnWeyl_tau_C hmL]
      obtain ⟨s, hs, hm⟩ := fieldTorus_mul_mem (I := I) (F := F) m L hmL δ (δ⁻¹ * β)
      rw [mul_inv_cancel_left] at hm
      exact ⟨s⁻¹, Subgroup.inv_mem (fnZ F) hs, by rw [hm]; group⟩
    · have hCa : Polynomial.C (δ : F) * a ≠ 0 :=
        mul_ne_zero (Polynomial.C_ne_zero.2 δ.ne_zero) ha
      obtain ⟨hq, hr⟩ := fnWeyl_divmod_scale δ ha b
      obtain ⟨z, hz, hih⟩ := ih (b % a) (Polynomial.degree_mod_lt b ha) δ⁻¹ (-a)
        (fnWeyl_coprime_step hab)
      refine ⟨z, hz, ?_⟩
      have key : ∀ T X X' V P : SteinbergGroup I (Polynomial F), T * X = X' * T →
          T * (X * V * P) = X' * V * (V⁻¹ * T * V * P) := by
        intro T X X' V P hTX
        calc T * (X * V * P) = T * X * V * P := by group
          _ = X' * T * V * P := by rw [hTX]
          _ = X' * V * (V⁻¹ * T * V * P) := by group
      rw [fnSigma_pair_of_ne m L hmL ha, fnSigma_pair_of_ne m L hmL hCa,
        hq, hr, key _ _ _ _ _ (fnWeyl_torus_mul_x hmL hmn hLn δ (b / a)),
        fnWeyl_W_conj_torus hmL hmn hLn δ, hih, inv_inv, mul_neg,
        mul_right_comm (Polynomial.C ((δ⁻¹ : Fˣ) : F)) (b / a)]
      simp only [mul_assoc]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_torus_mul_pair

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
