import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WeylTorus
import GroupApproximation.Meta.AxiomGuard

/-!
# `K₂(N, F[X])` over a field: the Weyl check of `σ`, and the rank-one case outright

k2-poly piece A5.2 (lane k2-field-a). The field port of lane 93d's `ElemFPK2PolyNagaoWeylLt`,
`…WeylTail`, `…WeylEq` and `…WeylMain`, and of lane 92q's `k2PolyNagaoSigma_gens_of_weyl`.
Notation of `FieldNF.WeylTorus`. For `v = (a, b)` on the `(m, L)` coordinates, `W v = (-b, a)`,
and the Weyl check element at `v` is `D(a, b) = (pair (-b) a)⁻¹ · W · pair a b`.

Over `F_p` the cases `b = 0` and `deg b < deg a` give `D = 1`. Over a field they give
`D ∈ Z = fnZ F`, the constant `K₂`: the torus products and torus equivariance now carry a
symbol. The case `deg b = deg a` gives `D ∈ Z ⊔ Q = fnZQ F K L`, as before with `Q` replaced by
`Z ⊔ Q`.

* `fnWeyl_check_pair_zero`, `fnWeyl_check_pair_lt`: `D ∈ Z`.
* `fnWeyl_eq_tail_ne`, `fnWeyl_eq_tail_zero`, `fnWeyl_check_pair_eq`: the case `deg b = deg a`.
* `fnWeyl_check_pair`, `fnWeyl_check_W`: `D ∈ Z ⊔ Q` whenever `deg v L ≤ deg v m`.
* **`fnWeyl_genGood_rankOne`**: for `K = {m}`, the explicit Euclidean section is good on the
  whole small generating set (`fnGenGood`). With `fn_coset_of_gen` this is the rank-one case of
  `FieldCosetAt F`, OUTRIGHT, over every field.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS fnZ fieldTorus fieldTorus_apply)
open GroupApproximation.BooneHigman.Metabelian.ElemFP (k2PolyNagaoWeyl_isCoprime_of_comb
  k2PolyNagaoWeyl_middle k2PolyNagaoSigma_act_W k2PolyDeg_w_conj_self_symm_eq)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (x_mem_rootSpan act
  unitVec)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F] {m L n : I}

/-- `Z ≤ Z ⊔ Q`. -/
theorem fn_mem_ZQ_of_mem_Z {K : Finset I} {g : SteinbergGroup I (Polynomial F)}
    (hg : g ∈ fnZ F) : g ∈ fnZQ F K L :=
  Subgroup.mem_sup_left hg

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fn_mem_ZQ_of_mem_Z

/-- `C(-1) = -1`. -/
theorem fnWeyl_C_neg_one : Polynomial.C ((-1 : Fˣ) : F) = -1 := by
  rw [Units.val_neg, Units.val_one, map_neg, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_C_neg_one

/-- `C((-1)⁻¹) = -1`. -/
theorem fnWeyl_C_inv_neg_one : Polynomial.C (((-1 : Fˣ)⁻¹ : Fˣ) : F) = -1 := by
  rw [inv_neg, inv_one, Units.val_neg, Units.val_one, map_neg, map_one]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_C_inv_neg_one

/-- `W W = t(-1)` commutes with every `x'(f)`. -/
theorem fnWeyl_WW_comm (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) (f : Polynomial F) :
    w m L hmL (-1 : (Polynomial F)ˣ) * w m L hmL (-1 : (Polynomial F)ˣ) * x L m hmL.symm f =
      x L m hmL.symm f *
        (w m L hmL (-1 : (Polynomial F)ˣ) * w m L hmL (-1 : (Polynomial F)ˣ)) := by
  rw [fnWeyl_W_mul_W hmL, fnWeyl_torus_mul_x hmL hmn hLn, fnWeyl_C_inv_neg_one, neg_one_mul,
    mul_neg_one, neg_neg]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_WW_comm

/-- **Case `b = 0`.** The check element at the column `(a, 0)`, `a` a unit, lies in `Z`. -/
theorem fnWeyl_check_pair_zero (hmL : m ≠ L) {a : Polynomial F} (ha : IsUnit a) :
    (fnSigma_pair F m L hmL (-0) a)⁻¹ * w m L hmL (-1 : (Polynomial F)ˣ) *
      fnSigma_pair F m L hmL a 0 ∈ fnZ F := by
  obtain ⟨α, rfl⟩ := fnWeyl_exists_C_of_isUnit ha
  have hα : Polynomial.C (α : F) ≠ 0 := Polynomial.C_ne_zero.2 α.ne_zero
  have h0 : (0 : Polynomial F).degree < (Polynomial.C (α : F)).degree := by
    rw [Polynomial.degree_zero]
    exact bot_lt_iff_ne_bot.2 fun h => hα (Polynomial.degree_eq_bot.1 h)
  obtain ⟨hq, hr⟩ := fnWeyl_divmod_small hα h0
  have hn : -Polynomial.C (α : F) = Polynomial.C ((-α : Fˣ) : F) := by
    rw [Units.val_neg, map_neg]
  have e : ∀ A V B : SteinbergGroup I (Polynomial F), A * V * (V * B) = A * (V * V) * B :=
    fun A V B => by group
  rw [neg_zero, fnSigma_pair_zero, fnSigma_pair_of_ne m L hmL hα, hq, hr, x_zero, one_mul,
    fnSigma_pair_zero, hn, fnWeyl_tau_C hmL, fnWeyl_tau_C hmL, inv_inv, e,
    fnWeyl_W_mul_W hmL]
  obtain ⟨z, hz, hzt⟩ := fnWeyl_torus_mul_comm_mem (I := I) hmL (-1 : Fˣ) α
  rw [hzt, neg_one_mul, mul_inv_cancel_right]
  exact hz

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_check_pair_zero

/-- **Case `deg b < deg a`.** The check element at a coprime column `(a, b)`, `b ≠ 0`,
`deg b < deg a`, lies in `Z`. -/
theorem fnWeyl_check_pair_lt (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) {a b : Polynomial F}
    (hab : IsCoprime a b) (hb : b ≠ 0) (hlt : b.degree < a.degree) :
    (fnSigma_pair F m L hmL (-b) a)⁻¹ * w m L hmL (-1 : (Polynomial F)ˣ) *
      fnSigma_pair F m L hmL a b ∈ fnZ F := by
  have ha : a ≠ 0 := Polynomial.ne_zero_of_degree_gt hlt
  obtain ⟨hq0, hr0⟩ := fnWeyl_divmod_small ha hlt
  obtain ⟨hq1, hr1⟩ := fnWeyl_divmod_neg_left a hb
  obtain ⟨hq2, hr2⟩ := fnWeyl_divmod_neg_right a hb
  have h1 : b * (a / b) + a % b = a := EuclideanDomain.div_add_mod a b
  have hcop : IsCoprime (-(a % b)) (-b) := k2PolyNagaoWeyl_isCoprime_of_comb hab
    (x1 := -1) (y1 := -(a / b)) (x2 := 0) (y2 := -1) (by linear_combination -h1) (by ring)
  obtain ⟨z, hz, hE⟩ := fnWeyl_torus_mul_pair (I := I) hmL hmn hLn (-(a % b)) (-1) (-b) hcop
  rw [fnWeyl_C_inv_neg_one, fnWeyl_C_neg_one, neg_one_mul, neg_one_mul, neg_neg, neg_neg] at hE
  have g : ∀ X Y Z V : SteinbergGroup I (Polynomial F), V * V * X = X * (V * V) →
      (X * V * Y)⁻¹ * V * (V * (X * V * Z)) = Y⁻¹ * (V * V * Z) := by
    intro X Y Z V h
    have e1 : (X * V * Y)⁻¹ * V * (V * (X * V * Z)) =
        Y⁻¹ * V⁻¹ * X⁻¹ * (V * V * X) * V * Z := by group
    rw [e1, h]
    group
  rw [fnSigma_pair_of_ne m L hmL ha, hq0, hr0, x_zero, one_mul,
    fnSigma_pair_of_ne m L hmL hb, hq1, hr1,
    fnSigma_pair_of_ne m L hmL (neg_ne_zero.2 hb), hq2, hr2, neg_neg,
    g _ _ _ _ (fnWeyl_WW_comm hmL hmn hLn (-(a / b))), fnWeyl_W_mul_W hmL, hE,
    inv_mul_cancel_left]
  exact hz

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_check_pair_lt

/-- **Tail, `r ≠ 0`.** The tail element lies in `Z`. -/
theorem fnWeyl_eq_tail_ne (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) {a b r : Polynomial F}
    (γ δ : Fˣ) (hab : IsCoprime a b) (hr0 : r ≠ 0) (hr_def : r = b - Polynomial.C (γ : F) * a)
    (hδγ : Polynomial.C (δ : F) * Polynomial.C (γ : F) = -1)
    (hδinv : Polynomial.C ((δ⁻¹ : Fˣ) : F) = -Polynomial.C (γ : F)) :
    (fnSigma_pair F m L hmL (Polynomial.C (δ : F) * r) b)⁻¹ *
      (fieldTorus F m L hmL δ * x L m hmL.symm (Polynomial.C (δ : F)) *
        fnSigma_pair F m L hmL r (-a)) ∈ fnZ F := by
  have hδδ : Polynomial.C (δ : F) * Polynomial.C ((δ⁻¹ : Fˣ) : F) = 1 := by
    rw [← map_mul Polynomial.C, Units.mul_inv, map_one]
  have hshift : x L m hmL.symm (Polynomial.C (δ : F)) * fnSigma_pair F m L hmL r (-a) =
      fnSigma_pair F m L hmL r (-a + Polynomial.C (δ : F) * r) := by
    rw [fnSigma_pair_of_ne m L hmL hr0, fnSigma_pair_of_ne m L hmL hr0,
      fnSigma_mod_add, fnSigma_div_add hr0, add_comm (-a / r), ← x_mul]
    simp only [mul_assoc]
  have hcop2 : IsCoprime r (-a + Polynomial.C (δ : F) * r) :=
    k2PolyNagaoWeyl_isCoprime_of_comb hab (x1 := Polynomial.C (δ : F)) (y1 := -1)
      (x2 := 0) (y2 := -Polynomial.C (γ : F)) (by ring)
      (by linear_combination -hr_def + r * hδγ)
  have hb' : Polynomial.C ((δ⁻¹ : Fˣ) : F) * (-a + Polynomial.C (δ : F) * r) = b := by
    linear_combination -a * hδinv + r * hδδ + hr_def
  obtain ⟨z, hz, hE⟩ := fnWeyl_torus_mul_pair (I := I) hmL hmn hLn r δ _ hcop2
  rw [mul_assoc (fieldTorus F m L hmL δ), hshift, hE, hb', inv_mul_cancel_left]
  exact hz

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_eq_tail_ne

/-- **Tail, `r = 0`.** Here `a = C α`, `b = C γ · C α` and `γ α δ = -α`; the tail element is a
constant symbol times a root `x'(·)`, so it lies in `Z ⊔ Q`. -/
theorem fnWeyl_eq_tail_zero (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) {K : Finset I}
    (hmK : m ∈ K) (α γ δ : Fˣ) (hu : γ * α * δ = -α) :
    (fnSigma_pair F m L hmL (Polynomial.C (δ : F) * 0)
        (Polynomial.C (γ : F) * Polynomial.C (α : F)))⁻¹ *
      (fieldTorus F m L hmL δ * x L m hmL.symm (Polynomial.C (δ : F)) *
        fnSigma_pair F m L hmL 0 (-Polynomial.C (α : F))) ∈ fnZQ F K L := by
  have hn : -Polynomial.C (α : F) = Polynomial.C ((-α : Fˣ) : F) := by
    rw [Units.val_neg, map_neg]
  rw [mul_zero (Polynomial.C (δ : F)), fnSigma_pair_zero, fnSigma_pair_zero,
    ← map_mul Polynomial.C, ← Units.val_mul, hn, fnWeyl_tau_C hmL, fnWeyl_tau_C hmL, inv_inv]
  obtain ⟨z, hz, hzt⟩ := fnWeyl_torus_mul_comm_mem (I := I) hmL δ (γ * α)
  have hδ : δ * (γ * α) = -α := by rw [mul_comm δ (γ * α)]; exact hu
  rw [hδ] at hzt
  have e : ∀ A T X B : SteinbergGroup I (Polynomial F), A * (T * X * B) = A * T * X * B :=
    fun A T X B => by group
  rw [e, hzt, mul_assoc z, fnWeyl_torus_mul_x hmL hmn hLn (-α), ← mul_assoc z,
    mul_inv_cancel_right]
  exact Subgroup.mul_mem _ (fn_mem_ZQ_of_mem_Z hz) (fnSigma_x_mem_ZQ hmL hmK _)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_eq_tail_zero

/-- `b ≠ 0` and `deg b = deg a` force `a ≠ 0`. -/
theorem fnWeyl_ne_zero_of_degree_eq {a b : Polynomial F} (hb : b ≠ 0)
    (hdeq : b.degree = a.degree) : a ≠ 0 := by
  rintro rfl
  rw [Polynomial.degree_zero] at hdeq
  exact hb (Polynomial.degree_eq_bot.1 hdeq)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_ne_zero_of_degree_eq

/-- Equal degrees: some constant `γ` makes `deg (b - γ a) < deg a`. -/
theorem fnWeyl_eq_data {a b : Polynomial F} (hb : b ≠ 0) (hdeq : b.degree = a.degree) :
    ∃ γ : Fˣ, (b - Polynomial.C (γ : F) * a).degree < a.degree := by
  have hla : a.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.2 (fnWeyl_ne_zero_of_degree_eq hb hdeq)
  have hlb : b.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hb
  obtain ⟨γ, hγ⟩ : ∃ γ : Fˣ, (γ : F) = b.leadingCoeff * a.leadingCoeff⁻¹ :=
    ⟨Units.mk0 _ (mul_ne_zero hlb (inv_ne_zero hla)), Units.val_mk0 _⟩
  have hlc : b.leadingCoeff = (Polynomial.C (γ : F) * a).leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hγ, mul_assoc,
      inv_mul_cancel₀ hla, mul_one]
  have hdq : b.degree = (Polynomial.C (γ : F) * a).degree := by
    rw [Polynomial.degree_C_mul γ.ne_zero, hdeq]
  refine ⟨γ, ?_⟩
  rw [← hdeq]
  exact Polynomial.degree_sub_lt hdq hb hlc

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_eq_data

/-- **Case `deg b = deg a`.** The check element lies in `Z ⊔ Q`. -/
theorem fnWeyl_check_pair_eq (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) {K : Finset I}
    (hmK : m ∈ K) {a b : Polynomial F} (hab : IsCoprime a b) (hb : b ≠ 0)
    (hdeq : b.degree = a.degree) :
    (fnSigma_pair F m L hmL (-b) a)⁻¹ * w m L hmL (-1 : (Polynomial F)ˣ) *
      fnSigma_pair F m L hmL a b ∈ fnZQ F K L := by
  have ha : a ≠ 0 := fnWeyl_ne_zero_of_degree_eq hb hdeq
  obtain ⟨γ, hrlt⟩ := fnWeyl_eq_data hb hdeq
  obtain ⟨r, hr_def⟩ : ∃ r, r = b - Polynomial.C (γ : F) * a := ⟨_, rfl⟩
  rw [← hr_def] at hrlt
  obtain ⟨hq1, hr1⟩ := fnWeyl_divmod_unique (b := b) (q := Polynomial.C (γ : F))
    ha (by linear_combination -hr_def) hrlt
  obtain ⟨δ, hδ⟩ : ∃ δ : Fˣ, δ = -γ⁻¹ := ⟨_, rfl⟩
  have hδinv : Polynomial.C ((δ⁻¹ : Fˣ) : F) = -Polynomial.C (γ : F) := by
    rw [hδ, inv_neg, inv_inv, Units.val_neg, map_neg]
  have hδγ : Polynomial.C (δ : F) * Polynomial.C (γ : F) = -1 := by
    rw [← map_mul Polynomial.C, ← Units.val_mul, hδ, neg_mul, inv_mul_cancel, Units.val_neg,
      Units.val_one, map_neg, map_one]
  have hdeg2 : (Polynomial.C (δ : F) * r).degree < (-b).degree := by
    rw [Polynomial.degree_C_mul δ.ne_zero, Polynomial.degree_neg, hdeq]
    exact hrlt
  obtain ⟨hq2, hr2⟩ := fnWeyl_divmod_unique (b := a) (q := Polynomial.C (δ : F))
    (neg_ne_zero.2 hb)
    (by linear_combination -Polynomial.C (δ : F) * hr_def + a * hδγ) hdeg2
  have hM : (w m L hmL (-1 : (Polynomial F)ˣ))⁻¹ *
      x L m hmL.symm (-Polynomial.C (δ : F)) * w m L hmL (-1 : (Polynomial F)ˣ) *
        x L m hmL.symm (Polynomial.C (γ : F)) * w m L hmL (-1 : (Polynomial F)ˣ) =
      fieldTorus F m L hmL δ * x L m hmL.symm (Polynomial.C (δ : F)) := by
    rw [show Polynomial.C (γ : F) = -Polynomial.C ((δ⁻¹ : Fˣ) : F) by
      rw [hδinv, neg_neg], fieldTorus_apply]
    exact k2PolyNagaoWeyl_middle hmL hmn hLn
      (Units.map (Polynomial.C : F →+* Polynomial F).toMonoidHom δ)
  have gid : ∀ X Y V P1 P2 : SteinbergGroup I (Polynomial F),
      (X * V * P1)⁻¹ * V * (Y * V * P2) = P1⁻¹ * (V⁻¹ * X⁻¹ * V * Y * V * P2) :=
    fun X Y V P1 P2 => by group
  rw [fnSigma_pair_of_ne m L hmL ha, hq1, hr1,
    fnSigma_pair_of_ne m L hmL (neg_ne_zero.2 hb), hq2, hr2, neg_neg, gid, ← x_neg, hM]
  by_cases hr0 : r = 0
  · subst hr0
    have hb_eq : b = Polynomial.C (γ : F) * a := by linear_combination -hr_def
    obtain ⟨u, v, huv⟩ := hab
    have hua : IsUnit a :=
      isUnit_of_dvd_one ⟨u + v * Polynomial.C (γ : F), by linear_combination -huv + v * hb_eq⟩
    obtain ⟨α, rfl⟩ := fnWeyl_exists_C_of_isUnit hua
    subst hb_eq
    have hu : γ * α * δ = -α := by
      rw [hδ, mul_neg, mul_comm γ α, mul_assoc, mul_inv_cancel, mul_one]
    exact fnWeyl_eq_tail_zero hmL hmn hLn hmK α γ δ hu
  · exact fn_mem_ZQ_of_mem_Z (fnWeyl_eq_tail_ne hmL hmn hLn γ δ hab hr0 hr_def hδγ hδinv)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_check_pair_eq

/-- The Weyl check element at a coprime column `(a, b)` with `deg b ≤ deg a` lies in `Z ⊔ Q`. -/
theorem fnWeyl_check_pair (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) {K : Finset I}
    (hmK : m ∈ K) {a b : Polynomial F} (hab : IsCoprime a b) (hd : b.degree ≤ a.degree) :
    (fnSigma_pair F m L hmL (-b) a)⁻¹ * w m L hmL (-1 : (Polynomial F)ˣ) *
      fnSigma_pair F m L hmL a b ∈ fnZQ F K L := by
  by_cases hb : b = 0
  · subst hb
    exact fn_mem_ZQ_of_mem_Z (fnWeyl_check_pair_zero hmL (isCoprime_zero_right.1 hab))
  · by_cases hlt : b.degree < a.degree
    · exact fn_mem_ZQ_of_mem_Z (fnWeyl_check_pair_lt hmL hmn hLn hab hb hlt)
    · exact fnWeyl_check_pair_eq hmL hmn hLn hmK hab hb (le_antisymm hd (not_lt.1 hlt))

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_check_pair

/-- The Weyl check of `σ` at a vector with coprime `(m, L)` coordinates, `deg v L ≤ deg v m`. -/
theorem fnWeyl_check_W (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n) {K : Finset I} (hmK : m ∈ K)
    (v : I → Polynomial F) (hcop : IsCoprime (v m) (v L)) (hd : (v L).degree ≤ (v m).degree) :
    (fnSigma_sigma F m L hmL (act (w m L hmL (-1 : (Polynomial F)ˣ)) v))⁻¹ *
        w m L hmL (-1 : (Polynomial F)ˣ) * fnSigma_sigma F m L hmL v ∈ fnZQ F K L := by
  obtain ⟨e1, e2⟩ := k2PolyNagaoSigma_act_W hmL v
  rw [fnSigma_sigma, fnSigma_sigma, e1, e2]
  exact fnWeyl_check_pair hmL hmn hLn hmK hcop hd

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_check_W

/-- **The rank-one case, outright.** For `K = {m}`, the Euclidean section is good on the whole
small generating set. -/
theorem fnWeyl_genGood_rankOne {K : Finset I} (hmL : m ≠ L) (hmn : m ≠ n) (hLn : L ≠ n)
    (hmK : m ∈ K) (hKm : ∀ i ∈ K, i = m) :
    fnGenGood F K L m hmL (fnSigma_sigma F m L hmL) := by
  have hm' : m ∈ insert L K := Finset.mem_insert_of_mem hmK
  have hL' : L ∈ insert L K := Finset.mem_insert_self L K
  have hxS : ∀ {i j : I} (hij : i ≠ j) (f : Polynomial F), i ∈ insert L K → j ∈ insert L K →
      x i j hij f ∈ fnS F (insert L K) := fun hij f hi hj =>
    x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K) hij f ⟨hi, hj⟩
  have hLm : ∀ f : Polynomial F, fnGood F K L (fnSigma_sigma F m L hmL) (x L m hmL.symm f) :=
    fun f => ⟨hxS hmL.symm f hL' hm', fnSigma_check_Lm hmL hmK ⟨n, hmn, hLn⟩ f⟩
  have hWg : fnGood F K L (fnSigma_sigma F m L hmL) (w m L hmL (-1 : (Polynomial F)ˣ)) := by
    refine ⟨?_, fun v hv => ?_⟩
    · rw [w]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hxS hmL _ hm' hL') (hxS hmL.symm _ hL' hm'))
        (hxS hmL _ hm' hL')
    · rcases lt_or_ge (v m).degree (v L).degree with hd | hd
      · exact fnSigma_check_W_lt hmL v hd
      · exact fnWeyl_check_W hmL hmn hLn hmK v (fnWeyl_coprime_orbit hmL hKm hv) hd
  have e : x m L hmL (1 : Polynomial F) =
      w m L hmL (-1 : (Polynomial F)ˣ) * x L m hmL.symm (-1 : Polynomial F) *
        (w m L hmL (-1 : (Polynomial F)ˣ))⁻¹ := by
    rw [k2PolyDeg_w_conj_self_symm_eq m L n hmL hmn hLn (-1 : (Polynomial F)ˣ)
      (-1 : Polynomial F)]
    refine congrArg (x m L hmL) ?_
    rw [Units.val_neg, Units.val_one]
    ring
  refine ⟨fun i him hiK => absurd (hKm i hiK) him, ?_, hLm⟩
  rw [e]
  exact fn_good_mul (fn_good_mul hWg (hLm (-1))) (fn_good_inv hWg)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnWeyl_genGood_rankOne

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
