import GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.WeylTorus
import GroupApproximation.Meta.AxiomGuard

/-!
# Field port of the root check, part 1: the rank-one orbit of `e_L` over `F[X]`

k2-poly piece A5.2, back half (lane k2-field-b). This is the field port of
`ElemFPK2PolyNagaoRootOrbit` (lane bh-met-93v), with `ZMod p` replaced by an arbitrary field `F`
and `G_{{m}} = k2PolyDeg_G p {m} L` replaced by `fnS F (insert L {m})`. No step used finiteness of
`F_p`, so the port is exact; only the names change.

Notation: `R = F[X]`, `m ≠ L`, `P(α, β) = α e_m + β e_L`, `W = w_mL(-1)`.

* `fnRoot_act_xmL`, `fnRoot_act_xLm`, `fnRoot_act_W`: the actions of `x_mL(a)`, `x_Lm(a)`, `W`
  on `P(α, β)`.
* `fnRoot_orbit_pair`: every coprime `(a, b)` gives `P(a, b) = y e_L` with `y ∈ G_{{m}}`.
* `fnRoot_coprime`: a vector `v = v_m e_m + v_L e_L` in a `G_K`-orbit of `e_L` has coprime
  `(v_m, v_L)`.
* `fnRoot_orbit_one`: hence it lies in the `G_{{m}}`-orbit of `e_L`.

The two support lemmas take the decomposition `v = v m • e_m + v L • e_L` as a hypothesis. The
Wide layer's `Supp`/`decomp` (k2-field-a) supplies it, so this file doesn't depend on that layer.
-/

namespace GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF

open GroupApproximation.SteinbergGroup
open GroupApproximation.BooneHigmanLinear.K2Poly (fnS)
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (w)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (act act_mul act_one
  act_x_apply unitVec unitVec_apply x_mem_rootSpan)

variable {I : Type} [Fintype I] [DecidableEq I] {F : Type} [Field F]

omit [Fintype I] in
/-- Coordinates of `α e_m + β e_L`. -/
theorem fnRoot_P_apply (m L : I) (α β : Polynomial F) (k : I) :
    (α • (unitVec m : I → Polynomial F) + β • unitVec L) k =
      (if k = m then α else 0) + (if k = L then β else 0) := by
  simp only [Pi.add_apply, Pi.smul_apply, unitVec_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_P_apply

/-- `x_mL(a) P(α, β) = P(α + aβ, β)`. -/
theorem fnRoot_act_xmL {m L : I} (hmL : m ≠ L) (a α β : Polynomial F) :
    act (x m L hmL a) (α • unitVec m + β • unitVec L) =
      (α + a * β) • unitVec m + β • unitVec L := by
  funext k
  rw [act_x_apply, fnRoot_P_apply, fnRoot_P_apply, fnRoot_P_apply, if_neg hmL.symm, if_pos rfl,
    zero_add]
  split_ifs <;> ring

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_act_xmL

/-- `x_Lm(a) P(α, β) = P(α, β + aα)`. -/
theorem fnRoot_act_xLm {m L : I} (hmL : m ≠ L) (a α β : Polynomial F) :
    act (x L m hmL.symm a) (α • unitVec m + β • unitVec L) =
      α • unitVec m + (β + a * α) • unitVec L := by
  funext k
  rw [act_x_apply, fnRoot_P_apply, fnRoot_P_apply, fnRoot_P_apply, if_pos rfl, if_neg hmL,
    add_zero]
  split_ifs <;> ring

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_act_xLm

/-- `W P(α, β) = P(-β, α)`. -/
theorem fnRoot_act_W {m L : I} (hmL : m ≠ L) (α β : Polynomial F) :
    act (w m L hmL (-1 : (Polynomial F)ˣ)) (α • unitVec m + β • unitVec L) =
      (-β) • unitVec m + α • unitVec L := by
  have hu : ((-1 : (Polynomial F)ˣ) : Polynomial F) = -1 := by
    rw [Units.val_neg, Units.val_one]
  have hui : (((-1 : (Polynomial F)ˣ)⁻¹ : (Polynomial F)ˣ) : Polynomial F) = -1 := by
    rw [inv_neg, inv_one, Units.val_neg, Units.val_one]
  rw [w, act_mul, act_mul, fnRoot_act_xmL, fnRoot_act_xLm, fnRoot_act_xmL, hu, hui]
  exact congrArg₂ (fun s t => s • unitVec m + t • unitVec L) (by ring) (by ring)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_act_W

/-- `x_ij(a) ∈ G_K = fnS F (insert L K)` for `i, j ∈ insert L K`. -/
theorem fnRoot_x_mem {K : Finset I} {L i j : I} (hij : i ≠ j) (a : Polynomial F)
    (hi : i ∈ insert L K) (hj : j ∈ insert L K) : x i j hij a ∈ fnS F (insert L K) :=
  x_mem_rootSpan (p := fun i j => i ∈ insert L K ∧ j ∈ insert L K) hij a ⟨hi, hj⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_x_mem

/-- `w_mL(u) ∈ G_{{m}}`. -/
theorem fnRoot_w_mem {m L : I} (hmL : m ≠ L) (u : (Polynomial F)ˣ) :
    w m L hmL u ∈ fnS F (insert L ({m} : Finset I)) := by
  have hm : m ∈ insert L ({m} : Finset I) :=
    Finset.mem_insert_of_mem (Finset.mem_singleton_self m)
  have hL : L ∈ insert L ({m} : Finset I) := Finset.mem_insert_self L {m}
  rw [w]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (fnRoot_x_mem hmL _ hm hL)
    (fnRoot_x_mem hmL.symm _ hL hm)) (fnRoot_x_mem hmL _ hm hL)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_w_mem

/-- **The rank-one orbit.** Every coprime `(a, b)` gives `a e_m + b e_L = y e_L` with
`y ∈ G_{{m}}`, by induction on `deg a` along the Euclidean recursion of `σ₀`. -/
theorem fnRoot_orbit_pair {m L : I} (hmL : m ≠ L) (a : Polynomial F) :
    ∀ b : Polynomial F, IsCoprime a b →
      ∃ y ∈ fnS F (insert L ({m} : Finset I)), act y (unitVec L) = a • unitVec m + b • unitVec L := by
  induction a using (Polynomial.degree_lt_wf (R := F)).induction with
  | _ a ih =>
    intro b hab
    have hm : m ∈ insert L ({m} : Finset I) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self m)
    have hL : L ∈ insert L ({m} : Finset I) := Finset.mem_insert_self L {m}
    by_cases ha : a = 0
    · subst ha
      obtain ⟨c, hc⟩ := (isCoprime_zero_left.1 hab).exists_left_inv
      refine ⟨x m L hmL (-c) * x L m hmL.symm (b - 1) * x m L hmL 1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (fnRoot_x_mem hmL _ hm hL)
          (fnRoot_x_mem hmL.symm _ hL hm)) (fnRoot_x_mem hmL _ hm hL), ?_⟩
      have he : (unitVec L : I → Polynomial F) =
          (0 : Polynomial F) • unitVec m + (1 : Polynomial F) • unitVec L := by
        rw [zero_smul, one_smul, zero_add]
      have h0 := fnRoot_act_xmL hmL (1 : Polynomial F) 0 1
      rw [← he] at h0
      rw [act_mul, act_mul, h0, fnRoot_act_xLm, fnRoot_act_xmL]
      exact congrArg₂ (fun s t => s • unitVec m + t • unitVec L)
        (by linear_combination (-1 : Polynomial F) * hc) (by ring)
    · obtain ⟨y, hy, hye⟩ := ih (b % a) (Polynomial.degree_mod_lt b ha) (-a)
        (fnWeyl_coprime_step hab)
      refine ⟨x L m hmL.symm (b / a) * w m L hmL (-1 : (Polynomial F)ˣ) * y,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (fnRoot_x_mem hmL.symm _ hL hm)
          (fnRoot_w_mem hmL _)) hy, ?_⟩
      rw [act_mul, act_mul, hye, fnRoot_act_W, fnRoot_act_xLm]
      have h1 : a * (b / a) + b % a = b := EuclideanDomain.div_add_mod b a
      exact congrArg₂ (fun s t => s • unitVec m + t • unitVec L) (neg_neg a)
        (by linear_combination h1)

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_orbit_pair

/-- The action is linear. -/
theorem fnRoot_act_lin (g : SteinbergGroup I (Polynomial F)) (a b : Polynomial F)
    (u v : I → Polynomial F) : act g (a • u + b • v) = a • act g u + b • act g v := by
  simp only [act, Matrix.mulVec_add, Matrix.mulVec_smul]

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_act_lin

/-- A vector `v = v_m e_m + v_L e_L` in the `G_K`-orbit of `e_L` has coprime `(m, L)`
coordinates: read off the `L`-row of `y⁻¹ v = e_L`. -/
theorem fnRoot_coprime {K : Finset I} {m L : I} {v : I → Polynomial F}
    (hdec : v = v m • unitVec m + v L • unitVec L)
    (hv : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) : IsCoprime (v m) (v L) := by
  obtain ⟨y, _, hy⟩ := hv
  have h1 : act y⁻¹ v = unitVec L := by rw [← hy, ← act_mul, inv_mul_cancel, act_one]
  rw [hdec, fnRoot_act_lin] at h1
  have h2 := congrFun h1 L
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, unitVec_apply,
    if_pos rfl] at h2
  exact ⟨act y⁻¹ (unitVec m) L, act y⁻¹ (unitVec L) L, by linear_combination h2⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_coprime

/-- **Orbit transfer.** A vector `v = v_m e_m + v_L e_L` in the `G_K`-orbit of `e_L` lies in the
`G_{{m}}`-orbit of `e_L`. -/
theorem fnRoot_orbit_one {K : Finset I} {m L : I} (hmL : m ≠ L) {v : I → Polynomial F}
    (hdec : v = v m • unitVec m + v L • unitVec L)
    (hv : ∃ y ∈ fnS F (insert L K), act y (unitVec L) = v) :
    ∃ y ∈ fnS F (insert L ({m} : Finset I)), act y (unitVec L) = v := by
  obtain ⟨y, hy, e⟩ := fnRoot_orbit_pair hmL (v m) (v L) (fnRoot_coprime hdec hv)
  exact ⟨y, hy, e.trans hdec.symm⟩

#audit_axioms GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF.fnRoot_orbit_one

end GroupApproximation.BooneHigmanLinear.K2Poly.FieldNF
