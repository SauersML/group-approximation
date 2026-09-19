import GroupApproximation.BooneHigman.Join.Assoc
import GroupApproximation.ThompsonOre.NormalFormF

/-!
# The lift of `F` is faithful (lane bh-pal-met-join)

`Phi = psi.range ≤ Q` is the lift of Thompson's `F` into the all-swaps quotient of `V_2`.  This
file proves that the evaluation is injective on it (`Phi_faithful`).

* `HasGerm0 f m n`: `f` carries `0^(m+j)` onto `0^(n+j)` by prefix substitution, for every `j`.
  The permutations with such a germ at `0^∞` form a subgroup `G0`, and `chi0 f = n - m` is a
  homomorphism `G0 →* ℤ` (`chi0Hom`).
* `W = jEp(Phi)` is an `FModel` (`wModel`): the generators are `jEp (Y n)`, the shift is
  `localize [1]`, and the exponent is `chi0`.
* `psi_injective_E`: if `jEp (psi g) = 1` then `g = 1`.  Write `g` in normal form
  (`thompsonF_nf_exists`), push the form to `W`, and use uniqueness there (`FModel.nf_unique`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace GroupApproximation.BooneHigman.Join

open GroupApproximation.BooneHigman.Metabelian.Envelope
open GroupApproximation.ThompsonOre

/-- The evaluation as a homomorphism to permutations of the boundary. -/
noncomputable def jEp : higmanVCCommon_Q 2 →* Equiv.Perm (Cantor (Fin 2)) :=
  (higmanThompsonV (Fin 2)).subtype.comp (jE 2)

#audit_axioms GroupApproximation.BooneHigman.Join.jEp

theorem jEp_apply (q : higmanVCCommon_Q 2) : jEp q = jperm 2 q := rfl

#audit_axioms GroupApproximation.BooneHigman.Join.jEp_apply

/-- The word `0^n`. -/
abbrev zs (n : ℕ) : List (Fin 2) := List.replicate n 0

theorem zs_add (a b : ℕ) : zs a ++ zs b = zs (a + b) := List.replicate_append_replicate

#audit_axioms GroupApproximation.BooneHigman.Join.zs_add

/-- `f` has germ `(m, n)` at `0^∞`. -/
def HasGerm0 (f : Equiv.Perm (Cantor (Fin 2))) (m n : ℕ) : Prop :=
  ∀ j : ℕ, MapsCone f (zs (m + j)) (zs (n + j))

#audit_axioms GroupApproximation.BooneHigman.Join.HasGerm0

theorem hasGerm0_of_mapsCone {f : Equiv.Perm (Cantor (Fin 2))} {m n : ℕ}
    (h : MapsCone f (zs m) (zs n)) : HasGerm0 f m n := by
  intro j
  have h' := h.append (zs j)
  rwa [zs_add, zs_add] at h'

#audit_axioms GroupApproximation.BooneHigman.Join.hasGerm0_of_mapsCone

theorem HasGerm0.shift {f : Equiv.Perm (Cantor (Fin 2))} {m n : ℕ} (h : HasGerm0 f m n)
    (k : ℕ) : HasGerm0 f (m + k) (n + k) := by
  intro j
  have h' := h (k + j)
  rwa [← Nat.add_assoc, ← Nat.add_assoc] at h'

#audit_axioms GroupApproximation.BooneHigman.Join.HasGerm0.shift

theorem HasGerm0.mul {f g : Equiv.Perm (Cantor (Fin 2))} {m n m' n' : ℕ}
    (hf : HasGerm0 f m n) (hg : HasGerm0 g m' n') : HasGerm0 (f * g) (m' + m) (n + n') := by
  intro j
  have h1 := hg (m + j)
  have h2 := hf (n' + j)
  have e1 : m' + (m + j) = m' + m + j := by omega
  have e2 : n' + (m + j) = m + (n' + j) := by omega
  have e3 : n + (n' + j) = n + n' + j := by omega
  rw [e1, e2] at h1
  rw [e3] at h2
  exact MapsCone.comp h1 h2

#audit_axioms GroupApproximation.BooneHigman.Join.HasGerm0.mul

theorem HasGerm0.inv {f : Equiv.Perm (Cantor (Fin 2))} {m n : ℕ} (hf : HasGerm0 f m n) :
    HasGerm0 f⁻¹ n m := fun j => (hf j).inv

#audit_axioms GroupApproximation.BooneHigman.Join.HasGerm0.inv

theorem HasGerm0.eq {f : Equiv.Perm (Cantor (Fin 2))} {m n m' n' : ℕ} (h : HasGerm0 f m n)
    (h' : HasGerm0 f m' n') : (n : ℤ) - m = (n' : ℤ) - m' := by
  have h1 := h m'
  have h2 := h' m
  rw [Nat.add_comm m' m] at h2
  have e := congrArg List.length (MapsCone.unique h1 h2)
  simp only [List.length_replicate] at e
  omega

#audit_axioms GroupApproximation.BooneHigman.Join.HasGerm0.eq

/-- The permutations with a germ at `0^∞`. -/
def G0 : Subgroup (Equiv.Perm (Cantor (Fin 2))) where
  carrier := {f | ∃ m n, HasGerm0 f m n}
  mul_mem' := by
    rintro f g ⟨m, n, hf⟩ ⟨m', n', hg⟩
    exact ⟨_, _, hf.mul hg⟩
  one_mem' := ⟨0, 0, fun j => mapsCone_one _⟩
  inv_mem' := by
    rintro f ⟨m, n, hf⟩
    exact ⟨_, _, hf.inv⟩

#audit_axioms GroupApproximation.BooneHigman.Join.G0

theorem mem_G0 {f : Equiv.Perm (Cantor (Fin 2))} : f ∈ G0 ↔ ∃ m n, HasGerm0 f m n := Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Join.mem_G0

/-- The germ exponent `n - m`. -/
noncomputable def chi0 (f : ↥G0) : ℤ :=
  (Classical.choose (Classical.choose_spec (mem_G0.mp f.2)) : ℤ) -
    Classical.choose (mem_G0.mp f.2)

#audit_axioms GroupApproximation.BooneHigman.Join.chi0

theorem chi0_eq {f : ↥G0} {m n : ℕ} (h : HasGerm0 f m n) : chi0 f = (n : ℤ) - m :=
  (Classical.choose_spec (Classical.choose_spec (mem_G0.mp f.2))).eq h

#audit_axioms GroupApproximation.BooneHigman.Join.chi0_eq

/-- The germ exponent as a homomorphism. -/
noncomputable def chi0Hom : ↥G0 →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (chi0 f)
  map_one' := by
    show Multiplicative.ofAdd (chi0 1) = 1
    rw [chi0_eq (f := 1) (m := 0) (n := 0) (fun j => mapsCone_one _)]
    simp
  map_mul' f g := by
    show Multiplicative.ofAdd (chi0 (f * g)) =
      Multiplicative.ofAdd (chi0 f) * Multiplicative.ofAdd (chi0 g)
    obtain ⟨m, n, hf⟩ := mem_G0.mp f.2
    obtain ⟨m', n', hg⟩ := mem_G0.mp g.2
    rw [chi0_eq (f := f * g) (hf.mul hg), chi0_eq hf, chi0_eq hg, ← ofAdd_add]
    congr 1
    push_cast
    ring

#audit_axioms GroupApproximation.BooneHigman.Join.chi0Hom

theorem chi0Hom_eq {f : ↥G0} {m n : ℕ} (h : HasGerm0 f m n) :
    chi0Hom f = Multiplicative.ofAdd ((n : ℤ) - m) := by
  show Multiplicative.ofAdd (chi0 f) = _
  rw [chi0_eq h]

#audit_axioms GroupApproximation.BooneHigman.Join.chi0Hom_eq

theorem germ_X0 : HasGerm0 (jEp X0) 1 2 :=
  hasGerm0_of_mapsCone mapsCone_X0_zero

#audit_axioms GroupApproximation.BooneHigman.Join.germ_X0

theorem germ_phi_one (q : higmanVCCommon_Q 2) : HasGerm0 (jEp (jPhi 2 [1] q)) 1 1 := by
  refine hasGerm0_of_mapsCone fun y => ?_
  rw [jEp_apply, jperm_jPhi]
  exact localize_apply_of_not (fun h => Set.disjoint_left.mp
    (disjoint_cone (v := [0]) (w := [1]) (by decide) (by decide)) (prepend_mem_cone (zs 1) y) h) _

#audit_axioms GroupApproximation.BooneHigman.Join.germ_phi_one

theorem germ_Y_succ (n : ℕ) : HasGerm0 (jEp (Y (n + 1))) 1 1 := by
  rw [← jPhi_one_Y]
  exact germ_phi_one _

#audit_axioms GroupApproximation.BooneHigman.Join.germ_Y_succ

/-- The image of the lift of `F` in `V_2`. -/
noncomputable def W : Subgroup (Equiv.Perm (Cantor (Fin 2))) := Phi.map jEp

#audit_axioms GroupApproximation.BooneHigman.Join.W

theorem W_le_G0 : W ≤ G0 := by
  rintro _ ⟨q, ⟨g, rfl⟩, rfl⟩
  have hK : Subgroup.closure (Set.range (PresentedGroup.of (rels := thompsonRels))) ≤
      G0.comap (jEp.comp psi) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    show jEp (psi (PresentedGroup.of i)) ∈ G0
    rw [← xn_of, psi_xn]
    rcases i with ⟨_ | n, hn⟩
    · show jEp (Y 0) ∈ G0
      rw [Y_zero]
      exact mem_G0.mpr ⟨1, 2, germ_X0⟩
    · show jEp (Y (n + 1)) ∈ G0
      exact mem_G0.mpr ⟨1, 1, germ_Y_succ n⟩
  rw [PresentedGroup.closure_range_of] at hK
  exact hK (Subgroup.mem_top g)

#audit_axioms GroupApproximation.BooneHigman.Join.W_le_G0

theorem jEp_mem_W {q : higmanVCCommon_Q 2} (hq : q ∈ Phi) : jEp q ∈ W :=
  Subgroup.mem_map_of_mem jEp hq

#audit_axioms GroupApproximation.BooneHigman.Join.jEp_mem_W

/-- The generators of `W`. -/
noncomputable def wx (n : ℕ) : ↥W := ⟨jEp (Y n), jEp_mem_W (Y_mem_Phi n)⟩

#audit_axioms GroupApproximation.BooneHigman.Join.wx

/-- `localize [1]` preserves `W`. -/
theorem localize_one_mem_W {f : Equiv.Perm (Cantor (Fin 2))} (hf : f ∈ W) :
    localize [1] f ∈ W := by
  obtain ⟨q, hq, rfl⟩ := hf
  rw [jEp_apply, ← jperm_jPhi, ← jEp_apply]
  exact jEp_mem_W (jPhi_one_mem_Phi hq)

#audit_axioms GroupApproximation.BooneHigman.Join.localize_one_mem_W

/-- The shift of `W`. -/
noncomputable def wShift : ↥W →* ↥W where
  toFun f := ⟨localize [1] f, localize_one_mem_W f.2⟩
  map_one' := Subtype.ext (map_one (localize [1]))
  map_mul' f g := Subtype.ext (map_mul (localize [1]) f g)

#audit_axioms GroupApproximation.BooneHigman.Join.wShift

/-- The corestriction of `jEp ∘ psi` to `W`. -/
noncomputable def psiW : ThompsonF →* ↥W :=
  MonoidHom.codRestrict (jEp.comp psi) W fun g => jEp_mem_W ⟨g, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.psiW

theorem psiW_coe (g : ThompsonF) : (psiW g : Equiv.Perm (Cantor (Fin 2))) = jEp (psi g) := rfl

#audit_axioms GroupApproximation.BooneHigman.Join.psiW_coe

theorem psiW_xn (n : ℕ) : psiW (xn n) = wx n :=
  Subtype.ext (by rw [psiW_coe, psi_xn]; all_goals rfl)

#audit_axioms GroupApproximation.BooneHigman.Join.psiW_xn

theorem psiW_surjective : Function.Surjective psiW := by
  rintro ⟨_, q, ⟨g, rfl⟩, rfl⟩
  exact ⟨g, rfl⟩

#audit_axioms GroupApproximation.BooneHigman.Join.psiW_surjective

theorem psiW_shift (g : ThompsonF) : psiW (shift g) = wShift (psiW g) := by
  apply Subtype.ext
  show jEp (psi (shift g)) = localize [1] (jEp (psi g))
  rw [psi_shift, jEp_apply, jEp_apply, jperm_jPhi]

#audit_axioms GroupApproximation.BooneHigman.Join.psiW_shift

/-- **The model of `F` on `W`.** -/
noncomputable def wModel : FModel ↥W where
  x := wx
  rel i j hij := by
    apply Subtype.ext
    show jEp (Y j) * jEp (Y i) = jEp (Y i) * jEp (Y (j + 1))
    rw [← map_mul, ← map_mul]
    congr 1
    obtain ⟨k, rfl⟩ : ∃ k, j = i + k + 1 := ⟨j - i - 1, by omega⟩
    have h : (Y i)⁻¹ * Y (i + k + 1) * Y i = Y (i + k + 1 + 1) := conj_Y_Y i k
    calc Y (i + k + 1) * Y i = Y i * ((Y i)⁻¹ * Y (i + k + 1) * Y i) := by group
      _ = Y i * Y (i + k + 1 + 1) := by rw [h]
  closure_eq_top := by
    rw [eq_top_iff]
    rintro f -
    obtain ⟨g, rfl⟩ := psiW_surjective f
    have hK : Subgroup.closure (Set.range (PresentedGroup.of (rels := thompsonRels))) ≤
        (Subgroup.closure (Set.range wx)).comap psiW := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      show psiW (PresentedGroup.of i) ∈ Subgroup.closure (Set.range wx)
      rw [← xn_of, psiW_xn]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    rw [PresentedGroup.closure_range_of] at hK
    exact hK (Subgroup.mem_top g)
  shift := wShift
  shift_x n := by
    rw [← psiW_xn, ← psiW_shift, shift_xn, psiW_xn]
  shift_injective f g h := Subtype.ext (localize_injective [1] (congrArg Subtype.val h))
  chi := chi0Hom.comp (Subgroup.inclusion W_le_G0)
  chi_x_zero := by
    have h : HasGerm0 (jEp (Y 0)) 1 2 := by rw [Y_zero]; exact germ_X0
    exact (chi0Hom_eq (f := ⟨jEp (Y 0), W_le_G0 (wx 0).2⟩) h).trans (by norm_num)
  chi_x_succ n :=
    (chi0Hom_eq (f := ⟨jEp (Y (n + 1)), W_le_G0 (wx (n + 1)).2⟩) (germ_Y_succ n)).trans
      (by norm_num)

#audit_axioms GroupApproximation.BooneHigman.Join.wModel

/-- `psiW` carries normal-form values to normal-form values. -/
theorem psiW_val : ∀ l : List (ℕ × ℕ), psiW (thompsonFModel.val l) = wModel.val l
  | [] => by simp only [FModel.val_nil, map_one]
  | (a, b) :: r => by
    simp only [FModel.val_cons, map_mul, map_inv, map_pow]
    have h0 : psiW (thompsonFModel.x 0) = wModel.x 0 := psiW_xn 0
    have hs : psiW (thompsonFModel.shift (thompsonFModel.val r)) =
        wModel.shift (wModel.val r) := by
      show psiW (shift _) = wShift _
      rw [psiW_shift, psiW_val r]
    rw [h0, hs]

#audit_axioms GroupApproximation.BooneHigman.Join.psiW_val

/-- **Faithfulness of the lift of `F`**, on `ThompsonF`. -/
theorem psi_injective_E {g : ThompsonF} (h : jEp (psi g) = 1) : g = 1 := by
  obtain ⟨l, hl, rfl⟩ := thompsonF_nf_exists g
  have h1 : wModel.val l = 1 := by
    rw [← psiW_val]
    exact Subtype.ext h
  rw [wModel.eq_nil_of_val_eq_one l hl h1]
  all_goals rfl

#audit_axioms GroupApproximation.BooneHigman.Join.psi_injective_E

/-- **Faithfulness of the lift of `F`**: an element of `Phi` with trivial evaluation is `1`. -/
theorem Phi_faithful {q : higmanVCCommon_Q 2} (hq : q ∈ Phi) (h : jperm 2 q = 1) : q = 1 := by
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hq
  rw [psi_injective_E h, map_one]

#audit_axioms GroupApproximation.BooneHigman.Join.Phi_faithful

end GroupApproximation.BooneHigman.Join
