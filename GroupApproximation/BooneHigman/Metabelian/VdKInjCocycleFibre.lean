import GroupApproximation.BooneHigman.Metabelian.VdKInjActInj
import GroupApproximation.Meta.AxiomGuard

/-!
# Row cocycles and retractions, part 1: the action on the base fibre

Lane `bh-met-91y`.  Fix a row cocycle `c` (`vdkInjAct_IsCocycle c`) and its action
`vdkInjAct_hom hc` of `St_{n+1}(R)` on `St_n(R) × R^{n+1}`.  Everything here is unconditional.

* `vdkInjCocycle_hom_snd`: the row component of `hom g (h, u)` is `u M_{g⁻¹}`.
* `vdkInjCocycle_hom_lmul`: the action commutes with left multiplication in the first factor.
* `vdkInjCocycle_psi hc g` is the first component of `hom g (1, e_last)`.  On the stabiliser
  `rowStab(e_last)` it is an anti-homomorphism (`vdkInjCocycle_psi_mul`).
* If `c` is based, `psi (stab g) = g⁻¹` (`vdkInjCocycle_psi_stab`).

So `h ↦ (psi h)⁻¹` is a retraction `rowStab(e_last) →* St_n(R)` of `stab`.  That is the
direction "cocycle ⟹ retraction" of `VdKInjCocycleRetract.lean`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open GroupApproximation.BooneHigman.SteinbergBasic GroupApproximation.SteinbergGroup

variable {n : ℕ} {R : Type*} [CommRing R] {c : vdkInjAct_Cocycle n R}

/-- The inverse of the permutation `move_{ij}(a)` is `move_{ij}(-a)`, pointwise. -/
theorem vdkInjCocycle_permInv_apply (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1))
    (hij : i ≠ j) (a : R) (z : St n R × (Fin (n + 1) → R)) :
    (vdkInjAct_perm hc i j hij a)⁻¹ z = vdkInjAct_move c i j hij (-a) z := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  show z = vdkInjAct_move c i j hij a (vdkInjAct_move c i j hij (-a) z)
  rw [vdkInjAct_move_add hc, neg_add_cancel, vdkInjAct_move_zero hc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_permInv_apply

theorem vdkInjCocycle_hom_x_apply (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1))
    (hij : i ≠ j) (a : R) (z : St n R × (Fin (n + 1) → R)) :
    vdkInjAct_hom hc (x i j hij a) z = vdkInjAct_move c i j hij (-a) z := by
  rw [vdkInjAct_hom_x, vdkInjCocycle_permInv_apply]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_hom_x_apply

/-- The elements whose action moves the row component by `u ↦ u M_{g⁻¹}`. -/
noncomputable def vdkInjCocycle_sndSubgroup (hc : vdkInjAct_IsCocycle c) :
    Subgroup (St (n + 1) R) where
  carrier := {g | ∀ z : St n R × (Fin (n + 1) → R),
    (vdkInjAct_hom hc g z).2 = vdkInjAct_row z.2 g⁻¹}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    intro z
    rw [map_mul, Equiv.Perm.mul_apply, ha, hb, vdkInjAct_row_mul, mul_inv_rev]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro z
    rw [map_one, Equiv.Perm.one_apply, inv_one, vdkInjAct_row_one]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    intro z
    have hw : vdkInjAct_hom hc a ((vdkInjAct_hom hc a)⁻¹ z) = z :=
      Equiv.Perm.eq_inv_iff_eq.mp rfl
    have h1 := ha ((vdkInjAct_hom hc a)⁻¹ z)
    rw [hw] at h1
    rw [map_inv, inv_inv, h1, vdkInjAct_row_mul, inv_mul_cancel, vdkInjAct_row_one]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_sndSubgroup

theorem vdkInjCocycle_mem_sndSubgroup (hc : vdkInjAct_IsCocycle c) (g : St (n + 1) R) :
    g ∈ vdkInjCocycle_sndSubgroup hc ↔ ∀ z : St n R × (Fin (n + 1) → R),
      (vdkInjAct_hom hc g z).2 = vdkInjAct_row z.2 g⁻¹ :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_mem_sndSubgroup

theorem vdkInjCocycle_x_mem_snd (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1)) (hij : i ≠ j)
    (a : R) : x i j hij a ∈ vdkInjCocycle_sndSubgroup hc := by
  rw [vdkInjCocycle_mem_sndSubgroup]
  intro z
  rw [vdkInjCocycle_hom_x_apply]
  show vdkInjAct_row z.2 (x i j hij (-a)) = vdkInjAct_row z.2 (x i j hij a)⁻¹
  rw [x_neg]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_x_mem_snd

/-- **Row component.**  `hom g` moves the row by `g⁻¹`. -/
theorem vdkInjCocycle_hom_snd (hc : vdkInjAct_IsCocycle c) (g : St (n + 1) R)
    (z : St n R × (Fin (n + 1) → R)) : (vdkInjAct_hom hc g z).2 = vdkInjAct_row z.2 g⁻¹ := by
  have hg : g ∈ vdkInjCocycle_sndSubgroup hc := by
    refine PresentedGroup.generated_by _ (vdkInjCocycle_sndSubgroup hc) ?_ g
    rintro ⟨i, j, hij, a⟩
    exact vdkInjCocycle_x_mem_snd hc i j hij a
  exact (vdkInjCocycle_mem_sndSubgroup hc g).mp hg z

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_hom_snd

/-- The elements whose action commutes with left multiplication in the first factor. -/
noncomputable def vdkInjCocycle_lmulSubgroup (hc : vdkInjAct_IsCocycle c) :
    Subgroup (St (n + 1) R) where
  carrier := {g | ∀ (k : St n R) (z : St n R × (Fin (n + 1) → R)),
    vdkInjAct_hom hc g (k * z.1, z.2) =
      (k * (vdkInjAct_hom hc g z).1, (vdkInjAct_hom hc g z).2)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    intro k z
    rw [map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hb k z,
      ha k (vdkInjAct_hom hc b z)]
  one_mem' := by
    simp only [Set.mem_setOf_eq]
    intro k z
    simp only [map_one, Equiv.Perm.one_apply]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    intro k z
    have hw : vdkInjAct_hom hc a ((vdkInjAct_hom hc a)⁻¹ z) = z :=
      Equiv.Perm.eq_inv_iff_eq.mp rfl
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, ha k ((vdkInjAct_hom hc a)⁻¹ z), hw]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_lmulSubgroup

theorem vdkInjCocycle_mem_lmulSubgroup (hc : vdkInjAct_IsCocycle c) (g : St (n + 1) R) :
    g ∈ vdkInjCocycle_lmulSubgroup hc ↔ ∀ (k : St n R) (z : St n R × (Fin (n + 1) → R)),
      vdkInjAct_hom hc g (k * z.1, z.2) =
        (k * (vdkInjAct_hom hc g z).1, (vdkInjAct_hom hc g z).2) :=
  Iff.rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_mem_lmulSubgroup

theorem vdkInjCocycle_x_mem_lmul (hc : vdkInjAct_IsCocycle c) (i j : Fin (n + 1))
    (hij : i ≠ j) (a : R) : x i j hij a ∈ vdkInjCocycle_lmulSubgroup hc := by
  rw [vdkInjCocycle_mem_lmulSubgroup]
  intro k z
  obtain ⟨h, u⟩ := z
  simp only [vdkInjCocycle_hom_x_apply]
  show (k * h * c u i j hij (-a), vdkInjAct_row u (x i j hij (-a))) =
    (k * (h * c u i j hij (-a)), vdkInjAct_row u (x i j hij (-a)))
  rw [mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_x_mem_lmul

/-- **Left equivariance.**  The action commutes with left multiplication on `St_n(R)`. -/
theorem vdkInjCocycle_hom_lmul (hc : vdkInjAct_IsCocycle c) (g : St (n + 1) R) (k h : St n R)
    (u : Fin (n + 1) → R) :
    vdkInjAct_hom hc g (k * h, u) =
      (k * (vdkInjAct_hom hc g (h, u)).1, (vdkInjAct_hom hc g (h, u)).2) := by
  have hg : g ∈ vdkInjCocycle_lmulSubgroup hc := by
    refine PresentedGroup.generated_by _ (vdkInjCocycle_lmulSubgroup hc) ?_ g
    rintro ⟨i, j, hij, a⟩
    exact vdkInjCocycle_x_mem_lmul hc i j hij a
  exact (vdkInjCocycle_mem_lmulSubgroup hc g).mp hg k (h, u)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_hom_lmul

/-- The fibre readout: the first component of `hom g (1, e_last)`. -/
noncomputable def vdkInjCocycle_psi (hc : vdkInjAct_IsCocycle c) (g : St (n + 1) R) :
    St n R :=
  (vdkInjAct_hom hc g (1, Pi.single (Fin.last n) 1)).1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_psi

/-- An element of `rowStab(e_last)` maps `(1, e_last)` into the fibre over `e_last`. -/
theorem vdkInjCocycle_hom_base (hc : vdkInjAct_IsCocycle c) {g : St (n + 1) R}
    (hg : g ∈ vdkInjCoset_rowStab n R) :
    vdkInjAct_hom hc g (1, Pi.single (Fin.last n) 1) =
      (vdkInjCocycle_psi hc g, Pi.single (Fin.last n) 1) := by
  have h2 : (vdkInjAct_hom hc g (1, Pi.single (Fin.last n) 1)).2 =
      Pi.single (Fin.last n) 1 := by
    rw [vdkInjCocycle_hom_snd]
    exact (vdkInjCoset_mem_rowStab _).mp (inv_mem hg)
  exact Prod.ext rfl h2

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_hom_base

/-- On the fibre over `e_last`, an element of `rowStab(e_last)` acts by `k ↦ k · psi g`. -/
theorem vdkInjCocycle_hom_fibre (hc : vdkInjAct_IsCocycle c) {g : St (n + 1) R}
    (hg : g ∈ vdkInjCoset_rowStab n R) (k : St n R) :
    vdkInjAct_hom hc g (k, Pi.single (Fin.last n) 1) =
      (k * vdkInjCocycle_psi hc g, Pi.single (Fin.last n) 1) := by
  have h := vdkInjCocycle_hom_lmul hc g k 1 (Pi.single (Fin.last n) 1)
  rw [mul_one, vdkInjCocycle_hom_base hc hg] at h
  exact h

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_hom_fibre

theorem vdkInjCocycle_hom_mul_base (hc : vdkInjAct_IsCocycle c) {a b : St (n + 1) R}
    (ha : a ∈ vdkInjCoset_rowStab n R) (hb : b ∈ vdkInjCoset_rowStab n R) :
    vdkInjAct_hom hc (a * b) (1, Pi.single (Fin.last n) 1) =
      (vdkInjCocycle_psi hc b * vdkInjCocycle_psi hc a, Pi.single (Fin.last n) 1) := by
  rw [map_mul, Equiv.Perm.mul_apply, vdkInjCocycle_hom_base hc hb, vdkInjCocycle_hom_fibre hc ha]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_hom_mul_base

/-- **Anti-homomorphism.**  On `rowStab(e_last)`, `psi (a b) = psi b · psi a`. -/
theorem vdkInjCocycle_psi_mul (hc : vdkInjAct_IsCocycle c) {a b : St (n + 1) R}
    (ha : a ∈ vdkInjCoset_rowStab n R) (hb : b ∈ vdkInjCoset_rowStab n R) :
    vdkInjCocycle_psi hc (a * b) = vdkInjCocycle_psi hc b * vdkInjCocycle_psi hc a :=
  congrArg Prod.fst (vdkInjCocycle_hom_mul_base hc ha hb)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_psi_mul

/-- For a based cocycle, `psi (stab g) = g⁻¹`. -/
theorem vdkInjCocycle_psi_stab (hc : vdkInjAct_IsCocycle c) (hb : vdkInjAct_IsBased c)
    (g : St n R) : vdkInjCocycle_psi hc (stab n R g) = g⁻¹ := by
  have h1 := (vdkInjAct_mem_baseSubgroup hc g).mp (vdkInjAct_mem_base_all hc hb g) 1
  rw [one_mul] at h1
  exact congrArg Prod.fst h1

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.vdkInjCocycle_psi_stab

end GroupApproximation.BooneHigman.Metabelian.ElemFP
