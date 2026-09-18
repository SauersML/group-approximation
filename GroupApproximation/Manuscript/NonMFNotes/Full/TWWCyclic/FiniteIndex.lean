import GroupApproximation.Manuscript.NonMFNotes.Full.TWWCyclic.InducedMat

/-!
# Cyclic extension by an element of finite order modulo the subgroup

`non_mf_group_notes.tex`, proof of `thm:fixed-radical-membership`
(tex l. 1376--1378), finite-index half of the cyclic extension step
(Ozawa--Rørdam--Sato, GAFA 25 (2015), §3: induction from a finite-index
normal subgroup).

If `k` normalizes `H`, some positive power of `k` lies in `H`, and the regular
character of `G` is modelled on `H` (`TWW.IsModelled`), then it is modelled on
`H ⊔ ⟨k⟩` (`isModelled_sup_zpowers_of_pow_mem`). The models are the induced
matrices of `InducedMat`, built from a model of `H` on the enlarged test set
`liftTestSet`. This step uses no amenability.
-/

namespace GroupApproximation.Full.TWWCyclic

open scoped Matrix
open scoped Matrix.Norms.L2Operator

variable {G : Type} [Group G]

open scoped Classical in
/-- The block coordinates in `H` of the elements of `F`. -/
noncomputable def liftTestSet (H : Subgroup G) (k : G) (m : ℕ) (F : Finset G) : Finset G :=
  ((F ×ˢ (Finset.univ : Finset (Fin m × Fin m))).image
    fun t => cc k t.1 t.2.1 t.2.2).filter (· ∈ H)

theorem mem_liftTestSet_H {H : Subgroup G} {k : G} {m : ℕ} {F : Finset G} {g : G}
    (hg : g ∈ liftTestSet H k m F) : g ∈ H := by
  rw [liftTestSet, Finset.mem_filter] at hg
  exact hg.2

theorem mem_liftTestSet {H : Subgroup G} {k : G} {m : ℕ} {F : Finset G} {x : G}
    (hx : x ∈ F) (i j : Fin m) (hmem : cc k x i j ∈ H) : cc k x i j ∈ liftTestSet H k m F := by
  rw [liftTestSet, Finset.mem_filter, Finset.mem_image]
  exact ⟨⟨(x, i, j), Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, rfl⟩, hmem⟩

theorem one_mem_liftTestSet {H : Subgroup G} {k : G} {m : ℕ} {F : Finset G} (hm : 0 < m)
    (h1 : (1 : G) ∈ F) : (1 : G) ∈ liftTestSet H k m F := by
  have h1H : cc k 1 (0 : ℕ) (0 : ℕ) ∈ H := by
    rw [cc_one_self]
    exact H.one_mem
  have h := mem_liftTestSet (H := H) (k := k) h1 (⟨0, hm⟩ : Fin m) ⟨0, hm⟩ h1H
  rwa [cc_one_self] at h

/-- **The induced model.** A model of the regular character on `liftTestSet H k m F`
induces a model on `F`, when `F ⊆ H ⊔ ⟨k⟩` and `m > 0` is least with `k ^ m ∈ H`. -/
noncomputable def inducedModel {H : Subgroup G} {k : G} {m : ℕ} {F : Finset G} {ε : ℝ}
    (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) (hm : 0 < m)
    (hkm : k ^ m ∈ H) (hmin : ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H)
    (hF : ∀ x ∈ F, x ∈ H ⊔ Subgroup.zpowers k) (hε : 0 < ε)
    (π : MFTraceRecognition.RegularCharacterModel G (liftTestSet H k m F) ε
      fun _ : G => (1 : ℝ)) :
    MFTraceRecognition.RegularCharacterModel G F ε fun _ : G => (1 : ℝ) where
  carrier := ⟨Fin m × π.carrier, inferInstance, inferInstance⟩
  nonempty := card_induced_pos hm π
  map := inducedMat H k m π
  bounded := fun x hx =>
    norm_inducedMat_le_one hmin π fun i j hmem => mem_liftTestSet hx i j hmem
  multiplicative := fun x hx y hy =>
    norm_inducedMat_mul_sub_le hk hk' hm hkm hmin π (hF x hx)
      (fun i j hmem => mem_liftTestSet hx i j hmem)
      (fun i j hmem => mem_liftTestSet hy i j hmem) hε.le
  star_compatible := fun x hx =>
    norm_inducedMat_inv_sub_le hmin π (fun i j hmem => mem_liftTestSet hx i j hmem) hε.le
  trace_correct_one := fun h1 =>
    norm_trace_inducedMat_one_sub_le H k hm π (one_mem_liftTestSet hm h1)
  trace_correct_ne := fun x hx hne =>
    norm_trace_inducedMat_le H k hm π hε.le (fun i j hmem => mem_liftTestSet hx i j hmem) hne

/-- **Cyclic extension, finite order modulo `H`.** If `k` normalizes `H` and
`k ^ m₀ ∈ H` for some `m₀ > 0`, then `IsModelled H` implies
`IsModelled (H ⊔ ⟨k⟩)` (`thm:fixed-radical-membership`, finite-index case of the
cyclic extension step; ORS GAFA 25 (2015), §3). -/
theorem isModelled_sup_zpowers_of_pow_mem {H : Subgroup G} {k : G}
    (hk : ∀ h ∈ H, k * h * k⁻¹ ∈ H) (hk' : ∀ h ∈ H, k⁻¹ * h * k ∈ H) {m₀ : ℕ}
    (hm₀ : 0 < m₀) (hkm₀ : k ^ m₀ ∈ H) (hH : TWW.IsModelled H) :
    TWW.IsModelled (H ⊔ Subgroup.zpowers k) := by
  classical
  have hex : ∃ m : ℕ, 0 < m ∧ k ^ m ∈ H := ⟨m₀, hm₀, hkm₀⟩
  obtain ⟨m, ⟨hm, hkm⟩, hmin⟩ :
      ∃ m : ℕ, (0 < m ∧ k ^ m ∈ H) ∧ ∀ r : ℕ, 0 < r → r < m → k ^ r ∉ H :=
    ⟨Nat.find hex, Nat.find_spec hex, fun r hr hlt hkr => Nat.find_min hex hlt ⟨hr, hkr⟩⟩
  intro F hF ε hε
  obtain ⟨π⟩ := hH (liftTestSet H k m F) (fun g hg => mem_liftTestSet_H hg) ε hε
  exact ⟨inducedModel hk hk' hm hkm hmin hF hε π⟩

end GroupApproximation.Full.TWWCyclic
