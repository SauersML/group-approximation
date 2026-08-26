import GroupApproximation.Higman.HNNCentralizer

/-!
# A conjugated exact commutation detector

This file packages the algebraic detector that can be attached *after* an
arbitrary tower has been constructed.  Let `e : F → K` cut out `N` by a
subgroup `L ≤ K`, let `q ∈ K`, and inject `K` into a completed tower `P`.
In `P`, centralize the conjugate of `L` by the image of `q`.  Britton's lemma
then gives the exact equivalence

    `[v, j(q e(f) q⁻¹)] = 1  ↔  f ∈ N`.

No stable letter from the earlier tower has to act on `v`, and no commutation
relation between `v` and `j(q)` is imposed.  The only tower hypothesis is that
its base map is injective.
-/

namespace GroupApproximation
namespace Higman
namespace ConjugatedDetector

open HNNExtension

variable {F K P : Type} [Group F] [Group K] [Group P]

/-- The conjugate `q L q⁻¹`, expressed as the image of `L` under an inner
automorphism. -/
def conjugateSubgroup (L : Subgroup K) (q : K) : Subgroup K :=
  L.map (MulAut.conj q).toMonoidHom

/-- Membership of a conjugated element in a conjugated subgroup is exactly
membership of the original element. -/
theorem conj_mem_conjugateSubgroup_iff (L : Subgroup K) (q x : K) :
    q * x * q⁻¹ ∈ conjugateSubgroup L q ↔ x ∈ L := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hconj : (MulAut.conj q) y = (MulAut.conj q) x := by
      simpa [MulAut.conj_apply] using hxy
    have hyx : y = x := (MulAut.conj q).injective hconj
    simpa [← hyx] using hy
  · intro hx
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩

/-- The conjugated subgroup after embedding the old base into a completed
tower.  This definition is deliberately outside all details of that tower. -/
def towerSubgroup (L : Subgroup K) (q : K) (j : K →* P) : Subgroup P :=
  (conjugateSubgroup L q).map j

/-- Injecting the tower base neither creates nor destroys membership in the
conjugated subgroup. -/
theorem map_conj_mem_towerSubgroup_iff (L : Subgroup K) (q x : K)
    (j : K →* P) (hj : Function.Injective j) :
    j (q * x * q⁻¹) ∈ towerSubgroup L q j ↔ x ∈ L := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = q * x * q⁻¹ := hj hxy
    rw [hyx] at hy
    exact (conj_mem_conjugateSubgroup_iff L q x).mp hy
  · intro hx
    exact ⟨q * x * q⁻¹, (conj_mem_conjugateSubgroup_iff L q x).2 hx, rfl⟩

/-! ## The free-letter separation behind `H ∩ F = 1` -/

/-- A free letter over `K`, realized as the central HNN extension over the
trivial subgroup.  This is the `K * ⟨q⟩` model for which Britton normal
forms are already available in the repository. -/
abbrev FreeLetterExtension (K : Type) [Group K] : Type :=
  CentHNN (⊥ : Subgroup K)

/-- The subgroup `q L q⁻¹` in `K * ⟨q⟩`. -/
def freeLetterConjugateSubgroup (L : Subgroup K) :
    Subgroup (FreeLetterExtension K) :=
  (L.map (of : K →* FreeLetterExtension K)).map
    (MulAut.conj (t : FreeLetterExtension K)).toMonoidHom

/-- **A free conjugate of any subgroup misses the old base.**  In
`K * ⟨q⟩`, one has `qLq⁻¹ ∩ K = 1`.  This is the precise separation
used by the corrected detector; it is stronger than the required
`qLq⁻¹ ∩ e(F) = 1`.

The proof is a single Britton pinch: if `q l q⁻¹` lies in the base, then
conjugating that base element back by `q` also lies in the base, forcing the
base element into the trivial associated subgroup. -/
theorem freeLetterConjugate_inf_base (L : Subgroup K) :
    freeLetterConjugateSubgroup L ⊓
        MonoidHom.range (of : K →* FreeLetterExtension K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx.2 with ⟨k, hkx⟩
  rcases hx.1 with ⟨y, ⟨l, hl, hly⟩, hyx⟩
  have hconj :
      (t : FreeLetterExtension K) * of l * t⁻¹ = of k := by
    calc
      (t : FreeLetterExtension K) * of l * t⁻¹ =
          (MulAut.conj (t : FreeLetterExtension K)) y := by
            rw [← hly]
            rfl
      _ = x := hyx
      _ = of k := hkx.symm
  have hbase :
      (t : FreeLetterExtension K)⁻¹ * of k * t ∈
        MonoidHom.range (of : K →* FreeLetterExtension K) := by
    refine ⟨l, ?_⟩
    rw [← hconj]
    group
  have hkbot : k ∈ (⊥ : Subgroup K) :=
    mem_of_conj_mem_range (⊥ : Subgroup K) hbase
  have hkone : k = 1 := by simpa using hkbot
  rw [← hkx, hkone, map_one]

/-- The outermost central HNN detector attached to the completed tower `P`. -/
abbrev Extension (L : Subgroup K) (q : K) (j : K →* P) : Type _ :=
  CentHNN (towerSubgroup L q j)

/-- The old word `q e(f) q⁻¹`, first injected into the completed tower. -/
def towerWord (e : F →* K) (q : K) (j : K →* P) (f : F) : P :=
  j (q * e f * q⁻¹)

/-- The detector word as an element of the outer central HNN extension. -/
def detectedWord (L : Subgroup K) (e : F →* K) (q : K)
    (j : K →* P) (f : F) : Extension L q j :=
  of (towerWord e q j f)

/-- **Exact conjugated detector.**  If `L` cuts out `N` on the old copy of
`F`, the outer stable letter commutes with the conjugated word exactly on
`N`.  The proof uses the exact centralizer theorem for a central HNN extension
and injectivity of the completed tower's base map. -/
theorem commute_stable_detectedWord_iff
    (N : Subgroup F) (L : Subgroup K) (e : F →* K) (q : K)
    (j : K →* P) (hj : Function.Injective j)
    (hcut : L.comap e = N) (f : F) :
    Commute (t : Extension L q j) (detectedWord L e q j f) ↔ f ∈ N := by
  unfold detectedWord
  rw [commute_t_of_iff]
  change j (q * e f * q⁻¹) ∈ towerSubgroup L q j ↔ f ∈ N
  rw [map_conj_mem_towerSubgroup_iff L q (e f) j hj]
  change f ∈ L.comap e ↔ f ∈ N
  rw [hcut]

/-- The same theorem with the benign cut written pointwise rather than as an
equality of subgroups. -/
theorem commute_stable_detectedWord_iff_of_mem
    (N : Subgroup F) (L : Subgroup K) (e : F →* K) (q : K)
    (j : K →* P) (hj : Function.Injective j)
    (hcut : ∀ f : F, e f ∈ L ↔ f ∈ N) (f : F) :
    Commute (t : Extension L q j) (detectedWord L e q j f) ↔ f ∈ N := by
  unfold detectedWord
  rw [commute_t_of_iff]
  change j (q * e f * q⁻¹) ∈ towerSubgroup L q j ↔ f ∈ N
  rw [map_conj_mem_towerSubgroup_iff L q (e f) j hj]
  exact hcut f

end ConjugatedDetector
end Higman
end GroupApproximation
