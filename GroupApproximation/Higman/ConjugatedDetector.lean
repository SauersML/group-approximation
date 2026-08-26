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

/-- Membership in the image of a subgroup can be reflected across an
injective homomorphism. -/
theorem map_mem_map_iff_of_injective (A : Subgroup K) (j : K →* P)
    (hj : Function.Injective j) (x : K) :
    j x ∈ A.map j ↔ x ∈ A := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := hj hyx
    simpa [this] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- An injective homomorphism preserves a trivial intersection of subgroups. -/
theorem map_inf_map_eq_bot_of_inf_eq_bot (A B : Subgroup K) (j : K →* P)
    (hj : Function.Injective j) (hAB : A ⊓ B = ⊥) :
    A.map j ⊓ B.map j = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx.1 with ⟨a, ha, rfl⟩
  rcases hx.2 with ⟨b, hb, hba⟩
  have hba' : b = a := hj hba
  subst b
  have haBot : a ∈ A ⊓ B := ⟨ha, hb⟩
  rw [hAB] at haBot
  have haone : a = 1 := by simpa using haBot
  rw [haone, map_one]

/-! ## The free-letter separation behind `H ∩ F = 1` -/

/-- A free letter over `K`, realized as the central HNN extension over the
trivial subgroup.  This is the `K * ⟨q⟩` model for which Britton normal
forms are already available in the repository. -/
abbrev FreeLetterExtension (K : Type) [Group K] : Type :=
  CentHNN (⊥ : Subgroup K)

/-! The description as `K * Z` is not merely mnemonic.  The following maps
identify the trivial-edge central HNN extension with the binary free product.
Keeping this equivalence explicit isolates the analytic permanence theorem
needed by the positive branch from the compiler's group-theoretic encoding. -/

/-- Map the trivial-edge HNN extension to the free product, sending its stable
letter to the generator of the infinite cyclic factor. -/
noncomputable def freeLetterToCoprod :
    FreeLetterExtension K →* Monoid.Coprod K (Multiplicative ℤ) :=
  HNNExtension.lift Monoid.Coprod.inl
    (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) (by
      intro a
      have ha : (a : K) = 1 := Subgroup.mem_bot.mp a.property
      simpa only [ha, map_one, mul_one, one_mul])

/-- Map the free product to the trivial-edge HNN extension. -/
def coprodToFreeLetter :
    Monoid.Coprod K (Multiplicative ℤ) →* FreeLetterExtension K :=
  Monoid.Coprod.lift HNNExtension.of
    (zpowersHom (FreeLetterExtension K) HNNExtension.t)

theorem freeLetterToCoprod_comp_coprodToFreeLetter :
    (freeLetterToCoprod (K := K)).comp coprodToFreeLetter = MonoidHom.id _ := by
  refine Monoid.Coprod.hom_ext ?_ ?_
  · ext k
    simp [freeLetterToCoprod, coprodToFreeLetter]
  · refine MonoidHom.ext_mint ?_
    simp [freeLetterToCoprod, coprodToFreeLetter]

theorem coprodToFreeLetter_comp_freeLetterToCoprod :
    (coprodToFreeLetter (K := K)).comp freeLetterToCoprod = MonoidHom.id _ := by
  refine HNNExtension.hom_ext ?_ ?_
  · ext k
    simp [freeLetterToCoprod, coprodToFreeLetter]
  · simp [freeLetterToCoprod, coprodToFreeLetter]

/-- The free-letter extension is exactly the free product `K * Z`. -/
noncomputable def freeLetterEquivCoprod :
    FreeLetterExtension K ≃* Monoid.Coprod K (Multiplicative ℤ) where
  toFun := freeLetterToCoprod
  invFun := coprodToFreeLetter
  left_inv x := congrArg (fun f : FreeLetterExtension K →* FreeLetterExtension K ↦ f x)
    coprodToFreeLetter_comp_freeLetterToCoprod
  right_inv x := congrArg
    (fun f : Monoid.Coprod K (Multiplicative ℤ) →*
      Monoid.Coprod K (Multiplicative ℤ) ↦ f x)
    freeLetterToCoprod_comp_coprodToFreeLetter
  map_mul' := map_mul _

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

/-- Exact membership in the free-letter conjugate. -/
theorem freeLetter_conj_mem_iff (L : Subgroup K) (x : K) :
    (t : FreeLetterExtension K) * of x * t⁻¹ ∈
        freeLetterConjugateSubgroup L ↔ x ∈ L := by
  change (t : FreeLetterExtension K) * of x * t⁻¹ ∈
      conjugateSubgroup
        (L.map (of : K →* FreeLetterExtension K))
        (t : FreeLetterExtension K) ↔ x ∈ L
  rw [conj_mem_conjugateSubgroup_iff]
  exact map_mem_map_iff_of_injective L
    (of : K →* FreeLetterExtension K)
    (of_injective_centHNN (⊥ : Subgroup K)) x

/-- The old copy of `F` inside the free-letter extension. -/
def freeLetterEmbeddedSubgroup (e : F →* K) :
    Subgroup (FreeLetterExtension K) :=
  MonoidHom.range ((of : K →* FreeLetterExtension K).comp e)

/-- The corrected detector subgroup misses the old copy of `F`, with no
assumption on `e`: `qLq⁻¹ ∩ e(F) = 1`. -/
theorem freeLetterConjugate_inf_embedded (L : Subgroup K) (e : F →* K) :
    freeLetterConjugateSubgroup L ⊓ freeLetterEmbeddedSubgroup e = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxBase : x ∈ MonoidHom.range (of : K →* FreeLetterExtension K) := by
    rcases hx.2 with ⟨f, rfl⟩
    exact ⟨e f, rfl⟩
  have hxBot : x ∈ freeLetterConjugateSubgroup L ⊓
      MonoidHom.range (of : K →* FreeLetterExtension K) := ⟨hx.1, hxBase⟩
  rw [freeLetterConjugate_inf_base L] at hxBot
  simpa using hxBot

/-- The separation `qLq⁻¹ ∩ e(F)=1` survives every subsequent tower
whose base map is injective. -/
theorem tower_freeLetterConjugate_inf_embedded
    (L : Subgroup K) (e : F →* K)
    (j : FreeLetterExtension K →* P) (hj : Function.Injective j) :
    (freeLetterConjugateSubgroup L).map j ⊓
        (freeLetterEmbeddedSubgroup e).map j = ⊥ :=
  map_inf_map_eq_bot_of_inf_eq_bot _ _ j hj
    (freeLetterConjugate_inf_embedded L e)

/-! ## The corrected detector after an arbitrary injected tower -/

/-- The conjugated edge subgroup after the free-letter base has passed through
an arbitrary injective tower. -/
def freeTowerSubgroup (L : Subgroup K)
    (j : FreeLetterExtension K →* P) : Subgroup P :=
  (freeLetterConjugateSubgroup L).map j

/-- Add the corrected detector only after the preceding tower is complete. -/
abbrev FreeOutermostExtension (L : Subgroup K)
    (j : FreeLetterExtension K →* P) : Type :=
  CentHNN (freeTowerSubgroup L j)

/-- The literal conjugated payload in the completed tower. -/
def freeTowerWord (e : F →* K) (j : FreeLetterExtension K →* P)
    (f : F) : P :=
  j ((t : FreeLetterExtension K) * of (e f) * t⁻¹)

/-- The literal conjugated payload in the outer detector extension. -/
def freeDetectedWord (L : Subgroup K) (e : F →* K)
    (j : FreeLetterExtension K →* P) (f : F) :
    FreeOutermostExtension L j :=
  of (freeTowerWord e j f)

/-- **Exact corrected outermost detector.**  For `H=qLq⁻¹` in
`K * ⟨q⟩`, subsequently embedded in any tower, the final central letter
commutes with `q e(f) q⁻¹` exactly when `f ∈ N`.

This statement simultaneously captures the corrected conjugation and the
"detector last" ordering: no earlier tower letter acts on the detector stable
letter. -/
theorem commute_freeStable_freeDetectedWord_iff
    (N : Subgroup F) (L : Subgroup K) (e : F →* K)
    (j : FreeLetterExtension K →* P) (hj : Function.Injective j)
    (hcut : L.comap e = N) (f : F) :
    Commute (t : FreeOutermostExtension L j)
        (freeDetectedWord L e j f) ↔ f ∈ N := by
  unfold freeDetectedWord
  rw [commute_t_of_iff]
  unfold freeTowerWord freeTowerSubgroup
  rw [map_mem_map_iff_of_injective _ j hj]
  rw [freeLetter_conj_mem_iff]
  change f ∈ L.comap e ↔ f ∈ N
  rw [hcut]

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
