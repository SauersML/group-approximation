import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.Relative
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.StableReduction.StableKTwo
import GroupApproximation.Meta.AxiomGuard

/-!
# Stable `K₂(L)` from stable `K₂(C_2)` and relative `K₁(C_2, (p))`

Lane `sk-leavitt-18`, fifth module.  Write `C = C_2(𝔽₂)`, `L = L_{𝔽₂}(1,2)`,
`π = toLeavitt : C → L` and `I = (p) = ker π`.

Route (finite-stage Milnor argument, no colimit needed).  Let `k ∈ K₂(n, L)`.
1. Pad `k` to rank `n + 2` (`indexMap_mem_K2`) and lift it to `x ∈ St_{n+2}(C)` (`π` is onto).
2. `g = projection x` maps to `1` over `L`, so `g ≡ 1 (mod I)` entrywise, and likewise `g⁻¹`
   (`sub_one_mem_pIdeal_of_map_eq_one`).
3. **Relative `K₁`** (`CohnRelativeKOneTrivialStatement`): `g ∈ EL_{n+2}(C, I)`.  Hence
   (`relativeElementary_le_map_ker`) `g = projection t` with `ringMap π t = 1`.
4. `x t⁻¹ ∈ K₂(n + 2, C)`.  **Stable `K₂(C)`** (`BinaryCohnStableK2TrivialStatement`) gives
   `N` with `x = t` in `St_N(C)`.  Hence the image of `k` in `St_N(L)` is `π t = 1`.

`binaryLeavittStableK2Trivial_of_cohn` records this.  The relative `K₁` hypothesis is
discharged in `RelativeKOne.lean` from lane `sk-leavitt-19`'s excision theorem.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

/-- **Stable `K₂(C_2(𝔽₂)) = 0`**, in the same finite-stage form as
`BinaryLeavittStableK2TrivialStatement`: every `k ∈ K₂(n, C_2)` becomes trivial in some
`St_N(C_2)`, `n ≤ N`.

*Why it is true.*  The inclusion `𝔽₂ → C_2(𝔽₂)` induces an isomorphism on algebraic `K`-theory
(Ara–Brustenga–Cortiñas 2009, the Cohn algebra is `K`-equivalent to the base field), and
`K₂(𝔽₂) = 0` (Steinberg symbols over a finite field).  Finite stages detect the stable
group because a filtered colimit of groups kills an element iff some stage does.  Not proved
in Lean. -/
def BinaryCohnStableK2TrivialStatement : Prop :=
  ∀ (n : ℕ) (k : GroupApproximation.SteinbergGroup (Fin n) (CohnTwo (ZMod 2))),
    k ∈ GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin n) (CohnTwo (ZMod 2)) →
    ∃ (N : ℕ) (h : n ≤ N), GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb h) k = 1

/-- **Relative `K₁(C_2, (p)) = 0`** at every finite rank `n ≥ 2`: an invertible matrix
congruent to `1` modulo `(p)`, with inverse also congruent to `1`, lies in the relative
elementary group `EL_n(C_2, (p))`.  This is lane `sk-leavitt-19`'s interface.  It is proved in
`RelativeKOne.lean` (`cohnRelativeKOneTrivial`). -/
def CohnRelativeKOneTrivialStatement : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ u : (Matrix (Fin n) (Fin n) (CohnTwo (ZMod 2)))ˣ,
    (∀ i j, ((u : Matrix (Fin n) (Fin n) (CohnTwo (ZMod 2))) - 1) i j ∈
      CohnTwo.pIdeal (ZMod 2)) →
    (∀ i j, (((u⁻¹ : (Matrix (Fin n) (Fin n) (CohnTwo (ZMod 2)))ˣ) :
        Matrix (Fin n) (Fin n) (CohnTwo (ZMod 2))) - 1) i j ∈ CohnTwo.pIdeal (ZMod 2)) →
    ∃ g ∈ relativeElementary (Fin n) (CohnTwo.pIdeal (ZMod 2)),
      (g : (Matrix (Fin n) (Fin n) (CohnTwo (ZMod 2)))ˣ) = u

namespace CohnTwo

/-- Steps 2–3: a Steinberg element over `C_2` whose image over `L` lies in `K₂` has the same
projection as some element of `ker (St_n(C_2) → St_n(L))`. -/
theorem projection_lift_of_relativeKOne (hK : CohnRelativeKOneTrivialStatement) {n : ℕ}
    (hn : 2 ≤ n) (x : GroupApproximation.SteinbergGroup (Fin n) (CohnTwo (ZMod 2)))
    (hx : GroupApproximation.SteinbergGroup.ringMap (toLeavitt (ZMod 2)).toRingHom x ∈
      GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin n)
        (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) :
    ∃ t : GroupApproximation.SteinbergGroup (Fin n) (CohnTwo (ZMod 2)),
      GroupApproximation.SteinbergGroup.ringMap (toLeavitt (ZMod 2)).toRingHom t = 1 ∧
        GroupApproximation.SteinbergGroup.projection t =
          GroupApproximation.SteinbergGroup.projection x := by
  have hg : elementaryGroupMap (toLeavitt (ZMod 2)).toRingHom
      (GroupApproximation.SteinbergGroup.projection x) = 1 := by
    rw [← GroupApproximation.BooneHigman.SteinbergBasic.projection_ringMap]
    exact (GroupApproximation.BooneHigman.SteinbergBasic.mem_K2_iff _).mp hx
  have hU : elementaryMatrixUnitMap (toLeavitt (ZMod 2)).toRingHom
      ((GroupApproximation.SteinbergGroup.projection x :
          elementaryGroup (Fin n) (CohnTwo (ZMod 2))) :
        (Matrix (Fin n) (Fin n) (CohnTwo (ZMod 2)))ˣ) = 1 := by
    have h := congrArg
      (fun z : elementaryGroup (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) =>
        (z : (Matrix (Fin n) (Fin n) (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)))ˣ)) hg
    exact h
  have hU' : elementaryMatrixUnitMap (toLeavitt (ZMod 2)).toRingHom
      ((GroupApproximation.SteinbergGroup.projection x :
          elementaryGroup (Fin n) (CohnTwo (ZMod 2))) :
        (Matrix (Fin n) (Fin n) (CohnTwo (ZMod 2)))ˣ)⁻¹ = 1 := by
    rw [map_inv, hU, inv_one]
  obtain ⟨g, hgmem, hgu⟩ := hK n hn _ (sub_one_mem_pIdeal_of_map_eq_one (ZMod 2) _ hU)
    (sub_one_mem_pIdeal_of_map_eq_one (ZMod 2) _ hU')
  obtain ⟨t, ht, hpt⟩ := Subgroup.mem_map.mp (relativeElementary_le_map_ker (ZMod 2) n hgmem)
  refine ⟨t, (MonoidHom.mem_ker).mp ht, ?_⟩
  rw [hpt]
  exact Subtype.ext hgu

end CohnTwo

/-- **Lane endpoint.** Stable `K₂(C_2(𝔽₂)) = 0` and relative `K₁(C_2, (p)) = 0` give stable
`K₂(L_{𝔽₂}(1,2)) = 0`. -/
theorem binaryLeavittStableK2Trivial_of_cohn (hS : BinaryCohnStableK2TrivialStatement)
    (hK : CohnRelativeKOneTrivialStatement) : BinaryLeavittStableK2TrivialStatement := by
  intro n k hk
  have hk2 := GroupApproximation.BooneHigman.SteinbergBasic.indexMap_mem_K2
    (Fin.castLEEmb (Nat.le_add_right n 2)) hk
  obtain ⟨x, hx⟩ := GroupApproximation.SteinbergGroup.ringMap_surjective_of_surjective
    (I := Fin (n + 2)) (CohnTwo.toLeavitt (ZMod 2)).toRingHom
    (CohnTwo.toLeavitt_surjective (ZMod 2))
    (GroupApproximation.SteinbergGroup.indexMap (Fin.castLEEmb (Nat.le_add_right n 2)) k)
  rw [← hx] at hk2
  obtain ⟨t, ht1, htx⟩ :=
    CohnTwo.projection_lift_of_relativeKOne hK (Nat.le_add_left 2 n) x hk2
  have hxt : x * t⁻¹ ∈
      GroupApproximation.BooneHigman.SteinbergBasic.K2 (Fin (n + 2)) (CohnTwo (ZMod 2)) := by
    rw [GroupApproximation.BooneHigman.SteinbergBasic.mem_K2_iff, map_mul, map_inv, htx,
      mul_inv_cancel]
  obtain ⟨N, hN, hNx⟩ := hS (n + 2) (x * t⁻¹) hxt
  rw [map_mul, map_inv, mul_inv_eq_one] at hNx
  refine ⟨N, (Nat.le_add_right n 2).trans hN, ?_⟩
  rw [← CohnTwo.indexMap_castLE_castLE (Nat.le_add_right n 2) hN, ← hx,
    CohnTwo.indexMap_castLE_ringMap, hNx, ← CohnTwo.indexMap_castLE_ringMap, ht1, map_one]

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.BinaryCohnStableK2TrivialStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnRelativeKOneTrivialStatement
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.CohnTwo.projection_lift_of_relativeKOne
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.binaryLeavittStableK2Trivial_of_cohn
