import GroupApproximation.PropertyT.IntegralGeneratorShearMass

/-!
# The descent mass inequality

This is the analytic step the integral route was missing.  Let `mu` be the
column-plane spectral measure of a unit vector moved by less than `delta` by
every element of the integral control set.  Then, one degree stage down,

```
sqrt (mu (A ∪ B)ᵢₙₜ) ≤ sqrt (mu (C ∪ D)) + sqrt |X| * delta
```

and symmetrically for `C ∪ B` against `A ∪ D`, where the interior part is the
set of characters whose relevant valuation is already visible at the lower
stage.  The proof cuts the source into the disjoint measurable letter pieces
of `IntegralGeneratorShearSelector`, shears the `i`-th piece by the `i`-th
generator, and applies Kassabov's disjoint-union transport
`KassabovBorelMeasureInequalities.sqrt_measureReal_biUnion_le_of_disjoint_transport`.

Two facts make the cut work.  The placement
`IntegralGeneratorShearDescent.leastRootWordDegreeWithin_lowerGenerator_zero`
puts every image in `C ∪ D` at the lower stage.  The invariance
`IntegralGeneratorShearSelector.descentSet_lowerCharacterAction` puts the
image of the `i`-th piece inside the `i`-th piece of the *target*
decomposition, so the images are pairwise disjoint and the `|X|` pieces share
one copy of the target mass rather than each paying for the whole of it.
This is the integral counterpart of `FreeRootPlaneMass.sum_planeMass_AB_le_coarse_CD`.
-/

namespace GroupApproximation
namespace IntegralGeneratorShearDescentMass

open Set MeasureTheory WeakDual
open IntegralCharacterMass
open IntegralColumnPlaneSpectralMeasure
open IntegralColumnPlaneSpectralShear
open IntegralColumnPlaneSpectralTorus
open IntegralColumnPlaneSpectralMassBound
open IntegralGeneratorShearDescent
open IntegralGeneratorShearSelector
open IntegralGeneratorShearMass
open FreeAlgebraDegree

noncomputable section

universe u v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
variable {X : Type u} [Fintype X]
variable (rho : elementaryGroup (Fin 3) (FreeAlgebra ℤ X) →* (E ≃ₗᵢ[ℝ] E))

noncomputable local instance columnPlaneCharacterMeasurableSpace'' :
    MeasurableSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  borel _

local instance columnPlaneCharacterBorelSpace'' :
    BorelSpace (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  ⟨rfl⟩

noncomputable local instance columnPlaneSpectralMeasureIsFinite''
    (z : E) (hz : ‖z‖ = 1) :
    IsFiniteMeasure (columnPlaneSpectralMeasure rho z hz) := by
  unfold columnPlaneSpectralMeasure
  infer_instance

/-! ### The interior of a region at one stage -/

/-- The characters whose least visible degree in root coordinate `b` is
already attained one stage down. -/
def stageInteriorSet (b : Fin 2) (n : ℕ) :
    Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  {chi | leastRootWordDegreeWithin rho b (n + 1) chi ≤ n}

theorem measurableSet_stageInteriorSet (b : Fin 2) (n : ℕ) :
    MeasurableSet (stageInteriorSet rho b n) := by
  have hset : stageInteriorSet rho b n =
      ⋃ d ∈ (Finset.range (n + 1) : Finset ℕ),
        rootWordDegreeFiber rho b (n + 1) d := by
    ext chi
    constructor
    · intro hchi
      have hchi' : leastRootWordDegreeWithin rho b (n + 1) chi ≤ n := hchi
      have hd : leastRootWordDegreeWithin rho b (n + 1) chi ∈
          (Finset.range (n + 1) : Finset ℕ) :=
        Finset.mem_range.mpr (by omega)
      exact Set.mem_biUnion (Finset.mem_coe.mpr hd) rfl
    · intro hchi
      obtain ⟨d, hd, hfiber⟩ := Set.mem_iUnion₂.mp hchi
      have hdlt := Finset.mem_range.mp (Finset.mem_coe.mp hd)
      change leastRootWordDegreeWithin rho b (n + 1) chi = d at hfiber
      change leastRootWordDegreeWithin rho b (n + 1) chi ≤ n
      omega
  rw [hset]
  exact MeasurableSet.biUnion (Finset.countable_toSet _)
    fun d _ ↦ measurableSet_rootWordDegreeFiber rho b (n + 1) d

/-- The source of the lower descent: the `A ∪ B` region one stage up, cut down
to the characters whose second-coordinate valuation is interior. -/
def lowerDescentSource (n : ℕ) :
    Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  (wordPairRegionSet rho (n + 1) .A ∪ wordPairRegionSet rho (n + 1) .B) ∩
    stageInteriorSet rho 1 n

/-- The source of the upper descent. -/
def upperDescentSource (n : ℕ) :
    Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  (wordPairRegionSet rho (n + 1) .C ∪ wordPairRegionSet rho (n + 1) .B) ∩
    stageInteriorSet rho 0 n

theorem measurableSet_lowerDescentSource (n : ℕ) :
    MeasurableSet (lowerDescentSource rho n) :=
  ((measurableSet_wordPairRegionSet rho (n + 1) .A).union
    (measurableSet_wordPairRegionSet rho (n + 1) .B)).inter
      (measurableSet_stageInteriorSet rho 1 n)

theorem measurableSet_upperDescentSource (n : ℕ) :
    MeasurableSet (upperDescentSource rho n) :=
  ((measurableSet_wordPairRegionSet rho (n + 1) .C).union
    (measurableSet_wordPairRegionSet rho (n + 1) .B)).inter
      (measurableSet_stageInteriorSet rho 0 n)

/-! ### Valuation data of a source character -/

theorem lowerDescentSource_data (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hchi : chi ∈ lowerDescentSource rho n) :
    0 < leastRootWordDegreeWithin rho 1 (n + 1) chi ∧
      leastRootWordDegreeWithin rho 1 (n + 1) chi ≤
        leastRootWordDegreeWithin rho 0 (n + 1) chi ∧
      leastRootWordDegreeWithin rho 1 (n + 1) chi ≤ n ∧
      chi ∈ rootWordVisibleSet rho 1 (n + 1) := by
  obtain ⟨hregion, hint⟩ := hchi
  have hint' : leastRootWordDegreeWithin rho 1 (n + 1) chi ≤ n := hint
  have hdata : 0 < leastRootWordDegreeWithin rho 1 (n + 1) chi ∧
      leastRootWordDegreeWithin rho 1 (n + 1) chi ≤
        leastRootWordDegreeWithin rho 0 (n + 1) chi := by
    rcases hregion with hA | hB
    · obtain ⟨-, hb, hlt⟩ := wordPairRegionOfDegrees_A_data (n + 1) _ _ hA
      exact ⟨by omega, by omega⟩
    · obtain ⟨-, ha, hb, heq⟩ := wordPairRegionOfDegrees_B_data (n + 1) _ _ hB
      exact ⟨by omega, by omega⟩
  refine ⟨hdata.1, hdata.2, hint', ?_⟩
  by_contra hnot
  have hsentinel :=
    leastRootWordDegreeWithin_eq_succ_of_not_mem rho 1 (n + 1) chi hnot
  omega

theorem upperDescentSource_data (n : ℕ)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hchi : chi ∈ upperDescentSource rho n) :
    0 < leastRootWordDegreeWithin rho 0 (n + 1) chi ∧
      leastRootWordDegreeWithin rho 0 (n + 1) chi ≤
        leastRootWordDegreeWithin rho 1 (n + 1) chi ∧
      leastRootWordDegreeWithin rho 0 (n + 1) chi ≤ n ∧
      chi ∈ rootWordVisibleSet rho 0 (n + 1) := by
  obtain ⟨hregion, hint⟩ := hchi
  have hint' : leastRootWordDegreeWithin rho 0 (n + 1) chi ≤ n := hint
  have hdata : 0 < leastRootWordDegreeWithin rho 0 (n + 1) chi ∧
      leastRootWordDegreeWithin rho 0 (n + 1) chi ≤
        leastRootWordDegreeWithin rho 1 (n + 1) chi := by
    rcases hregion with hC | hB
    · obtain ⟨ha, -, hlt⟩ := wordPairRegionOfDegrees_C_data (n + 1) _ _ hC
      exact ⟨by omega, by omega⟩
    · obtain ⟨-, ha, hb, heq⟩ := wordPairRegionOfDegrees_B_data (n + 1) _ _ hB
      exact ⟨by omega, by omega⟩
  refine ⟨hdata.1, hdata.2, hint', ?_⟩
  by_contra hnot
  have hsentinel :=
    leastRootWordDegreeWithin_eq_succ_of_not_mem rho 0 (n + 1) chi hnot
  omega

/-! ### The letter-explicit placement -/

/-- A source character sheared by a letter that realizes its descent lands in
`C ∪ D` one stage down. -/
theorem lowerCharacterAction_mem_regionCD (n : ℕ) (x : X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hchi : chi ∈ lowerDescentSource rho n)
    (hx : chi ∈ descentSet rho 1 (n + 1) x) :
    lowerCharacterAction rho (FreeAlgebra.ι ℤ x) chi ∈
      wordPairRegionSet rho n .C ∪ wordPairRegionSet rho n .D := by
  obtain ⟨hpos, hle, hint, hvis⟩ := lowerDescentSource_data rho n chi hchi
  obtain ⟨w, hlen, hne⟩ := hx
  have hzero := leastRootWordDegreeWithin_lowerGenerator_zero rho (n + 1) n
    chi x hlen hne hle (by omega)
  have hone :
      leastRootWordDegreeWithin rho 1 n
          (lowerCharacterAction rho (FreeAlgebra.ι ℤ x) chi) =
        leastRootWordDegreeWithin rho 1 (n + 1) chi := by
    rw [leastRootWordDegreeWithin_lowerCharacterAction_one]
    exact leastRootWordDegreeWithin_stage_eq rho 1 (n + 1) n chi hvis hint
  rcases Nat.eq_zero_or_pos
      (leastRootWordDegreeWithin rho 1 (n + 1) chi - 1) with h0 | hp
  · right
    change wordPairRegionOfDegrees n _ _ = _
    rw [hzero, hone]
    exact wordPairRegionOfDegrees_eq_D_of_left_zero n _ _ h0
  · left
    change wordPairRegionOfDegrees n _ _ = _
    rw [hzero, hone]
    exact wordPairRegionOfDegrees_eq_C_of_pos_of_lt n _ _ (by omega) (by omega)

/-- The mirror placement for the upper generator shear. -/
theorem upperCharacterAction_mem_regionAD (n : ℕ) (x : X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hchi : chi ∈ upperDescentSource rho n)
    (hx : chi ∈ descentSet rho 0 (n + 1) x) :
    upperCharacterAction rho (FreeAlgebra.ι ℤ x) chi ∈
      wordPairRegionSet rho n .A ∪ wordPairRegionSet rho n .D := by
  obtain ⟨hpos, hle, hint, hvis⟩ := upperDescentSource_data rho n chi hchi
  obtain ⟨w, hlen, hne⟩ := hx
  have hone := leastRootWordDegreeWithin_upperGenerator_one rho (n + 1) n
    chi x hlen hne hle (by omega)
  have hzero :
      leastRootWordDegreeWithin rho 0 n
          (upperCharacterAction rho (FreeAlgebra.ι ℤ x) chi) =
        leastRootWordDegreeWithin rho 0 (n + 1) chi := by
    rw [leastRootWordDegreeWithin_upperCharacterAction_zero]
    exact leastRootWordDegreeWithin_stage_eq rho 0 (n + 1) n chi hvis hint
  rcases Nat.eq_zero_or_pos
      (leastRootWordDegreeWithin rho 0 (n + 1) chi - 1) with h0 | hp
  · right
    change wordPairRegionOfDegrees n _ _ = _
    rw [hzero, hone]
    exact wordPairRegionOfDegrees_eq_D_of_right_zero n _ _ h0
  · left
    change wordPairRegionOfDegrees n _ _ = _
    rw [hzero, hone]
    exact wordPairRegionOfDegrees_eq_A_of_pos_of_lt n _ _ (by omega) (by omega)

/-! ### The image of a letter piece stays in that letter's piece -/

theorem descentPiece_lowerCharacterAction (n : ℕ)
    (i : Fin (Fintype.card X)) (r : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho 1 (n + 1))
    (hint : leastRootWordDegreeWithin rho 1 (n + 1) chi ≤ n)
    (hchi : chi ∈ descentPiece rho 1 (n + 1) i) :
    lowerCharacterAction rho r chi ∈ descentPiece rho 1 n i := by
  have hstage : leastRootWordDegreeWithin rho 1 n chi =
      leastRootWordDegreeWithin rho 1 (n + 1) chi :=
    leastRootWordDegreeWithin_stage_eq rho 1 (n + 1) n chi hvis hint
  have hiff : ∀ y : X,
      lowerCharacterAction rho r chi ∈ descentSet rho 1 n y ↔
        chi ∈ descentSet rho 1 (n + 1) y := by
    intro y
    rw [descentSet_lowerCharacterAction]
    exact descentSet_stage_congr rho 1 (n + 1) n y chi hstage
  refine ⟨(hiff _).mpr hchi.1, ?_⟩
  intro hmem
  obtain ⟨j, hj, hjmem⟩ := Set.mem_iUnion₂.mp hmem
  exact hchi.2 (Set.mem_biUnion hj ((hiff _).mp hjmem))

theorem descentPiece_upperCharacterAction (n : ℕ)
    (i : Fin (Fintype.card X)) (r : FreeAlgebra ℤ X)
    (chi : characterSpace ℂ (representedColumnPlane rho).algebra)
    (hvis : chi ∈ rootWordVisibleSet rho 0 (n + 1))
    (hint : leastRootWordDegreeWithin rho 0 (n + 1) chi ≤ n)
    (hchi : chi ∈ descentPiece rho 0 (n + 1) i) :
    upperCharacterAction rho r chi ∈ descentPiece rho 0 n i := by
  have hstage : leastRootWordDegreeWithin rho 0 n chi =
      leastRootWordDegreeWithin rho 0 (n + 1) chi :=
    leastRootWordDegreeWithin_stage_eq rho 0 (n + 1) n chi hvis hint
  have hiff : ∀ y : X,
      upperCharacterAction rho r chi ∈ descentSet rho 0 n y ↔
        chi ∈ descentSet rho 0 (n + 1) y := by
    intro y
    rw [descentSet_upperCharacterAction]
    exact descentSet_stage_congr rho 0 (n + 1) n y chi hstage
  refine ⟨(hiff _).mpr hchi.1, ?_⟩
  intro hmem
  obtain ⟨j, hj, hjmem⟩ := Set.mem_iUnion₂.mp hmem
  exact hchi.2 (Set.mem_biUnion hj ((hiff _).mp hjmem))

/-! ### The descent mass inequality -/

/-- The letter pieces of the lower descent source. -/
def lowerDescentPart (n : ℕ) (i : Fin (Fintype.card X)) :
    Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  lowerDescentSource rho n ∩ descentPiece rho 1 (n + 1) i

/-- The letter pieces of the upper descent source. -/
def upperDescentPart (n : ℕ) (i : Fin (Fintype.card X)) :
    Set (characterSpace ℂ (representedColumnPlane rho).algebra) :=
  upperDescentSource rho n ∩ descentPiece rho 0 (n + 1) i

theorem iUnion_lowerDescentPart (n : ℕ) :
    ⋃ i ∈ (Finset.univ : Finset (Fin (Fintype.card X))),
        lowerDescentPart rho n i = lowerDescentSource rho n := by
  ext chi
  constructor
  · intro hchi
    obtain ⟨i, -, hmem⟩ := Set.mem_iUnion₂.mp hchi
    exact hmem.1
  · intro hchi
    obtain ⟨hpos, -, -, hvis⟩ := lowerDescentSource_data rho n chi hchi
    obtain ⟨i, hi⟩ := exists_mem_descentPiece rho 1 (n + 1) chi hvis hpos
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) ⟨hchi, hi⟩

theorem iUnion_upperDescentPart (n : ℕ) :
    ⋃ i ∈ (Finset.univ : Finset (Fin (Fintype.card X))),
        upperDescentPart rho n i = upperDescentSource rho n := by
  ext chi
  constructor
  · intro hchi
    obtain ⟨i, -, hmem⟩ := Set.mem_iUnion₂.mp hchi
    exact hmem.1
  · intro hchi
    obtain ⟨hpos, -, -, hvis⟩ := upperDescentSource_data rho n chi hchi
    obtain ⟨i, hi⟩ := exists_mem_descentPiece rho 0 (n + 1) chi hvis hpos
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ i)) ⟨hchi, hi⟩

/-- **The lower descent mass inequality.**  The interior `A ∪ B` mass one
stage up is dominated by the `C ∪ D` mass one stage down, at the cost of
`sqrt |X| * delta`. -/
theorem sqrt_measureReal_lowerDescentSource_le
    (z : E) (hz : ‖z‖ = 1) (n : ℕ) (delta : ℝ) (hdelta : 0 < delta)
    (hnear : ∀ s ∈ integralControlSet X, ‖rho s z - z‖ < delta) :
    Real.sqrt ((columnPlaneSpectralMeasure rho z hz).real
        (lowerDescentSource rho n)) ≤
      Real.sqrt ((columnPlaneSpectralMeasure rho z hz).real
        (wordPairRegionSet rho n .C ∪ wordPairRegionSet rho n .D)) +
        Real.sqrt (Fintype.card X : ℝ) * delta := by
  classical
  set mu := columnPlaneSpectralMeasure rho z hz with hmu
  set g : Fin (Fintype.card X) →
      Equiv.Perm (characterSpace ℂ (representedColumnPlane rho).algebra) :=
    fun i ↦ (lowerCharacterMeasurableEquiv rho
      (FreeAlgebra.ι ℤ ((letterIndex (X := X)).symm i))).toEquiv with hg
  have hgapply : ∀ i chi, g i chi =
      lowerCharacterAction rho
        (FreeAlgebra.ι ℤ ((letterIndex (X := X)).symm i)) chi :=
    fun _ _ ↦ rfl
  have hmeasurable : ∀ i : Fin (Fintype.card X),
      MeasurableSet (lowerDescentPart rho n i) :=
    fun i ↦ (measurableSet_lowerDescentSource rho n).inter
      (measurableSet_descentPiece rho 1 (n + 1) i)
  have himage : ∀ i : Fin (Fintype.card X),
      MeasurableSet (g i '' lowerDescentPart rho n i) := by
    intro i
    exact (MeasurableEquiv.measurableSet_image
      (lowerCharacterMeasurableEquiv rho
        (FreeAlgebra.ι ℤ ((letterIndex (X := X)).symm i)))).mpr
      (hmeasurable i)
  have himagePiece : ∀ (i : Fin (Fintype.card X)) (chi),
      chi ∈ lowerDescentPart rho n i →
        g i chi ∈ descentPiece rho 1 n i := by
    intro i chi hchi
    obtain ⟨-, -, hint, hvis⟩ := lowerDescentSource_data rho n chi hchi.1
    exact descentPiece_lowerCharacterAction rho n i _ chi hvis hint hchi.2
  have hdisjA : Set.Pairwise (↑(Finset.univ : Finset (Fin (Fintype.card X))))
      fun i j ↦ Disjoint (lowerDescentPart rho n i) (lowerDescentPart rho n j) := by
    intro i _ j _ hij
    exact Set.disjoint_of_subset (fun _ h ↦ h.2) (fun _ h ↦ h.2)
      (disjoint_descentPiece rho 1 (n + 1) hij)
  have hdisjImage : Set.Pairwise (↑(Finset.univ : Finset (Fin (Fintype.card X))))
      fun i j ↦ Disjoint (g i '' lowerDescentPart rho n i)
        (g j '' lowerDescentPart rho n j) := by
    intro i _ j _ hij
    refine Set.disjoint_of_subset ?_ ?_ (disjoint_descentPiece rho 1 n hij)
    · rintro _ ⟨chi, hchi, rfl⟩
      exact himagePiece i chi hchi
    · rintro _ ⟨chi, hchi, rfl⟩
      exact himagePiece j chi hchi
  have hsubset : (⋃ i ∈ (Finset.univ : Finset (Fin (Fintype.card X))),
      g i '' lowerDescentPart rho n i) ⊆
        wordPairRegionSet rho n .C ∪ wordPairRegionSet rho n .D := by
    rintro y hy
    obtain ⟨i, -, chi, hchi, rfl⟩ := Set.mem_iUnion₂.mp hy
    rw [hgapply]
    exact lowerCharacterAction_mem_regionCD rho n _ chi hchi.1
      (descentPiece_subset rho 1 (n + 1) i hchi.2)
  have hquasi : ∀ i ∈ (Finset.univ : Finset (Fin (Fintype.card X))),
      KassabovBorelMeasureInequalities.MeasurableQuasiInvariantAtScale mu delta
        (g i).symm := by
    intro i _ A hA himageA
    have hfun : ∀ chi, (g i).symm chi =
        lowerCharacterMeasurableEquiv rho
          (-(FreeAlgebra.ι ℤ ((letterIndex (X := X)).symm i))) chi := by
      intro chi
      exact lowerCharacterMeasurableEquiv_symm_apply rho _ chi
    have hset : (g i).symm '' A =
        lowerCharacterMeasurableEquiv rho
          (-(FreeAlgebra.ι ℤ ((letterIndex (X := X)).symm i))) '' A :=
      Set.image_congr' hfun
    rw [hset]
    rw [hset] at himageA
    exact lowerShear_neg_control_measurableQuasiInvariantAtScale rho z hz delta
      hdelta hnear (some ((letterIndex (X := X)).symm i)) A hA himageA
  have hmain :=
    KassabovBorelMeasureInequalities.sqrt_measureReal_biUnion_le_of_disjoint_transport
      mu Finset.univ (lowerDescentPart rho n)
      (wordPairRegionSet rho n .C ∪ wordPairRegionSet rho n .D) g hdelta.le
      (fun i _ ↦ hmeasurable i) (fun i _ ↦ himage i) hdisjA hdisjImage hsubset
      hquasi
  rw [iUnion_lowerDescentPart rho n] at hmain
  simpa using hmain

end

end IntegralGeneratorShearDescentMass
end GroupApproximation
