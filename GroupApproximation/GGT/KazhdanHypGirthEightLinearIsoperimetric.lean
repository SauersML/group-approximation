import GroupApproximation.GGT.KazhdanHypGirthEightFromDiagram
import GroupApproximation.Sofic.GreendlingerIsoperimetric
import GroupApproximation.Algebra.HyperbolicTransport
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import GroupApproximation.Meta.AxiomGuard

/-!
# The linear isoperimetric inequality of a checked triangular presentation

A table passing `GirthEightChecks` gives the curvature bound
`rCellCount ≤ 3 * boundaryWord.length` for every disc diagram carrying
`TriangularDiagramLocalData` (`KazhdanHypGirthEightFromDiagram.lean`).  This
module turns that bound into the algebraic linear isoperimetric inequality of
`Sofic/GreendlingerIsoperimetric.lean`,

`LinearIsoperimetric (symmetrizedRelators T) 3`:

every element of the relator subgroup is a product of at most `3 * |g|`
conjugates of relators and their inverses.

## The one input

`CyclicallyReducedLocalDataFilling T` asks that a nonempty cyclically reduced
word that is trivial in the presented group bound a disc diagram whose outer
word is the word itself and which carries triangular local data.  It is the
filling half of van Kampen's lemma with cellular reduction, and it is exactly
the first two conclusions of `KazhdanHypLiteralFilling.LeastLiteralDiscLocalData`
(the torsion lane's producer, which adds a minimality clause).  Cyclic
reducedness is needed: at a boundary spur the local datum
`boundaryVertexDegree` fails, and a spur is a cancelling pair in the cyclic
boundary word.

## The argument

Given `g` in the relator subgroup, Mathlib's `reduceCyclically` writes
`g = c * mk w * c⁻¹` with `w` cyclically reduced and `|w| ≤ |g|`.  The word `w`
is trivial in the presented group, so it bounds a diagram `Δ` with local data,
and `Δ.boundary_product` spells `mk w` as the product of the `Δ.rCellCount`
signed conjugates stored in the relator cells, each a conjugate of a triangle
relator or of its inverse.  Conjugating every factor by `c` gives `g`, and the
curvature bound gives `rCellCount ≤ 3 * |w| ≤ 3 * |g|`.  Nothing here is
planar: the diagram is used only through its stored product and its area.
-/

set_option linter.unusedSectionVars false

namespace GroupApproximation
namespace GGT
namespace KazhdanHypGirthEightLinearIsoperimetric

open GroupApproximation.KazhdanHyp
open GroupApproximation.SmallCancellationRouter
open GGT.VanKampen

/-! ## Algebraic area -/

section Algebraic

variable {α : Type*}

/-- A list of conjugates of members of `R` is a conjugate product of its own
length. -/
theorem isConjugateProduct_of_forall {R : Set (FreeGroup α)} (l : List (FreeGroup α))
    (h : ∀ x ∈ l, ∃ c s : FreeGroup α, s ∈ R ∧ x = c * s * c⁻¹) :
    IsConjugateProduct R l.length l.prod := by
  induction l with
  | nil => exact List.prod_nil
  | cons x l ih =>
      obtain ⟨c, s, hs, hx⟩ := h x (by simp)
      rw [List.length_cons, List.prod_cons]
      show ∃ c' s' h' : FreeGroup α,
        s' ∈ R ∧ x * l.prod = c' * s' * c'⁻¹ * h' ∧
          IsConjugateProduct R l.length h'
      exact ⟨c, s, l.prod, hs, by rw [hx], ih (fun y hy => h y (by simp [hy]))⟩

/-- Conjugation preserves the algebraic area. -/
theorem isConjugateProduct_conj {R : Set (FreeGroup α)} (c : FreeGroup α) {n : ℕ}
    {g : FreeGroup α} (hg : IsConjugateProduct R n g) :
    IsConjugateProduct R n (c * g * c⁻¹) := by
  induction n generalizing g with
  | zero =>
      have hg' : g = 1 := hg
      show c * g * c⁻¹ = 1
      rw [hg', mul_one, mul_inv_cancel]
  | succ n ih =>
      have hg' : ∃ c₁ s h₁ : FreeGroup α,
          s ∈ R ∧ g = c₁ * s * c₁⁻¹ * h₁ ∧ IsConjugateProduct R n h₁ := hg
      obtain ⟨c₁, s, h₁, hs, hsplit, hrest⟩ := hg'
      show ∃ c' s' h' : FreeGroup α,
        s' ∈ R ∧ c * g * c⁻¹ = c' * s' * c'⁻¹ * h' ∧
          IsConjugateProduct R n h'
      exact ⟨c * c₁, s, c * h₁ * c⁻¹, hs, by rw [hsplit]; group, ih hrest⟩

/-- Every element of a free group is a conjugate of a cyclically reduced word
that is no longer than it. -/
theorem exists_cyclicallyReduced_conj [DecidableEq α] (g : FreeGroup α) :
    ∃ (c : FreeGroup α) (w : List (α × Bool)),
      g = c * FreeGroup.mk w * c⁻¹ ∧ FreeGroup.IsCyclicallyReduced w ∧
        w.length ≤ FreeGroup.norm g := by
  refine ⟨FreeGroup.mk (FreeGroup.reduceCyclically.conjugator g.toWord),
    FreeGroup.reduceCyclically g.toWord, ?_,
    FreeGroup.reduceCyclically.isCyclicallyReduced FreeGroup.isReduced_toWord, ?_⟩
  · have hconj :=
      FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically g.toWord
    conv_lhs => rw [← FreeGroup.mk_toWord (x := g), ← hconj]
    rw [FreeGroup.inv_mk, FreeGroup.mul_mk, FreeGroup.mul_mk]
  · have h1 := congrArg List.length
      (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically g.toWord)
    simp only [List.length_append, FreeGroup.invRev_length] at h1
    show (FreeGroup.reduceCyclically g.toWord).length ≤ g.toWord.length
    omega

end Algebraic

/-! ## Triangle relators -/

section Table

variable {Generator TriangleIndex : Type}
  [Fintype Generator] [DecidableEq Generator]
  [Fintype TriangleIndex] [DecidableEq TriangleIndex]

/-- The defining relators of a triangle table together with their inverses. -/
def symmetrizedRelators
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    Set (FreeGroup Generator) :=
  (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) ∪
    (fun r => r⁻¹) '' (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))

/-- Adjoining inverses does not change the relator subgroup. -/
theorem normalClosure_symmetrizedRelators
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) :
    Subgroup.normalClosure (symmetrizedRelators T) =
      Subgroup.normalClosure
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x (hx | ⟨r, hr, rfl⟩)
    · exact Subgroup.subset_normalClosure hx
    · exact Subgroup.inv_mem _ (Subgroup.subset_normalClosure hr)
  · exact Subgroup.normalClosure_mono Set.subset_union_left

/-- Reading a signed word letter by letter through `signedFreeRelLetter`
spells the free-group element of the word. -/
theorem listVal_map_signedFreeRelLetter :
    ∀ w : List (TriangularHodgeLayer.SignedGenerator Generator),
      GGT.RelLetter.listVal (w.map signedFreeRelLetter) =
        PresentedGroupRelatorReplay.word w
  | [] => rfl
  | u :: w => by
      have ih := listVal_map_signedFreeRelLetter w
      have hhead : GGT.RelLetter.listVal ((u :: w).map signedFreeRelLetter) =
          FoxBoundary.letterValue FreeGroup.of u *
            GGT.RelLetter.listVal (w.map signedFreeRelLetter) := by
        show ((u :: w).map signedFreeRelLetter |>.map GGT.RelLetter.val).prod =
          FoxBoundary.letterValue FreeGroup.of u *
            ((w.map signedFreeRelLetter).map GGT.RelLetter.val).prod
        rw [List.map_cons, List.map_cons, List.prod_cons]
        rfl
      have hletter : FoxBoundary.letterValue FreeGroup.of u = FreeGroup.mk [u] := by
        obtain ⟨a, b⟩ := u
        cases b
        · show (FreeGroup.of a)⁻¹ = FreeGroup.mk [(a, false)]
          show (FreeGroup.mk [(a, true)])⁻¹ = FreeGroup.mk [(a, false)]
          rw [FreeGroup.inv_mk]
          rfl
        · rfl
      rw [hhead, ih, hletter]
      show FreeGroup.mk [u] * FreeGroup.mk w = FreeGroup.mk (u :: w)
      rw [FreeGroup.mul_mk]
      rfl

/-- The value of a literal triangle word is its relator. -/
theorem listVal_triangleRelatorWord
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator)
    (j : TriangleIndex) :
    GGT.RelLetter.listVal (triangleRelatorWord T j) =
      TriangularHodgeLayer.relator (T j) :=
  listVal_map_signedFreeRelLetter (TriangularHodgeLayer.letters (T j))

/-- A relator cell over the triangle words contributes a conjugate of a relator
or of its inverse. -/
theorem relatorCell_value_mem
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator}
    {M : CombMap} {outer : M.Face}
    (C : RelatorCell M outer (triangleRelatorWords T)) :
    ∃ c s : FreeGroup Generator,
      s ∈ symmetrizedRelators T ∧ C.value = c * s * c⁻¹ := by
  obtain ⟨j, hj⟩ := C.word_mem
  have hval : GGT.RelLetter.listVal C.word = TriangularHodgeLayer.relator (T j) := by
    rw [← hj]
    exact listVal_triangleRelatorWord T j
  have hmem : TriangularHodgeLayer.relator (T j) ∈
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) :=
    Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  cases hrev : C.reversed
  · refine ⟨C.conjugator, TriangularHodgeLayer.relator (T j), Or.inl hmem, ?_⟩
    simp [RelatorCell.value, hrev, hval]
  · refine ⟨C.conjugator, (TriangularHodgeLayer.relator (T j))⁻¹,
      Or.inr ⟨_, hmem, rfl⟩, ?_⟩
    simp [RelatorCell.value, hrev, hval]

/-! ## The inequality -/

/-- **The filling input.**  Every nonempty cyclically reduced word that is
trivial in the presented group is the outer word of a disc diagram carrying
triangular local data.  The torsion lane's
`KazhdanHypLiteralFilling.LeastLiteralDiscLocalData` supplies it at every
checked table. -/
def CyclicallyReducedLocalDataFilling
    (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) : Prop :=
  ∀ word : List (TriangularHodgeLayer.SignedGenerator Generator),
    word ≠ [] → FreeGroup.IsCyclicallyReduced word →
    PresentedGroup.mk (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word word) = 1 →
    ∃ Δ : VanKampen.DiscDiagram.{0, 0, 0} (triangleRelatorWords T),
      Δ.boundaryWord = word.map signedFreeRelLetter ∧
        Nonempty (TriangularDiagramLocalData T Δ)

/-- **Linear isoperimetric inequality, constant three.**  At a table passing
`GirthEightChecks`, the filling input gives every element of the relator
subgroup as a product of at most `3 * |g|` conjugates of relators and their
inverses. -/
theorem linearIsoperimetric_of_localDataFilling
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} {d : ℕ}
    (hchecks : GirthEightChecks T d)
    (hfill : CyclicallyReducedLocalDataFilling T) :
    LinearIsoperimetric (symmetrizedRelators T) 3 := by
  intro g hg
  rw [normalClosure_symmetrizedRelators] at hg
  obtain ⟨c, w, hg_eq, hcyc, hwlen⟩ := exists_cyclicallyReduced_conj g
  have hwmem : FreeGroup.mk w ∈ Subgroup.normalClosure
      (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)) := by
    have hrewrite : FreeGroup.mk w = c⁻¹ * g * c⁻¹⁻¹ := by
      rw [hg_eq]
      group
    rw [hrewrite]
    exact (Subgroup.normalClosure_normal).conj_mem g hg c⁻¹
  by_cases hw : w = []
  · refine ⟨0, Nat.zero_le _, ?_⟩
    show g = 1
    rw [hg_eq, hw, ← FreeGroup.one_eq_mk, mul_one, mul_inv_cancel]
  · have htriv : PresentedGroup.mk
        (TriangularHodgeLayer.relators T : Set (FreeGroup Generator))
        (PresentedGroupRelatorReplay.word w) = 1 :=
      PresentedGroup.mk_eq_one_iff.mpr hwmem
    obtain ⟨Δ, hbd, ⟨Lloc⟩⟩ := hfill w hw hcyc htriv
    have hcells : Δ.rCellCount ≤ 3 * Δ.boundaryWord.length :=
      Lloc.rCellCount_le_three_mul_boundaryWord_length hchecks
    have hbdlen : Δ.boundaryWord.length = w.length := by
      rw [hbd, List.length_map]
    have hval : Δ.boundaryValue = FreeGroup.mk w := by
      show GGT.RelLetter.listVal Δ.boundaryWord = FreeGroup.mk w
      rw [hbd]
      exact listVal_map_signedFreeRelLetter w
    refine ⟨Δ.rCellCount, by omega, ?_⟩
    rw [hg_eq]
    apply isConjugateProduct_conj
    have hprod := Δ.relatorValues_prod_eq_boundaryValue
    rw [hval] at hprod
    rw [← hprod]
    have hlen : Δ.rCellCount = (Δ.relatorCells.map RelatorCell.value).length := by
      rw [List.length_map]
      rfl
    rw [hlen]
    apply isConjugateProduct_of_forall
    intro x hx
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hx
    exact relatorCell_value_mem C

/-- Every symmetrized triangle relator has norm at most three. -/
theorem norm_le_three_of_mem_symmetrizedRelators
    {T : TriangleIndex → TriangularHodgeLayer.Triangle Generator} :
    ∀ r ∈ symmetrizedRelators T, FreeGroup.norm r ≤ 3 := by
  have hrel : ∀ j : TriangleIndex,
      FreeGroup.norm (TriangularHodgeLayer.relator (T j)) ≤ 3 := by
    intro j
    show FreeGroup.norm (FreeGroup.mk (TriangularHodgeLayer.letters (T j))) ≤ 3
    have h := FreeGroup.norm_mk_le (L₁ := TriangularHodgeLayer.letters (T j))
    simpa [TriangularHodgeLayer.letters_eq_three] using h
  rintro r (hr | ⟨s, hs, rfl⟩)
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hr)
    exact hrel j
  · obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hs)
    show FreeGroup.norm ((TriangularHodgeLayer.relator (T j))⁻¹) ≤ 3
    rw [FreeGroup.norm_inv_eq]
    exact hrel j

end Table

/-! ## Hyperbolicity from Gromov's theorem -/

/-- **Gromov's theorem in the form consumed here**: a finite alphabet, relators
of bounded norm, and a linear isoperimetric inequality make the presented group
hyperbolic.  The hull-bridge lane builds it as
`isHyperbolicGroup_presentedGroup_of_linearIsoperimetric`. -/
def LinearIsoperimetricHyperbolicityStatement : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (R : Set (FreeGroup α)),
    (∃ L : ℕ, ∀ r ∈ R, FreeGroup.norm r ≤ L) → ∀ K : ℕ,
      LinearIsoperimetric R K → Hyperbolic.IsHyperbolicGroup (PresentedGroup R)

/-- **`GirthEightHyperbolicity` from the filling input and Gromov's theorem.**
The inequality is proved for the symmetrized relators, and adjoining inverses
leaves the presented group unchanged. -/
theorem girthEightHyperbolicity_of_localDataFilling
    (hgromov : LinearIsoperimetricHyperbolicityStatement)
    (hfill : ∀ (Generator TriangleIndex : Type) (_ : Fintype Generator)
      (_ : DecidableEq Generator) (_ : Fintype TriangleIndex)
      (_ : DecidableEq TriangleIndex)
      (T : TriangleIndex → TriangularHodgeLayer.Triangle Generator) (d : ℕ),
      GirthEightChecks T d → CyclicallyReducedLocalDataFilling T) :
    GirthEightHyperbolicity := by
  intro Generator TriangleIndex fg dg _ng ft dt T d hchecks
  have hiso := linearIsoperimetric_of_localDataFilling hchecks
    (hfill Generator TriangleIndex fg dg ft dt T d hchecks)
  have hH : Hyperbolic.IsHyperbolicGroup
      (FreeGroup Generator ⧸ Subgroup.normalClosure (symmetrizedRelators T)) :=
    hgromov Generator (symmetrizedRelators T)
      ⟨3, norm_le_three_of_mem_symmetrizedRelators⟩ 3 hiso
  show Hyperbolic.IsHyperbolicGroup (FreeGroup Generator ⧸ Subgroup.normalClosure
    (TriangularHodgeLayer.relators T : Set (FreeGroup Generator)))
  exact Hyperbolic.IsHyperbolicGroup.of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (normalClosure_symmetrizedRelators T)) hH

end KazhdanHypGirthEightLinearIsoperimetric
end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightLinearIsoperimetric.isConjugateProduct_of_forall
#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightLinearIsoperimetric.isConjugateProduct_conj
#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightLinearIsoperimetric.exists_cyclicallyReduced_conj
#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightLinearIsoperimetric.linearIsoperimetric_of_localDataFilling
#audit_axioms GroupApproximation.GGT.KazhdanHypGirthEightLinearIsoperimetric.girthEightHyperbolicity_of_localDataFilling
