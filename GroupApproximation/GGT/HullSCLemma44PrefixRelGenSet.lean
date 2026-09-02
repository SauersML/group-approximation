import GroupApproximation.GGT.HullSCLemma44QuotientRelGenSet
import GroupApproximation.GGT.HullSCPublishedSmallCancellation

/-!
# Prefix generators for the quotient in Hull's Lemma 4.4

Hull's quotient conclusion does not require the relative base to be exactly
the image of the source base.  For an unbounded family of long relators, the
relative-presentation proof adjoins the values of relator prefixes.  A relator
then decomposes into uniformly short triangular relations between consecutive
prefixes.  This is the quotient-base construction used in DGO Theorem 7.19.

This file constructs that relative generating set without referring to a
presentation.  The values of all prefixes form an inversion-closed set because
the relator family is closed under formal inversion and cyclic rotation.  They
can thus be adjoined to the source base while retaining the same labelled
peripheral family.  Mapping the result through a surjection gives the concrete
quotient relative generating set needed by the later isoperimetric bridge.

The construction is useful even when relator lengths are not uniformly
bounded.  Its base contains the image of the old base, and its peripherals are
definitionally the subgroup images.  Hyperbolicity and properness of the new
relative metrics remain the geometric conclusions of the linear relative-area
argument.
-/

namespace GroupApproximation
namespace GGT

universe u v w

namespace RelGenSet

/-! ## Adjoining an inversion-closed base set -/

/-- Adjoin an inversion-closed set to the base of a relative generating set,
without changing its labelled peripheral family. -/
def adjoinSymmetricBase
    {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (P : Set G)
    (hP : ∀ x ∈ P, x⁻¹ ∈ P) : RelGenSet G Lambda where
  base := D.base ∪ P
  fam := D.fam
  symmetricGenerating := by
    have hcarrier :
        (D.base ∪ P) ∪ ⋃ lam : Lambda, (D.fam lam : Set G) =
          (D.base ∪ ⋃ lam : Lambda, (D.fam lam : Set G)) ∪ P :=
      Set.union_right_comm _ _ _
    rw [hcarrier]
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact Set.mem_union_left P
          (D.symmetricGenerating.inv_mem x hx)
      · exact Set.mem_union_right _ (hP x hx)
    · apply le_antisymm
      · exact le_top
      · have hmono : Subgroup.closure
            (D.base ∪ ⋃ lam : Lambda, (D.fam lam : Set G)) ≤
            Subgroup.closure
              ((D.base ∪ ⋃ lam : Lambda, (D.fam lam : Set G)) ∪ P) :=
          Subgroup.closure_mono Set.subset_union_left
        rw [D.symmetricGenerating.closure_eq] at hmono
        exact hmono

@[simp] theorem base_adjoinSymmetricBase
    {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (P : Set G)
    (hP : ∀ x ∈ P, x⁻¹ ∈ P) :
    (D.adjoinSymmetricBase P hP).base = D.base ∪ P := rfl

@[simp] theorem fam_adjoinSymmetricBase
    {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (P : Set G)
    (hP : ∀ x ∈ P, x⁻¹ ∈ P) (lam : Lambda) :
    (D.adjoinSymmetricBase P hP).fam lam = D.fam lam := rfl

/-- The old base is contained in the enlarged base. -/
theorem base_subset_adjoinSymmetricBase
    {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda) (P : Set G)
    (hP : ∀ x ∈ P, x⁻¹ ∈ P) :
    D.base ⊆ (D.adjoinSymmetricBase P hP).base :=
  Set.subset_union_left

end RelGenSet
end GGT

namespace HullSC

universe u v w

/-! ## Values of relator prefixes -/

/-- Group elements represented by prefixes of words in `W`. -/
def RelWord.prefixValues
    {G : Type u} [Group G] {Lambda : Type w}
    (W : Set (List (GGT.RelLetter G Lambda))) : Set G :=
  {g | ∃ word ∈ W, ∃ pre suffix, word = pre ++ suffix ∧
    g = GGT.RelLetter.listVal pre}

/-- A displayed prefix decomposition gives a prefix value. -/
theorem RelWord.listVal_mem_prefixValues
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {word pre suffix : List (GGT.RelLetter G Lambda)}
    (hword : word ∈ W) (hsplit : word = pre ++ suffix) :
    GGT.RelLetter.listVal pre ∈ RelWord.prefixValues W :=
  ⟨word, hword, pre, suffix, hsplit, rfl⟩

/-- The value of a complete relator is among its prefix values. -/
theorem RelWord.listVal_mem_prefixValues_of_mem
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {word : List (GGT.RelLetter G Lambda)} (hword : word ∈ W) :
    GGT.RelLetter.listVal word ∈ RelWord.prefixValues W := by
  exact RelWord.listVal_mem_prefixValues (pre := word) (suffix := [])
    hword (by simp)

/-- The empty prefix puts the identity in the prefix-value set whenever the
relator family is nonempty. -/
theorem RelWord.one_mem_prefixValues_of_nonempty
    {G : Type u} [Group G] {Lambda : Type w}
    {W : Set (List (GGT.RelLetter G Lambda))} (hW : W.Nonempty) :
    (1 : G) ∈ RelWord.prefixValues W := by
  obtain ⟨word, hword⟩ := hW
  refine ⟨word, hword, [], word, rfl, ?_⟩
  change (1 : G) = 1
  rfl

/-- Formal inversion and rotation make prefix values inversion closed. -/
theorem RelWord.inv_mem_prefixValues
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    {g : G} (hg : g ∈ RelWord.prefixValues W) :
    g⁻¹ ∈ RelWord.prefixValues W := by
  obtain ⟨word, hword, pre, suffix, hsplit, rfl⟩ := hg
  let inverseWord := RelWord.revInv word
  let rotated := inverseWord.rotate (RelWord.revInv suffix).length
  have hinverse : inverseWord ∈ W := hsc.inv_mem word hword
  have hrotated : rotated ∈ W :=
    hsc.rotate_mem inverseWord hinverse (RelWord.revInv suffix).length
  have hrotatedSplit :
      rotated = RelWord.revInv pre ++ RelWord.revInv suffix := by
    dsimp only [rotated, inverseWord]
    rw [hsplit, RelWord.revInv_append,
      List.rotate_append_length_eq]
  refine ⟨rotated, hrotated, RelWord.revInv pre,
    RelWord.revInv suffix, hrotatedSplit, ?_⟩
  exact (RelWord.listVal_revInv pre).symm

/-- The empty family has no prefix values. -/
@[simp] theorem RelWord.prefixValues_empty
    {G : Type u} [Group G] {Lambda : Type w} :
    RelWord.prefixValues
      (∅ : Set (List (GGT.RelLetter G Lambda))) = ∅ := by
  ext g
  constructor
  · rintro ⟨word, hword, pre, suffix, hsplit, hvalue⟩
    exact hword.elim
  · intro hg
    exact hg.elim

end HullSC

namespace GGT
namespace RelGenSet

open HullSC

/-! ## Source and quotient prefix relative generating sets -/

/-- Enlarge the source relative base by every relator-prefix value. -/
def adjoinRelatorPrefixes
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
    GGT.RelGenSet G Lambda :=
  D.adjoinSymmetricBase (RelWord.prefixValues W)
    (fun _ hg => RelWord.inv_mem_prefixValues hsc hg)

@[simp] theorem base_adjoinRelatorPrefixes
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) :
    (D.adjoinRelatorPrefixes W hsc).base =
      D.base ∪ RelWord.prefixValues W := rfl

@[simp] theorem fam_adjoinRelatorPrefixes
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho) (lam : Lambda) :
    (D.adjoinRelatorPrefixes W hsc).fam lam = D.fam lam := rfl

/-- Map the prefix-enlarged relative generating set to a quotient. -/
noncomputable def prefixQuotient
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) :
    GGT.RelGenSet Q Lambda :=
  (D.adjoinRelatorPrefixes W hsc).mapSurjective q hq

/-- Every old base letter maps into the quotient prefix base. -/
theorem map_mem_prefixQuotient_base
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    {x : G} (hx : x ∈ D.base) :
    q x ∈ (D.prefixQuotient W hsc q hq).base := by
  exact ⟨x, Set.mem_union_left _ hx, rfl⟩

/-- Quotient prefix peripherals are exactly the subgroup images. -/
@[simp] theorem fam_prefixQuotient
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q) (lam : Lambda) :
    (D.prefixQuotient W hsc q hq).fam lam = (D.fam lam).map q := rfl

/-- Every relator-prefix value maps into the quotient prefix base. -/
theorem map_prefixValue_mem_prefixQuotient_base
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    (W : Set (List (GGT.RelLetter G Lambda)))
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsSmallCancellation D W eps mu rho)
    (q : G →* Q) (hq : Function.Surjective q)
    {x : G} (hx : x ∈ RelWord.prefixValues W) :
    q x ∈ (D.prefixQuotient W hsc q hq).base := by
  exact ⟨x, Set.mem_union_right _ hx, rfl⟩

end RelGenSet
end GGT
end GroupApproximation
