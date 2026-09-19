import GroupApproximation.Sofic.ScalingFamilyPresentation
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Every member of the scaling family has exactly forty-one relators

`LiteralNonMFPresentation.relators_card` proves the count for the manuscript's
group `E`, which is the member `m = 2` of the family.  The count is uniform:
for every `m ≥ 2` the `m`-th presentation again has exactly forty-one
relators, so the whole family shares the printed shape of the displayed
presentation of `E`.

Only three of the forty-one relators move with `m` — the stable-letter
relations at the three lattice letters `v₁,v₂,v₃`.  The other thirty-eight are
literally the ones counted for `E`, so distinctness inside that block is
settled once and for all by kernel evaluation of the reduced-word normal
form.  The moving relators cannot be handled that way (`m` is a variable), so
they are separated from the fixed block by a homomorphic invariant: the
exponent sums of `v₁,v₂,v₃`.

The `m`-th stable relator at `vⱼ` is `t vⱼ t⁻¹ vⱼ^{-m}`, whose `vⱼ`-exponent
is `1 - m` and whose other two lattice exponents vanish.  Among the fixed
thirty-eight the only exponent triples with two vanishing coordinates are
`(0,0,0)` and `(0,0,2)`.  Since `m ≥ 2` forces `1 - m ≤ -1`, neither value is
attained.  The hypothesis `m ≥ 2` is used only here, and only through
`1 - m ∉ {0, 2}`.
-/

namespace GroupApproximation
namespace ScalingFamilyRelatorCount

open LiteralNonMFPresentation
open ScalingFamilyPresentation

/-! ## The lattice-exponent invariant -/

/-- The homomorphism recording the exponent sum of the lattice letter `vⱼ`. -/
def expHom (j : BaseGenerator) : FreeGroup Generator →* Multiplicative ℤ :=
  FreeGroup.lift fun g ↦
    Multiplicative.ofAdd (if g = Sum.inl j then (1 : ℤ) else 0)

/-- The exponent sum of the lattice letter `vⱼ` in a word. -/
def expAt (j : BaseGenerator) (w : FreeGroup Generator) : ℤ :=
  Multiplicative.toAdd (expHom j w)

@[simp] theorem expAt_one (j : BaseGenerator) : expAt j 1 = 0 := by
  simp [expAt]

@[simp] theorem expAt_mul (j : BaseGenerator) (a b : FreeGroup Generator) :
    expAt j (a * b) = expAt j a + expAt j b := by
  simp [expAt]

@[simp] theorem expAt_inv (j : BaseGenerator) (a : FreeGroup Generator) :
    expAt j a⁻¹ = -expAt j a := by
  simp [expAt]

@[simp] theorem expAt_pow (j : BaseGenerator) (a : FreeGroup Generator)
    (n : ℕ) : expAt j (a ^ n) = (n : ℤ) * expAt j a := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, expAt_mul, ih]
      push_cast
      ring

@[simp] theorem expAt_of (j : BaseGenerator) (g : Generator) :
    expAt j (FreeGroup.of g) = if g = Sum.inl j then 1 else 0 := by
  simp [expAt, expHom]

@[simp] theorem expAt_vertexLetter (j i : BaseGenerator) :
    expAt j (vertexLetter i) = if i = j then 1 else 0 := by
  simp [vertexLetter, Generator.base]

@[simp] theorem expAt_stableWord (j : BaseGenerator) : expAt j stableWord = 0 := by
  simp [stableWord, Generator.stable]

@[simp] theorem embedBaseWord_of (i : BaseGenerator) :
    embedBaseWord (FreeGroup.of i) = vertexLetter i := by
  simp [embedBaseWord]

/-- The three lattice exponents of a word. -/
def expTriple (w : FreeGroup Generator) : ℤ × ℤ × ℤ :=
  (expAt v1Index w, expAt v2Index w, expAt v3Index w)

/-! ## The thirty-eight relators that do not move -/

/-- The three stable-letter relators at `x`, `y`, `z`: the compressed word is
the letter itself, so these do not depend on `m`. -/
@[simp] theorem stableRelator_x (m : ℕ) :
    ScalingFamilyPresentation.stableRelator m xIndex =
      LiteralNonMFPresentation.stableRelator xIndex := rfl

@[simp] theorem stableRelator_y (m : ℕ) :
    ScalingFamilyPresentation.stableRelator m yIndex =
      LiteralNonMFPresentation.stableRelator yIndex := rfl

@[simp] theorem stableRelator_z (m : ℕ) :
    ScalingFamilyPresentation.stableRelator m zIndex =
      LiteralNonMFPresentation.stableRelator zIndex := rfl

/-- The three stable-letter relators that do not depend on `m`. -/
def fixedStableList : List (FreeGroup Generator) :=
  [LiteralNonMFPresentation.stableRelator xIndex,
    LiteralNonMFPresentation.stableRelator yIndex,
    LiteralNonMFPresentation.stableRelator zIndex]

/-- The thirty-eight relators shared by every member of the family. -/
def fixedBlock : List (FreeGroup Generator) :=
  fixedStableList ++
    (transportedBaseRelatorList ++ lampRelatorList ++ markedRelatorList)

@[simp] theorem fixedBlock_length : fixedBlock.length = 38 := rfl

theorem fixedBlock_nodup : fixedBlock.Nodup :=
  List.Nodup.of_map FreeGroup.toWord (by decide)

/-- The only lattice-exponent triples realized by the fixed relators.  The
evaluation is delegated to the kernel: the marked relators are thirty-four
letters long, which exceeds the elaborator's default recursion budget. -/
theorem expTriple_mem_of_mem_fixedBlock :
    ∀ w ∈ fixedBlock,
      expTriple w ∈ ([(0, 0, 0), (1, 0, -1), (-1, 1, 0), (0, -1, 1),
        (0, 2, -1), (-1, 1, 1), (1, -1, 1), (0, 0, 2)] :
          List (ℤ × ℤ × ℤ)) := by
  decide +kernel

/-! ## The three relators that move -/

/-- The three stable-letter relators at the lattice letters. -/
def latticeBlock (m : ℕ) : List (FreeGroup Generator) :=
  [ScalingFamilyPresentation.stableRelator m v1Index,
    ScalingFamilyPresentation.stableRelator m v2Index,
    ScalingFamilyPresentation.stableRelator m v3Index]

/-- At a lattice letter the compressed word is the `m`-th power of that
letter; this is the only place `m` enters a relator. -/
theorem compressedGeneratorWord_lattice (m : ℕ) (i : BaseGenerator)
    (hi : i = v1Index ∨ i = v2Index ∨ i = v3Index) :
    ScalingFamilyPresentation.compressedGeneratorWord m i =
      vertexLetter i ^ m := by
  rcases hi with rfl | rfl | rfl <;>
    simp [ScalingFamilyPresentation.compressedGeneratorWord,
      ScalingFamilyPresentation.compressedBaseWord, v1Index, v2Index, v3Index]

theorem expAt_stableRelator_lattice (m : ℕ) (j i : BaseGenerator)
    (hi : i = v1Index ∨ i = v2Index ∨ i = v3Index) :
    expAt j (ScalingFamilyPresentation.stableRelator m i) =
      (if i = j then 1 - (m : ℤ) else 0) := by
  rw [ScalingFamilyPresentation.stableRelator,
    compressedGeneratorWord_lattice m i hi]
  simp only [expAt_mul, expAt_inv, expAt_pow, expAt_stableWord,
    expAt_vertexLetter]
  split_ifs <;> ring

theorem expTriple_stableRelator_v1 (m : ℕ) :
    expTriple (ScalingFamilyPresentation.stableRelator m v1Index) =
      (1 - (m : ℤ), 0, 0) := by
  have h1 := expAt_stableRelator_lattice m v1Index v1Index (Or.inl rfl)
  have h2 := expAt_stableRelator_lattice m v2Index v1Index (Or.inl rfl)
  have h3 := expAt_stableRelator_lattice m v3Index v1Index (Or.inl rfl)
  rw [if_pos rfl] at h1
  rw [if_neg (by decide)] at h2
  rw [if_neg (by decide)] at h3
  simp only [expTriple, h1, h2, h3]

theorem expTriple_stableRelator_v2 (m : ℕ) :
    expTriple (ScalingFamilyPresentation.stableRelator m v2Index) =
      (0, 1 - (m : ℤ), 0) := by
  have h1 := expAt_stableRelator_lattice m v1Index v2Index
    (Or.inr (Or.inl rfl))
  have h2 := expAt_stableRelator_lattice m v2Index v2Index
    (Or.inr (Or.inl rfl))
  have h3 := expAt_stableRelator_lattice m v3Index v2Index
    (Or.inr (Or.inl rfl))
  rw [if_neg (by decide)] at h1
  rw [if_pos rfl] at h2
  rw [if_neg (by decide)] at h3
  simp only [expTriple, h1, h2, h3]

theorem expTriple_stableRelator_v3 (m : ℕ) :
    expTriple (ScalingFamilyPresentation.stableRelator m v3Index) =
      (0, 0, 1 - (m : ℤ)) := by
  have h1 := expAt_stableRelator_lattice m v1Index v3Index
    (Or.inr (Or.inr rfl))
  have h2 := expAt_stableRelator_lattice m v2Index v3Index
    (Or.inr (Or.inr rfl))
  have h3 := expAt_stableRelator_lattice m v3Index v3Index
    (Or.inr (Or.inr rfl))
  rw [if_neg (by decide)] at h1
  rw [if_neg (by decide)] at h2
  rw [if_pos rfl] at h3
  simp only [expTriple, h1, h2, h3]

theorem latticeBlock_nodup (m : ℕ) (hm : 2 ≤ m) : (latticeBlock m).Nodup := by
  have h2 : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have h12 : ScalingFamilyPresentation.stableRelator m v1Index ≠
      ScalingFamilyPresentation.stableRelator m v2Index := by
    intro h
    have hv := congrArg expTriple h
    rw [expTriple_stableRelator_v1, expTriple_stableRelator_v2,
      ] at hv
    simp only [Prod.mk.injEq] at hv
    omega
  have h13 : ScalingFamilyPresentation.stableRelator m v1Index ≠
      ScalingFamilyPresentation.stableRelator m v3Index := by
    intro h
    have hv := congrArg expTriple h
    rw [expTriple_stableRelator_v1, expTriple_stableRelator_v3,
      ] at hv
    simp only [Prod.mk.injEq] at hv
    omega
  have h23 : ScalingFamilyPresentation.stableRelator m v2Index ≠
      ScalingFamilyPresentation.stableRelator m v3Index := by
    intro h
    have hv := congrArg expTriple h
    rw [expTriple_stableRelator_v2, expTriple_stableRelator_v3,
      ] at hv
    simp only [Prod.mk.injEq] at hv
    omega
  simp only [latticeBlock]
  refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h12, h13⟩
  · simp only [List.mem_singleton]
    exact h23

theorem latticeBlock_disjoint_fixedBlock (m : ℕ) (hm : 2 ≤ m) :
    List.Disjoint (latticeBlock m) fixedBlock := by
  have h2 : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  intro r hr hfix
  have hval := expTriple_mem_of_mem_fixedBlock r hfix
  simp only [latticeBlock, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [expTriple_stableRelator_v1] at hval
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      at hval
    omega
  · rw [expTriple_stableRelator_v2] at hval
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      at hval
    omega
  · rw [expTriple_stableRelator_v3] at hval
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
      at hval
    omega

/-! ## The count -/

/-- All forty-one relators of the `m`-th presentation. -/
def relatorList (m : ℕ) : List (FreeGroup Generator) :=
  latticeBlock m ++ fixedBlock

@[simp] theorem relatorList_length (m : ℕ) : (relatorList m).length = 41 := rfl

theorem relatorList_nodup (m : ℕ) (hm : 2 ≤ m) : (relatorList m).Nodup :=
  List.Nodup.append (latticeBlock_nodup m hm) fixedBlock_nodup
    (latticeBlock_disjoint_fixedBlock m hm)

/-- The six stable-letter relators of the `m`-th presentation, in the printed
order `v₁,v₂,v₃,x,y,z`. -/
def stableRelatorList (m : ℕ) : List (FreeGroup Generator) :=
  baseGeneratorList.map (ScalingFamilyPresentation.stableRelator m)

/-- Splitting that list into the three that move and the three that do not. -/
@[simp] theorem stableRelatorList_eq (m : ℕ) :
    stableRelatorList m = latticeBlock m ++ fixedStableList := rfl

theorem mem_stableRelators_iff (m : ℕ) (r : FreeGroup Generator) :
    r ∈ ScalingFamilyPresentation.stableRelators m ↔
      r ∈ stableRelatorList m := by
  simp only [ScalingFamilyPresentation.stableRelators, stableRelatorList,
    Finset.mem_image, Finset.mem_univ, true_and, List.mem_map,
    mem_baseGeneratorList]

theorem mem_relators_iff_mem_list (m : ℕ) (r : FreeGroup Generator) :
    r ∈ ScalingFamilyPresentation.relators m ↔ r ∈ relatorList m := by
  simp only [ScalingFamilyPresentation.relators, Finset.mem_union,
    mem_transportedBaseRelators_iff, mem_stableRelators_iff,
    mem_lampRelators_iff, mem_markedRelators_iff, relatorList, fixedBlock,
    stableRelatorList_eq, List.mem_append]
  tauto

theorem relators_eq_toFinset (m : ℕ) :
    ScalingFamilyPresentation.relators m = (relatorList m).toFinset := by
  ext r
  rw [List.mem_toFinset]
  exact mem_relators_iff_mem_list m r

/-- **Every member of the scaling family with `m ≥ 2` has exactly forty-one
relators**, on the same eight generators.  At `m = 2` this is the
manuscript's group `E`. -/
theorem relators_card (m : ℕ) (hm : 2 ≤ m) :
    (ScalingFamilyPresentation.relators m).card = 41 := by
  rw [relators_eq_toFinset,
    List.toFinset_card_of_nodup (relatorList_nodup m hm), relatorList_length]

/-- The printed shape of the whole family: eight generators, forty-one
relators, for every `m ≥ 2`. -/
theorem manuscriptScalingFamilyPresentationCounts :
    ∀ m : ℕ, 2 ≤ m →
      Fintype.card Generator = 8 ∧
        (ScalingFamilyPresentation.relators m).card = 41 :=
  fun m hm ↦ ⟨generator_card, relators_card m hm⟩

end ScalingFamilyRelatorCount
end GroupApproximation
