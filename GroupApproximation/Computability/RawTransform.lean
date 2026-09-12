import GroupApproximation.Computability.RawWord
import GroupApproximation.Computability.RabinVariantCode
import GroupApproximation.Computability.CoprodCode

/-!
# The transformation as raw list surgery

`AdianRabinVariantTransform.transform` is correct but `noncomputable`, and not
by accident: it builds its output with `PresentationCodeList.codeOfList`, which
encodes free-group elements, and `FreeGroup` over the *dependent* alphabet
`Fin (genCount c)` has no `Primcodable` instance --- so `Computable transform`
cannot even be approached in that form.

This file rebuilds the same code by pure list surgery on `List (ℕ × Bool)`.
Nothing here mentions `FreeGroup` in a *definition*; the free group appears only
in the theorems saying what the raw words read as.

The generator numbering is the one `RabinVariantCode.genEquiv` fixes, and this
file simply writes it out: a left-factor generator keeps its number, a
right-factor generator is shifted by the left alphabet's size, the killing
letters `tⱼ` follow at `srcCount + j`, and `s, u, b, c, k` follow those.
`idxT` and `idxE` name those positions, and the four `genEquiv_val_*` lemmas
are the whole content of the identification --- everything else is
concatenation.
-/

namespace GroupApproximation
namespace RawTransform

open PresentationCodes PresentationCodeList RawWord CoprodCode RabinVariantCode
open RabinVariantPresentation PresentedGroupRelabel

/-! ## The numbering, written out -/

/-- The alphabet of the construction's source: the free product's generators. -/
abbrev srcCount (c d : PresentationCode) : ℕ := genCount c + genCount d

/-- The output alphabet, stored offset by one as a code's first component is. -/
abbrev outIdx (c d : PresentationCode) : ℕ := srcCount c d + (srcCount c d + 5)

/-- The number of the `j`-th killing letter. -/
def idxT (c d : PresentationCode) (j : ℕ) : ℕ := srcCount c d + j

/-- The number of the `k`-th adjoined letter: `s, u, b, c, k` at `0, …, 4`. -/
def idxE (c d : PresentationCode) (k : ℕ) : ℕ :=
  srcCount c d + (srcCount c d + 1) + k

/-! ## What the numbering does

Four value computations.  `genEquiv` is a composite of `finSumFinEquiv`s, each
of which either preserves the underlying number or shifts it by the size of the
left summand, so every case is arithmetic. -/

variable {m : ℕ}

@[simp] theorem genEquiv_val_inl (i : Fin m) :
    ((genEquiv m (Sum.inl i) : Fin (m + (m + 5) + 1)) : ℕ) = (i : ℕ) := by
  simp [genEquiv]

@[simp] theorem genEquiv_val_t (j : Fin (m + 1)) :
    ((genEquiv m (Sum.inr (Extra.t j)) : Fin (m + (m + 5) + 1)) : ℕ) = m + (j : ℕ) := by
  simp [genEquiv, extraEquiv]

@[simp] theorem genEquiv_val_s :
    ((genEquiv m (Sum.inr Extra.s) : Fin (m + (m + 5) + 1)) : ℕ) = m + (m + 1) + 0 := by
  simp [genEquiv, extraEquiv]

@[simp] theorem genEquiv_val_u :
    ((genEquiv m (Sum.inr Extra.u) : Fin (m + (m + 5) + 1)) : ℕ) = m + (m + 1) + 1 := by
  simp [genEquiv, extraEquiv]
  omega

@[simp] theorem genEquiv_val_b :
    ((genEquiv m (Sum.inr Extra.b) : Fin (m + (m + 5) + 1)) : ℕ) = m + (m + 1) + 2 := by
  simp [genEquiv, extraEquiv]
  omega

@[simp] theorem genEquiv_val_c :
    ((genEquiv m (Sum.inr Extra.c) : Fin (m + (m + 5) + 1)) : ℕ) = m + (m + 1) + 3 := by
  simp [genEquiv, extraEquiv]
  omega

@[simp] theorem genEquiv_val_k :
    ((genEquiv m (Sum.inr Extra.k) : Fin (m + (m + 5) + 1)) : ℕ) = m + (m + 1) + 4 := by
  simp [genEquiv, extraEquiv]
  omega

/-! ## The raw words -/

variable (c d : PresentationCode)

/-- The left factor's relators: their letters already have the right numbers,
so only the reduction into range is needed. -/
def leftWords : List (List (ℕ × Bool)) := c.2.map (normWord c)

/-- The right factor's relators, shifted past the left alphabet. -/
def rightWords : List (List (ℕ × Bool)) :=
  d.2.map fun u => u.map fun p => (genCount c + p.1 % genCount d, p.2)

/-- `(sⱼ)⁻¹` as a raw word: `s⁻¹` at `j = 0`, and `xᵢ⁻¹ s⁻¹` at `j = i + 1`. -/
def invSWord (j : ℕ) : List (ℕ × Bool) :=
  match j with
  | 0 => [(idxE c d 0, false)]
  | i + 1 => [(i, false), (idxE c d 0, false)]

/-- The `j`-th killing relator `u tⱼ u⁻¹ (tⱼ sⱼ)⁻¹`, as a raw word. -/
def killWord (j : ℕ) : List (ℕ × Bool) :=
  (idxE c d 1, true) :: (idxT c d j, true) :: (idxE c d 1, false) ::
    (invSWord c d j ++ [(idxT c d j, false)])

/-- The witness `⁅w, s⁆`, as a raw word. -/
def zWord (w : List (ℕ × Bool)) : List (ℕ × Bool) :=
  normWord c w ++ (idxE c d 0, true) ::
    (invWord (normWord c w) ++ [(idxE c d 0, false)])

/-- The three cascade relators, as raw words. -/
def cascadeWords (w : List (ℕ × Bool)) : List (List (ℕ × Bool)) :=
  [[(idxE c d 2, true), (idxE c d 1, true), (idxE c d 2, false),
      (idxE c d 1, false), (idxE c d 1, false)],
   [(idxE c d 3, true), (idxE c d 2, true), (idxE c d 3, false),
      (idxE c d 2, false), (idxE c d 2, false)],
   (idxE c d 4, true) :: (zWord c d w ++ [(idxE c d 4, false), (idxE c d 3, false)])]

/-- **All the relators of the output, as raw words.** -/
def rawWords (w : List (ℕ × Bool)) : List (List (ℕ × Bool)) :=
  leftWords c ++ rightWords c d ++
    (List.range (srcCount c d + 1)).map (killWord c d) ++ cascadeWords c d w

/-- **The transformation, as list surgery.**  No `FreeGroup` appears in this
definition, which is what makes it a candidate for `Computable`. -/
def rawTransform (w : List (ℕ × Bool)) : PresentationCode :=
  (outIdx c d, rawWords c d w)

@[simp] theorem genCount_rawTransform (w : List (ℕ × Bool)) :
    genCount (rawTransform c d w) = srcCount c d + (srcCount c d + 5) + 1 := rfl

/-- The output code's relator list, read off the construction.  `@[simp]` like
`genCount_rawTransform` above: definitional, and worth stating only because
`simp` and `rw` need the surgery form spelled out.  No loop --- the right-hand
side has no `relatorListOf` of a `rawTransform`. -/
@[simp] theorem relatorListOf_rawTransform (w : List (ℕ × Bool)) :
    relatorListOf (rawTransform c d w)
      = (rawWords c d w).map (wordOf (rawTransform c d w)) := rfl

/-! ## What each raw letter reads as

Every index the raw words use is below the output alphabet's size, so the
code's reduction leaves it alone, and the value computations above say which
generator of `Gen (srcCount c d)` it names. -/

variable (w : List (ℕ × Bool))

theorem letterOf_out_lt {i : ℕ} (h : i < genCount (rawTransform c d w)) :
    ((letterOf (rawTransform c d w) i : Fin (genCount (rawTransform c d w))) : ℕ) = i :=
  Nat.mod_eq_of_lt h

theorem letterOf_idxT {j : ℕ} (hj : j < srcCount c d + 1) :
    letterOf (rawTransform c d w) (idxT c d j)
      = genEquiv (srcCount c d) (Sum.inr (Extra.t ⟨j, hj⟩)) := by
  refine Fin.ext ?_
  have hb : idxT c d j < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform, idxT]
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_t]
  rfl

theorem letterOf_idxE_s :
    letterOf (rawTransform c d w) (idxE c d 0)
      = genEquiv (srcCount c d) (Sum.inr Extra.s) := by
  refine Fin.ext ?_
  have hb : idxE c d 0 < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform, idxE]
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_s]
  rfl

theorem letterOf_idxE_u :
    letterOf (rawTransform c d w) (idxE c d 1)
      = genEquiv (srcCount c d) (Sum.inr Extra.u) := by
  refine Fin.ext ?_
  have hb : idxE c d 1 < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform, idxE]
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_u]
  simp only [idxE]

theorem letterOf_idxE_b :
    letterOf (rawTransform c d w) (idxE c d 2)
      = genEquiv (srcCount c d) (Sum.inr Extra.b) := by
  refine Fin.ext ?_
  have hb : idxE c d 2 < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform, idxE]
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_b]
  simp only [idxE]

theorem letterOf_idxE_c :
    letterOf (rawTransform c d w) (idxE c d 3)
      = genEquiv (srcCount c d) (Sum.inr Extra.c) := by
  refine Fin.ext ?_
  have hb : idxE c d 3 < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform, idxE]
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_c]
  simp only [idxE]

theorem letterOf_idxE_k :
    letterOf (rawTransform c d w) (idxE c d 4)
      = genEquiv (srcCount c d) (Sum.inr Extra.k) := by
  refine Fin.ext ?_
  have hb : idxE c d 4 < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform, idxE]
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_k]
  simp only [idxE]

theorem letterOf_src {i : ℕ} :
    letterOf (rawTransform c d w) (i % genCount c)
      = genEquiv (srcCount c d)
          (Sum.inl (finSumFinEquiv (m := genCount c) (n := genCount d)
            (Sum.inl (letterOf c i)))) := by
  refine Fin.ext ?_
  have hlt : i % genCount c < genCount c := Nat.mod_lt _ (genCount_pos c)
  have hb : i % genCount c < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform]
    have hle : genCount c ≤ srcCount c d := Nat.le_add_right _ _
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_inl]
  simp
  rfl

theorem letterOf_right {i : ℕ} :
    letterOf (rawTransform c d w) (genCount c + i % genCount d)
      = genEquiv (srcCount c d)
          (Sum.inl (finSumFinEquiv (m := genCount c) (n := genCount d)
            (Sum.inr (letterOf d i)))) := by
  refine Fin.ext ?_
  have hlt : i % genCount d < genCount d := Nat.mod_lt _ (genCount_pos d)
  have hb : genCount c + i % genCount d < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform]
    have hs : srcCount c d = genCount c + genCount d := rfl
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_inl]
  simp
  rfl

theorem letterOf_gen {i : ℕ} (hi : i < srcCount c d) :
    letterOf (rawTransform c d w) i = genEquiv (srcCount c d) (Sum.inl ⟨i, hi⟩) := by
  refine Fin.ext ?_
  have hb : i < genCount (rawTransform c d w) := by
    simp only [genCount_rawTransform]
    omega
  rw [letterOf_out_lt c d w hb, genEquiv_val_inl]

/-! ## What each family of raw words reads as -/

/-- A left-factor relator. -/
theorem wordOf_leftWord (u : List (ℕ × Bool)) :
    wordOf (rawTransform c d w) (normWord c u)
      = relabel (genEquiv (srcCount c d))
          (emb (relabel (finSumFinEquiv (m := genCount c) (n := genCount d))
            (FreeGroup.map Sum.inl (wordOf c u)))) := by
  rw [wordOf_def, wordOf_def]
  simp only [emb, FreeGroup.map.mk, normWord, List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  exact Prod.ext (letterOf_src c d w) rfl

/-- A right-factor relator. -/
theorem wordOf_rightWord (u : List (ℕ × Bool)) :
    wordOf (rawTransform c d w) (u.map fun p => (genCount c + p.1 % genCount d, p.2))
      = relabel (genEquiv (srcCount c d))
          (emb (relabel (finSumFinEquiv (m := genCount c) (n := genCount d))
            (FreeGroup.map Sum.inr (wordOf d u)))) := by
  rw [wordOf_def, wordOf_def]
  simp only [emb, FreeGroup.map.mk, List.map_map, Function.comp_def]
  congr 1
  refine List.map_congr_left fun p _ => ?_
  exact Prod.ext (letterOf_right c d w) rfl

/-- A killing relator. -/
theorem wordOf_killWord {j : ℕ} (hj : j < srcCount c d + 1) :
    wordOf (rawTransform c d w) (killWord c d j)
      = relabel (genEquiv (srcCount c d))
          (U * T ⟨j, hj⟩ * U⁻¹ * (T ⟨j, hj⟩ * sWord ⟨j, hj⟩)⁻¹) := by
  rw [killWord]
  simp only [wordOf_cons_pos, wordOf_cons_neg, wordOf_append, wordOf_nil, mul_one,
    letterOf_idxE_u c d w, letterOf_idxT c d w hj]
  simp only [U, T, map_mul, map_inv, FreeGroup.map.of]
  match j, hj with
  | 0, hj =>
      rw [invSWord]
      simp only [wordOf_cons_neg, wordOf_nil, mul_one, letterOf_idxE_s c d w]
      simp only [show (⟨0, hj⟩ : Fin (srcCount c d + 1)) = 0 from rfl, sWord_zero, S,
        FreeGroup.map.of]
      group
      rfl
  | i + 1, hj =>
      have hi : i < srcCount c d := Nat.lt_of_succ_lt_succ hj
      rw [invSWord]
      simp only [wordOf_cons_neg, wordOf_nil, mul_one,
        letterOf_gen c d w hi, letterOf_idxE_s c d w]
      simp only [show (⟨i + 1, hj⟩ : Fin (srcCount c d + 1)) = (⟨i, hi⟩ : Fin (srcCount c d)).succ
          from rfl, sWord_succ, S, X, map_mul, FreeGroup.map.of]
      group
      rfl

/-- The first cascade relator. -/
theorem wordOf_cascade_b :
    wordOf (rawTransform c d w)
        [(idxE c d 2, true), (idxE c d 1, true), (idxE c d 2, false),
          (idxE c d 1, false), (idxE c d 1, false)]
      = relabel (genEquiv (srcCount c d)) (B * U * B⁻¹ * (U ^ (2 : ℕ))⁻¹) := by
  simp only [wordOf_cons_pos, wordOf_cons_neg, wordOf_nil, mul_one,
    letterOf_idxE_u c d w, letterOf_idxE_b c d w]
  simp only [B, U, map_mul, map_inv, map_pow, FreeGroup.map.of]
  group
  rfl

/-- The second cascade relator. -/
theorem wordOf_cascade_c :
    wordOf (rawTransform c d w)
        [(idxE c d 3, true), (idxE c d 2, true), (idxE c d 3, false),
          (idxE c d 2, false), (idxE c d 2, false)]
      = relabel (genEquiv (srcCount c d)) (C * B * C⁻¹ * (B ^ (2 : ℕ))⁻¹) := by
  simp only [wordOf_cons_pos, wordOf_cons_neg, wordOf_nil, mul_one,
    letterOf_idxE_b c d w, letterOf_idxE_c c d w]
  simp only [C, B, map_mul, map_inv, map_pow, FreeGroup.map.of]
  group
  rfl

/-- The witness word. -/
theorem wordOf_zWord :
    wordOf (rawTransform c d w) (zWord c d w)
      = relabel (genEquiv (srcCount c d))
          (Z (wordOf (coprodCode c d) (normWord c w))) := by
  rw [zWord]
  simp only [wordOf_append, wordOf_cons_pos, wordOf_cons_neg, wordOf_nil, mul_one,
    wordOf_invWord, wordOf_leftWord, letterOf_idxE_s c d w, Z, S,
    CoprodCode.wordOf_coprodCode, map_mul, map_inv, FreeGroup.map.of]
  group
  rfl

/-- The third cascade relator. -/
theorem wordOf_cascade_k :
    wordOf (rawTransform c d w)
        ((idxE c d 4, true) :: (zWord c d w ++ [(idxE c d 4, false), (idxE c d 3, false)]))
      = relabel (genEquiv (srcCount c d))
          (K * Z (wordOf (coprodCode c d) (normWord c w)) * K⁻¹ * C⁻¹) := by
  simp only [wordOf_cons_pos, wordOf_append, wordOf_cons_neg, wordOf_nil, mul_one,
    wordOf_zWord, letterOf_idxE_k c d w, letterOf_idxE_c c d w, K, C,
    map_mul, map_inv, FreeGroup.map.of]
  group
  rfl

/-! ## The raw code and the built code name the same relators

Four segments of raw words, three pieces of `relators`: the left and right
factor relators together are the source relators of the free product, and the
killing and cascade families match one for one. -/

theorem setOf_mem_map_append {α β : Type} (f : α → β) (A B : List α) :
    {x | x ∈ (A ++ B).map f} = {x | x ∈ A.map f} ∪ {x | x ∈ B.map f} := by
  ext x
  simp only [Set.mem_setOf_eq, List.map_append, List.mem_append, Set.mem_union]

theorem setOf_mem_leftWords :
    {x | x ∈ (leftWords c).map (wordOf (rawTransform c d w))}
      = (fun r => relabel (genEquiv (srcCount c d))
          (emb (relabel (finSumFinEquiv (m := genCount c) (n := genCount d))
            (FreeGroup.map Sum.inl r)))) '' {x | x ∈ relatorListOf c} := by
  ext x
  simp only [leftWords, List.map_map, Function.comp_def, Set.mem_setOf_eq, List.mem_map,
    relatorListOf, wordOf_leftWord]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨wordOf c u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨r, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem setOf_mem_rightWords :
    {x | x ∈ (rightWords c d).map (wordOf (rawTransform c d w))}
      = (fun r => relabel (genEquiv (srcCount c d))
          (emb (relabel (finSumFinEquiv (m := genCount c) (n := genCount d))
            (FreeGroup.map Sum.inr r)))) '' {x | x ∈ relatorListOf d} := by
  ext x
  simp only [rightWords, List.map_map, Function.comp_def, Set.mem_setOf_eq, List.mem_map,
    relatorListOf, wordOf_rightWord]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨wordOf d u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨r, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, rfl⟩

theorem setOf_mem_killWords :
    {x | x ∈ ((List.range (srcCount c d + 1)).map (killWord c d)).map
        (wordOf (rawTransform c d w))}
      = relabel (genEquiv (srcCount c d)) ''
          Set.range (fun i : Fin (srcCount c d + 1) =>
            U * T i * U⁻¹ * (T i * sWord i)⁻¹) := by
  ext x
  simp only [List.map_map, Function.comp_def, Set.mem_setOf_eq, List.mem_map,
    List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨_, ⟨⟨j, hj⟩, rfl⟩, (wordOf_killWord c d w hj).symm⟩
  · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
    exact ⟨(i : ℕ), i.isLt, wordOf_killWord c d w i.isLt⟩

theorem setOf_mem_cascadeWords :
    {x | x ∈ (cascadeWords c d w).map (wordOf (rawTransform c d w))}
      = relabel (genEquiv (srcCount c d)) ''
          {B * U * B⁻¹ * (U ^ (2 : ℕ))⁻¹, C * B * C⁻¹ * (B ^ (2 : ℕ))⁻¹,
            K * Z (wordOf (coprodCode c d) (normWord c w)) * K⁻¹ * C⁻¹} := by
  ext x
  simp only [cascadeWords, List.map_cons, List.map_nil, Set.mem_setOf_eq, List.mem_cons,
    List.not_mem_nil, or_false, wordOf_cascade_b, wordOf_cascade_c, wordOf_cascade_k]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨_, Or.inl rfl, rfl⟩
    · exact ⟨_, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨_, Or.inr (Or.inr rfl), rfl⟩
  · rintro ⟨-, (rfl | rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- **The raw code names the same relators as the built code.**  Both are
unions of the same four images, so the two codes present the same group. -/
theorem relSet_rawTransform :
    {x | x ∈ relatorListOf (rawTransform c d w)}
      = {x | x ∈ relatorListOf (variantCode (coprodCode c d) (normWord c w))} := by
  rw [relatorListOf_rawTransform, rawWords, setOf_mem_map_append, setOf_mem_map_append,
    setOf_mem_map_append, setOf_mem_leftWords, setOf_mem_rightWords, setOf_mem_killWords,
    setOf_mem_cascadeWords, relSet_variantCode, relSet_coprodCode]
  simp only [relators, relabelRels, Set.image_union, Set.image_image, emb]
  rfl

/-- **The raw code presents the group the construction builds.** -/
noncomputable def rawCarrierEquiv :
    Carrier (rawTransform c d w)
      ≃* Carrier (variantCode (coprodCode c d) (normWord c w)) :=
  ((carrierEquivList (rawTransform c d w)).trans
      (presCongrSet (relSet_rawTransform c d w))).trans
    (carrierEquivList (variantCode (coprodCode c d) (normWord c w))).symm

end RawTransform
end GroupApproximation
