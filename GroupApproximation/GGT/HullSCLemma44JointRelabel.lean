import GroupApproximation.GGT.HullSCLemma44FamilyAssembly
import GroupApproximation.GGT.HullSCRelatorFamily

/-!
# Hull's relator read in the joint peripheral family

Hull's relator is a word over the selected auxiliary alphabet.  The family form
of Lemma 4.4 also needs it as a word over the joint family, whose peripherals
are the original ones on the `inl` side and the selected ones on the `inr`
side.  This file performs that reading and proves that every clause of the
Lemma 4.4 input survives it.

The reading is the index relabelling `Sum.inr`, so no base letter becomes a
peripheral letter and the depth clause has nothing to prove on the `inl` side.
That is legitimate exactly when every base letter of the relator is already a
base letter of the joint family, and Hull's construction supplies it: by
`exists_hullRelatorWord₂OfBaseLetterPublished_exact` every base letter of the
relator is the single adjoined element `t⁻¹`, so `baseLetters_symmetrized_mem`
reduces the side condition to `t⁻¹ ∈ joint.base`.

Two structural facts make the metric clauses transport.  The letter map back,
`unrelabelJoint`, is total: an `inl`-component letter is read as a base letter,
because every original peripheral element is one of Hull's letters.  And the
two relative alphabets are equal as sets, so the word metrics agree and the
piece and quasi-geodesic clauses are the same statements on both sides.

What does **not** transport is the reading over the original family alone: the
selected peripheral letters are not letters there, so re-spelling them changes
lengths and the small-cancellation parameters.  That half stays a named input.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

/-! ## Base letters of the symmetrized relator -/

/-- Every base letter of the symmetrized closure of a relator lies in any
inverse-closed set containing the relator's single base letter.  Hull's §6
relator has exactly one base letter, `t⁻¹`, so this is the whole content of the
side condition used below. -/
theorem baseLetters_symmetrized_mem {G : Type u} [Group G] {Lambda : Type w}
    (R : List (GGT.RelLetter G Lambda)) (t : G) (B : Set G)
    (hbase : ∀ x : G, GGT.RelLetter.base x ∈ R → x = t⁻¹)
    (ht : t⁻¹ ∈ B) (hinv : ∀ x ∈ B, x⁻¹ ∈ B) :
    ∀ v ∈ RelWord.symmetrized R, ∀ x : G,
      GGT.RelLetter.base x ∈ v → x ∈ B := by
  intro v hv x hx
  rcases RelWord.Sym.letters (RelWord.mem_symmetrized.mp hv)
      (GGT.RelLetter.base x) hx with hmem | hmem
  · rw [hbase x hmem]
    exact ht
  · have hmem' : GGT.RelLetter.base x⁻¹ ∈ R := hmem
    have hxt : x⁻¹ = t⁻¹ := hbase _ hmem'
    have hxeq : x = t := by
      rw [← inv_inv x, hxt, inv_inv]
    have hinvB := hinv t⁻¹ ht
    rw [inv_inv] at hinvB
    rw [hxeq]
    exact hinvB

/-! ## The letter map back from the joint index -/

/-- Reading a joint letter in the selected family.  An `inl`-component letter
becomes a base letter, which is legitimate because every original peripheral
element is one of Hull's base letters. -/
def unrelabelJoint {G : Type u} {Lambda : Type w} {k : ℕ} :
    GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)) →
      GGT.RelLetter G (AuxiliaryPeripheralIndex k)
  | GGT.RelLetter.base x => GGT.RelLetter.base x
  | GGT.RelLetter.comp (Sum.inl _) h => GGT.RelLetter.base h
  | GGT.RelLetter.comp (Sum.inr i) h => GGT.RelLetter.comp i h

@[simp] theorem unrelabelJoint_val {G : Type u} {Lambda : Type w} {k : ℕ}
    (a : GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k))) :
    (unrelabelJoint a).val = a.val := by
  cases a with
  | base x => rfl
  | comp s h => cases s <;> rfl

@[simp] theorem unrelabelJoint_relabelLetter {G : Type u} {Lambda : Type w}
    {k : ℕ} (a : GGT.RelLetter G (AuxiliaryPeripheralIndex k)) :
    unrelabelJoint
        (relabelLetter
          (Sum.inr : AuxiliaryPeripheralIndex k →
            Sum Lambda (AuxiliaryPeripheralIndex k)) a) = a := by
  cases a <;> rfl

theorem map_unrelabelJoint_map_relabelLetter {G : Type u} {Lambda : Type w}
    {k : ℕ} (v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))) :
    (v.map
        (relabelLetter
          (Sum.inr : AuxiliaryPeripheralIndex k →
            Sum Lambda (AuxiliaryPeripheralIndex k)))).map unrelabelJoint =
      v := by
  induction v with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, unrelabelJoint_relabelLetter, ih]

theorem map_val_unrelabelJoint {G : Type u} {Lambda : Type w} {k : ℕ}
    (word : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))) :
    (word.map unrelabelJoint).map GGT.RelLetter.val =
      word.map GGT.RelLetter.val := by
  induction word with
  | nil => rfl
  | cons a t ih =>
      simp only [List.map_cons, unrelabelJoint_val, ih]

theorem listVal_map_unrelabelJoint {G : Type u} [Group G] {Lambda : Type w}
    {k : ℕ}
    (word : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))) :
    GGT.RelLetter.listVal (word.map unrelabelJoint) =
      GGT.RelLetter.listVal word := by
  show ((word.map unrelabelJoint).map GGT.RelLetter.val).prod =
    (word.map GGT.RelLetter.val).prod
  rw [map_val_unrelabelJoint]

/-- Reading back is exact on the `inr` component labels and kills the
others. -/
theorem unrelabelJoint_isCompOf {G : Type u} {Lambda : Type w} {k : ℕ}
    (i : AuxiliaryPeripheralIndex k)
    (a : GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k))) :
    (unrelabelJoint a).IsCompOf i ↔
      a.IsCompOf (Sum.inr i : Sum Lambda (AuxiliaryPeripheralIndex k)) := by
  cases a with
  | base x => exact Iff.rfl
  | comp s h =>
      cases s with
      | inl lam =>
          constructor
          · intro hfalse
            exact (hfalse : False).elim
          · intro hcontra
            have hEq :
                (Sum.inl lam : Sum Lambda (AuxiliaryPeripheralIndex k)) =
                  Sum.inr i := hcontra
            exact absurd hEq Sum.inl_ne_inr
      | inr j =>
          constructor
          · intro hj
            have hji : j = i := hj
            show (Sum.inr j : Sum Lambda (AuxiliaryPeripheralIndex k)) =
              Sum.inr i
            rw [hji]
          · intro hj
            have hji :
                (Sum.inr j : Sum Lambda (AuxiliaryPeripheralIndex k)) =
                  Sum.inr i := hj
            show j = i
            exact Sum.inr.inj hji

/-! ## Commutation with the two closure operations

These mirror `revInv_map_embedNLetter` and `listVal_take_map_focusLetterOfFull`
in `HullSCAuxiliaryRelatorPublished`, which perform the same transport for the
focused Bool-indexed pair. -/

section Closure

variable {G : Type u} [Group G] {Lambda : Type v} {Lambda' : Type w}

theorem inv_relabelLetter (f : Lambda → Lambda')
    (a : GGT.RelLetter G Lambda) :
    RelWord.inv (relabelLetter f a) = relabelLetter f (RelWord.inv a) := by
  cases a <;> rfl

theorem revInv_map_relabelLetter (f : Lambda → Lambda')
    (v : List (GGT.RelLetter G Lambda)) :
    RelWord.revInv (v.map (relabelLetter f)) =
      (RelWord.revInv v).map (relabelLetter f) := by
  simp only [RelWord.revInv, List.map_reverse, List.map_map]
  apply congrArg List.reverse
  exact List.map_congr_left (fun a _ => inv_relabelLetter f a)

omit [Group G] in
theorem take_map_relabelLetter (f : Lambda → Lambda')
    (v : List (GGT.RelLetter G Lambda)) (n : ℕ) :
    (v.map (relabelLetter f)).take n = (v.take n).map (relabelLetter f) := by
  induction v generalizing n with
  | nil => cases n <;> rfl
  | cons a t ih =>
      cases n with
      | zero => rfl
      | succ n =>
          change relabelLetter f a :: (t.map (relabelLetter f)).take n =
            relabelLetter f a :: (t.take n).map (relabelLetter f)
          exact congrArg (relabelLetter f a :: ·) (ih n)

end Closure

/-! ## The joint reading of a relator family -/

section Transport

variable {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
  {k : ℕ} {S : Fin k → Subgroup G} {Lambda : Type w}

/-- Hull's relator family read in the joint index. -/
def jointRelabelWords
    (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))) :
    Set (List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))) :=
  relabelWords Sum.inr W

omit [Group G] in
theorem mem_jointRelabelWords_iff
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {v : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))} :
    v ∈ jointRelabelWords (Lambda := Lambda) W ↔
      ∃ v₀ ∈ W,
        v₀.map
            (relabelLetter
              (Sum.inr : AuxiliaryPeripheralIndex k →
                Sum Lambda (AuxiliaryPeripheralIndex k))) = v := Iff.rfl

omit [Group G] in
theorem mem_jointRelabelWords_source
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {v : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))}
    (hv : v ∈ jointRelabelWords (Lambda := Lambda) W) :
    v.map unrelabelJoint ∈ W := by
  obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
  rw [← hmap, map_unrelabelJoint_map_relabelLetter]
  exact hv₀

omit [Group G] in
theorem map_relabelLetter_map_unrelabelJoint
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {v : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))}
    (hv : v ∈ jointRelabelWords (Lambda := Lambda) W) :
    (v.map unrelabelJoint).map
        (relabelLetter
          (Sum.inr : AuxiliaryPeripheralIndex k →
            Sum Lambda (AuxiliaryPeripheralIndex k))) = v := by
  obtain ⟨v₀, _hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
  rw [← hmap, map_unrelabelJoint_map_relabelLetter]

omit [Group G] in
/-- The reading is injective on the relabelled family. -/
theorem map_unrelabelJoint_injOn
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {v v' : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))}
    (hv : v ∈ jointRelabelWords (Lambda := Lambda) W)
    (hv' : v' ∈ jointRelabelWords (Lambda := Lambda) W)
    (h : v.map unrelabelJoint = v'.map unrelabelJoint) : v = v' := by
  rw [← map_relabelLetter_map_unrelabelJoint hv,
    ← map_relabelLetter_map_unrelabelJoint hv', h]

variable (selected : AuxiliaryPeripheralFamily A N S)
  (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))

/-- Every joint letter is a selected letter after reading back. -/
theorem unrelabelJoint_isLetter
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hfamInl : ∀ (lam : Lambda) (x : G),
      x ∈ joint.fam (Sum.inl lam) → x ∈ selected.rel.base)
    (hfamInr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.rel.fam i)
    {a : GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k))}
    (ha : joint.IsLetter a) : selected.rel.IsLetter (unrelabelJoint a) := by
  cases a with
  | base x => exact hbaseSub ha
  | comp s h =>
      cases s with
      | inl lam => exact hfamInl lam h ha
      | inr i =>
          show h ∈ selected.rel.fam i
          rw [← hfamInr i]
          exact ha

/-- Avoiding the `inr i` component survives the reading. -/
theorem avoidsFrom_map_unrelabelJoint
    (hfamInr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.rel.fam i)
    (i : AuxiliaryPeripheralIndex k)
    (word : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))) :
    ∀ v : G,
      GGT.AvoidsFrom joint.fam (Sum.inr i) word v →
        GGT.AvoidsFrom selected.rel.fam i (word.map unrelabelJoint) v := by
  induction word with
  | nil => simp [GGT.AvoidsFrom]
  | cons a t ih =>
      intro v hv
      constructor
      · rintro ⟨hcomp, hmem⟩
        apply hv.1
        refine ⟨(unrelabelJoint_isCompOf i a).mp hcomp, ?_⟩
        rw [hfamInr i]
        exact hmem
      · simpa [unrelabelJoint_val a] using ih (v * a.val) hv.2

/-- The joint relative ball at a selected peripheral embeds in the selected
one.  This is what makes the depth clause transport. -/
theorem relBall_inr_subset
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hfamInl : ∀ (lam : Lambda) (x : G),
      x ∈ joint.fam (Sum.inl lam) → x ∈ selected.rel.base)
    (hfamInr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.rel.fam i)
    (i : AuxiliaryPeripheralIndex k) (n : ℕ) :
    joint.relBall (Sum.inr i) n ⊆ selected.rel.relBall i n := by
  rintro x ⟨hmem, word, hletters, hval, havoid, hlen⟩
  refine ⟨?_, word.map unrelabelJoint, ?_, ?_, ?_, by simpa using hlen⟩
  · rw [← hfamInr i]
    exact hmem
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact unrelabelJoint_isLetter selected joint hbaseSub hfamInl hfamInr
      (hletters b hb)
  · rw [listVal_map_unrelabelJoint, hval]
  · exact avoidsFrom_map_unrelabelJoint selected joint hfamInr i word 1 havoid

/-! ### The piece relations -/

/-- A piece of the relabelled family reads back as a piece of the source
family.  Both relative alphabets are the same set, so the two `eps`-bounds are
the same statement. -/
theorem isPiece_map_unrelabelJoint
    (halphabet : joint.alphabet.carrier = selected.rel.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps : ℕ}
    {u v : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))}
    (h : RelWord.IsPiece joint (jointRelabelWords (Lambda := Lambda) W)
      eps u v) :
    RelWord.IsPiece selected.rel W eps (u.map unrelabelJoint)
      (v.map unrelabelJoint) := by
  obtain ⟨hv, ⟨s, hs⟩, v', hv', hne, u', s', hv'split,
    y, z, hy, hz, hval, hexcl⟩ := h
  refine ⟨mem_jointRelabelWords_source hv, ⟨s.map unrelabelJoint, ?_⟩,
    v'.map unrelabelJoint, mem_jointRelabelWords_source hv', ?_,
    u'.map unrelabelJoint, s'.map unrelabelJoint, ?_,
    y, z, ?_, ?_, ?_, ?_⟩
  · rw [hs, List.map_append]
  · intro hcontra
    exact hne (map_unrelabelJoint_injOn hv' hv hcontra)
  · rw [hv'split, List.map_append]
  · rw [← halphabet]
    exact hy
  · rw [← halphabet]
    exact hz
  · rw [listVal_map_unrelabelJoint, listVal_map_unrelabelJoint]
    exact hval
  · rw [listVal_map_unrelabelJoint, listVal_map_unrelabelJoint]
    exact hexcl

/-- The published piece relation reads back in the same way. -/
theorem isPublishedPiece_map_unrelabelJoint
    (halphabet : joint.alphabet.carrier = selected.rel.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps : ℕ}
    {u u' v : List (GGT.RelLetter G (Sum Lambda (AuxiliaryPeripheralIndex k)))}
    (h : RelWord.IsPublishedPiece joint
      (jointRelabelWords (Lambda := Lambda) W) eps u u' v) :
    RelWord.IsPublishedPiece selected.rel W eps (u.map unrelabelJoint)
      (u'.map unrelabelJoint) (v.map unrelabelJoint) := by
  obtain ⟨hv, ⟨s, hs⟩, v', hv', s', hv'split,
    y, z, hy, hz, hval, hexcl⟩ := h
  refine ⟨mem_jointRelabelWords_source hv, ⟨s.map unrelabelJoint, ?_⟩,
    v'.map unrelabelJoint, mem_jointRelabelWords_source hv',
    s'.map unrelabelJoint, ?_, y, z, ?_, ?_, ?_, ?_⟩
  · rw [hs, List.map_append]
  · rw [hv'split, List.map_append]
  · rw [← halphabet]
    exact hy
  · rw [← halphabet]
    exact hz
  · rw [listVal_map_unrelabelJoint, listVal_map_unrelabelJoint]
    exact hval
  · rw [listVal_map_unrelabelJoint, listVal_map_unrelabelJoint]
    exact hexcl

/-! ### The transported input -/

/-- **Hull's relator family, read in the joint peripheral family.**

The five bookkeeping clauses follow from the source clauses and the commutation
of relabelling with the two closure operations; the depth clause uses the
relative-ball inclusion; the two piece clauses and the quasi-geodesic clause use
the equality of the two relative alphabets; and strong boundedness holds because
a base letter never becomes a component letter.

The side condition is that the relator's base letters are already base letters
of the joint family.  For Hull's §6 relator that is `t⁻¹ ∈ joint.base`, by
`baseLetters_symmetrized_mem`. -/
theorem isLemma44Input_jointRelabelWords
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hfamInl : ∀ (lam : Lambda) (x : G),
      x ∈ joint.fam (Sum.inl lam) → x ∈ selected.rel.base)
    (hfamInr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.rel.fam i)
    (halphabet : joint.alphabet.carrier = selected.rel.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps rho : ℕ} {mu : ℝ}
    (hWbase : ∀ v ∈ W, ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base)
    (hsc : RelWord.IsLemma44Input selected.rel W eps mu rho) :
    RelWord.IsLemma44Input joint (jointRelabelWords (Lambda := Lambda) W)
      eps mu rho := by
  refine
    { admissible := ?_
      inv_mem := ?_
      rotate_mem := ?_
      long := ?_
      deep := ?_
      pieces_small := ?_
      quasiGeodesic := ?_
      publishedPiecesSmall := ?_
      stronglyBounded := ?_ }
  · intro v hv a ha
    obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
    rw [← hmap] at ha
    obtain ⟨a₀, ha₀, hab⟩ := List.mem_map.mp ha
    rw [← hab]
    cases a₀ with
    | base x =>
        show x ∈ joint.base
        exact hWbase v₀ hv₀ x ha₀
    | comp i g =>
        show g ∈ joint.fam (Sum.inr i)
        rw [hfamInr i]
        exact hsc.admissible v₀ hv₀ (GGT.RelLetter.comp i g) ha₀
  · intro v hv
    obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
    refine mem_jointRelabelWords_iff.mpr
      ⟨RelWord.revInv v₀, hsc.inv_mem v₀ hv₀, ?_⟩
    rw [← hmap, ← revInv_map_relabelLetter]
  · intro v hv n
    obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
    refine mem_jointRelabelWords_iff.mpr
      ⟨v₀.rotate n, hsc.rotate_mem v₀ hv₀ n, ?_⟩
    rw [← hmap, List.map_rotate]
  · intro v hv
    obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
    rw [← hmap, List.length_map]
    exact hsc.long v₀ hv₀
  · intro v hv a ha s hcomp
    obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
    rw [← hmap] at ha
    obtain ⟨a₀, ha₀, hab⟩ := List.mem_map.mp ha
    rw [← hab] at hcomp ⊢
    cases a₀ with
    | base x => exact (hcomp : False).elim
    | comp i g =>
        have hs : s = Sum.inr i := hcomp.symm
        subst hs
        have hdeep : g ∉ selected.rel.relBall i rho :=
          hsc.deep v₀ hv₀ (GGT.RelLetter.comp i g) ha₀ i rfl
        intro hball
        exact hdeep (relBall_inr_subset selected joint hbaseSub hfamInl
          hfamInr i rho hball)
  · intro u v hpiece
    have hsel := hsc.pieces_small (u.map unrelabelJoint) (v.map unrelabelJoint)
      (isPiece_map_unrelabelJoint selected joint halphabet hpiece)
    rw [List.length_map, List.length_map] at hsel
    exact hsel
  · intro v hv
    obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
    have hqg := hsc.quasiGeodesic v₀ hv₀
    have hchain : (fun i => GGT.RelLetter.listVal (v.take i)) =
        fun i => GGT.RelLetter.listVal (v₀.take i) := by
      funext i
      rw [← hmap, take_map_relabelLetter, listVal_map_relabelLetter]
    rw [halphabet, hchain, ← hmap, List.length_map]
    exact hqg
  · intro u u' v hpiece
    have hsel := hsc.publishedPiecesSmall (u.map unrelabelJoint)
      (u'.map unrelabelJoint) (v.map unrelabelJoint)
      (isPublishedPiece_map_unrelabelJoint selected joint halphabet hpiece)
    rw [List.length_map, List.length_map, List.length_map] at hsel
    exact hsel
  · refine Set.Finite.subset (Set.Finite.image
      (relabelLetter
        (Sum.inr : AuxiliaryPeripheralIndex k →
          Sum Lambda (AuxiliaryPeripheralIndex k))) hsc.stronglyBounded) ?_
    rintro a ⟨⟨s, g, rfl⟩, v, hv, ha⟩
    obtain ⟨v₀, hv₀, hmap⟩ := mem_jointRelabelWords_iff.mp hv
    rw [← hmap] at ha
    obtain ⟨a₀, ha₀, hab⟩ := List.mem_map.mp ha
    cases a₀ with
    | base x => exact absurd hab (by simp [relabelLetter])
    | comp i g' =>
        exact ⟨GGT.RelLetter.comp i g', ⟨⟨i, g', rfl⟩, v₀, hv₀, ha₀⟩, hab⟩

/-! ### The joint half of the re-spelling, discharged -/

/-- The joint family needs no re-spelling: the index relabelling is one, and it
meets any prescribed thresholds already met by the source relator. -/
theorem relatorRespellingAt_joint
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hfamInl : ∀ (lam : Lambda) (x : G),
      x ∈ joint.fam (Sum.inl lam) → x ∈ selected.rel.base)
    (hfamInr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.rel.fam i)
    (halphabet : joint.alphabet.carrier = selected.rel.alphabet.carrier)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho)
    (hWbase : ∀ v ∈ W, ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base)
    (hsc : RelWord.IsLemma44Input selected.rel W eps mu rho) :
    RelatorRespellingAt joint W eps0 rho0 mu :=
  relatorRespellingAt_of_relabel joint W
    (Sum.inr : AuxiliaryPeripheralIndex k →
      Sum Lambda (AuxiliaryPeripheralIndex k)) heps hrho h20
    (isLemma44Input_jointRelabelWords selected joint hbaseSub hfamInl hfamInr
      halphabet hWbase hsc)

end Transport

/-! ## What is left

`HullRelatorRespellingStatement` asks for a re-spelling over the original
family and one over the joint family.  The joint half is now a theorem,
`relatorRespellingAt_joint`, under three structural hypotheses and one side
condition on the relator:

* `joint.base ⊆ selected.rel.base` and
  `joint.alphabet.carrier = selected.rel.alphabet.carrier`: the two families are
  two peripheral structures on the same relative alphabet.  Hull's alphabet is
  the original relative alphabet together with the finitely many adjoined target
  letters, so this is what the selection input should be asked to produce.
* `∀ lam x, x ∈ joint.fam (Sum.inl lam) → x ∈ selected.rel.base`: free from the
  family form's own hypothesis `original.alphabet.carrier ⊆ A.alphabet.carrier`
  together with `AuxiliaryPeripheralFamily.base_le`.
* the side condition `∀ v ∈ W, ∀ x, base x ∈ v → x ∈ joint.base`, which for
  Hull's §6 relator is `t⁻¹ ∈ joint.base` by `baseLetters_symmetrized_mem`,
  since every base letter of that relator is `t⁻¹`.

The original half is not a relabelling and stays an input: the selected
peripheral letters are not letters of the original family, so re-spelling them
changes the length of every relator and therefore all three
small-cancellation parameters.  It is named next. -/

/-- **The residual re-spelling, over the original peripheral family alone.**

Hull's relators, presented over the selected auxiliary alphabet, have a
re-spelling over the original family with the same normal closure and again a
Lemma 4.4 input above the prescribed thresholds.  The source thresholds are
chosen after the target thresholds, as in `HullRelatorRespellingStatement`.

Its conclusion is model-tested by `relatorRespellingAt_empty`. -/
def OriginalRelatorRespellingStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda),
    original.IsHyperbolicallyEmbedded →
    original.alphabet.carrier ⊆ A.alphabet.carrier →
    ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 1000 →
      ∀ eps0 rho0 : ℕ,
        ∃ eps rho : ℕ,
          ∀ W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
            RelWord.IsLemma44Input selected.rel W eps mu rho →
              RelatorRespellingAt original W eps0 rho0 mu

end HullSC
end GroupApproximation
