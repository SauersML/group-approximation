import GroupApproximation.GGT.HullSCFillingNonElementary
import GroupApproximation.GGT.RelGenSetMulEquiv

/-!
# The quotient relative generating set in Hull's Lemma 4.4

Hull's Lemma 4.4 uses the relative generating set whose base is the image of
the source base and whose peripheral subgroups are the subgroup images.  This
file constructs that object for every surjective homomorphism.  It also proves
the letter-lifting statements used by the relative isoperimetric argument and
assembles `QuotientPeripheralPreservation` once hyperbolic embeddedness of this
specific relative generating set has been established.

No choice of quotient presentation occurs here.  The construction depends only
on the source relative generating set, the homomorphism, and its surjectivity.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

namespace RelGenSet

/-- The image relative generating set under a surjective homomorphism. -/
noncomputable def mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q) :
    RelGenSet Q Lambda where
  base := q '' D.base
  fam := fun i => (D.fam i).map q
  symmetricGenerating := by
    have hcarrier :
        q '' (D.base ∪ ⋃ i : Lambda, (D.fam i : Set G)) =
          (q '' D.base) ∪
            ⋃ i : Lambda, (((D.fam i).map q : Subgroup Q) : Set Q) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with hx | hx
        · exact Set.mem_union_left _ ⟨x, hx, rfl⟩
        · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
          exact Set.mem_union_right _
            (Set.mem_iUnion.mpr ⟨i, ⟨x, hxi, rfl⟩⟩)
      · intro hy
        rcases hy with hy | hy
        · obtain ⟨x, hx, rfl⟩ := hy
          exact ⟨x, Set.mem_union_left _ hx, rfl⟩
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
          change ∃ x, x ∈ D.fam i ∧ q x = y at hi
          obtain ⟨x, hx, rfl⟩ := hi
          exact ⟨x, Set.mem_union_right _
            (Set.mem_iUnion.mpr ⟨i, hx⟩), rfl⟩
    rw [← hcarrier]
    exact Hyperbolic.isSymmetricGeneratingSet_image q hq
      D.symmetricGenerating

@[simp] theorem base_mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q) :
    (D.mapSurjective q hq).base = q '' D.base := rfl

@[simp] theorem fam_mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q)
    (i : Lambda) :
    (D.mapSurjective q hq).fam i = (D.fam i).map q := rfl

/-- The quotient relative alphabet is exactly the image of the source relative
alphabet. -/
theorem alphabet_carrier_mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q) :
    (D.mapSurjective q hq).alphabet.carrier = q '' D.alphabet.carrier := by
  ext y
  constructor
  · intro hy
    rcases hy with hy | hy
    · obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨x, Set.mem_union_left _ hx, rfl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
      change ∃ x, x ∈ D.fam i ∧ q x = y at hi
      obtain ⟨x, hx, rfl⟩ := hi
      exact ⟨x, Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, hx⟩), rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · exact Set.mem_union_left _ ⟨x, hx, rfl⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_union_right _
        (Set.mem_iUnion.mpr ⟨i, ⟨x, hi, rfl⟩⟩)

/-- Every legal source relative letter maps to a legal quotient relative
letter. -/
theorem isLetter_mapHom_mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q)
    {a : RelLetter G Lambda} (ha : D.IsLetter a) :
    (D.mapSurjective q hq).IsLetter (RelLetter.mapHom q a) := by
  cases a with
  | base x => exact ⟨x, ha, rfl⟩
  | comp i x => exact ⟨x, ha, rfl⟩

/-- Every legal quotient relative letter has a legal source lift of the same
kind. -/
theorem exists_sourceLetter_of_isLetter_mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q)
    {a : RelLetter Q Lambda} (ha : (D.mapSurjective q hq).IsLetter a) :
    ∃ b : RelLetter G Lambda,
      D.IsLetter b ∧ RelLetter.mapHom q b = a := by
  cases a with
  | base y =>
      obtain ⟨x, hx, hxy⟩ := ha
      exact ⟨RelLetter.base x, hx, by rw [RelLetter.mapHom, hxy]⟩
  | comp i y =>
      obtain ⟨x, hx, hxy⟩ := ha
      exact ⟨RelLetter.comp i x, hx, by rw [RelLetter.mapHom, hxy]⟩

/-- A legal quotient relative word lifts letter-by-letter to a legal source
word, preserving length and the formal base/component tags. -/
theorem exists_sourceWord_of_admissible_mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q) :
    ∀ word : List (RelLetter Q Lambda),
      (∀ a ∈ word, (D.mapSurjective q hq).IsLetter a) →
        ∃ source : List (RelLetter G Lambda),
          (∀ b ∈ source, D.IsLetter b) ∧
          source.map (RelLetter.mapHom q) = word ∧
          source.length = word.length
  | [], _ => ⟨[], by simp, rfl, rfl⟩
  | a :: tail, hword => by
      obtain ⟨b, hb, hba⟩ :=
        exists_sourceLetter_of_isLetter_mapSurjective D q hq
          (hword a (by simp))
      obtain ⟨sourceTail, htail, hmapTail, hlengthTail⟩ :=
        exists_sourceWord_of_admissible_mapSurjective D q hq tail
          (fun c hc => hword c (by simp [hc]))
      refine ⟨b :: sourceTail, ?_, ?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hb
        · exact htail c hc
      · simp only [List.map_cons, hba, hmapTail]
      · simp only [List.length_cons, hlengthTail]

/-- Mapping the lifted source word recovers the value of the quotient word. -/
theorem map_listVal_sourceWord
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (q : G →* Q) {source : List (RelLetter G Lambda)}
    {word : List (RelLetter Q Lambda)}
    (hmap : source.map (RelLetter.mapHom q) = word) :
    q (RelLetter.listVal source) = RelLetter.listVal word := by
  rw [← hmap, RelLetter.listVal_map_mapHom]

/-- The letterwise lift simultaneously preserves admissibility, length, and
the group value after applying the quotient homomorphism. -/
theorem exists_sourceWord_value_of_admissible_mapSurjective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q)
    (word : List (RelLetter Q Lambda))
    (hword : ∀ a ∈ word, (D.mapSurjective q hq).IsLetter a) :
    ∃ source : List (RelLetter G Lambda),
      (∀ b ∈ source, D.IsLetter b) ∧
      source.length = word.length ∧
      q (RelLetter.listVal source) = RelLetter.listVal word := by
  obtain ⟨source, hsource, hmap, hlength⟩ :=
    exists_sourceWord_of_admissible_mapSurjective D q hq word hword
  exact ⟨source, hsource, hlength, map_listVal_sourceWord q hmap⟩

/-- For a bijective homomorphism, the surjective-image construction is the
usual transport across the induced group equivalence. -/
theorem isHyperbolicallyEmbedded_mapSurjective_of_bijective
    {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}
    (D : RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    (q : G →* Q) (hq : Function.Bijective q) :
    (D.mapSurjective q hq.2).IsHyperbolicallyEmbedded := by
  let e : G ≃* Q := MulEquiv.ofBijective q hq
  have heq : D.mapSurjective q hq.2 = D.mapMulEquiv e := by
    apply RelGenSet.ext
    · rfl
    · funext i
      rfl
  rw [heq]
  exact hD.mapMulEquiv e

end RelGenSet
end GGT

namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree

/-- Hyperbolic embeddedness of the concrete image relative generating set,
together with peripheral-union injectivity, gives the complete peripheral
preservation output of Hull's Lemma 4.4. -/
theorem quotientPeripheralPreservation_of_mapSurjective
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hq : Function.Surjective q)
    (hemb : (D.rel.mapSurjective q hq).IsHyperbolicallyEmbedded)
    (hinj : Set.InjOn q
      (⋃ i : AuxiliaryPeripheralIndex k,
        (D.cores.peripheral i : Set G))) :
    Nonempty (QuotientPeripheralPreservation q D) := by
  refine ⟨{
    rel := D.rel.mapSurjective q hq
    base_image := ?_
    fam_map := ?_
    embedded := hemb
    injOn_peripheralUnion := hinj }⟩
  · intro a ha
    exact ⟨a, D.base_le ha, rfl⟩
  · intro i
    rw [GGT.RelGenSet.fam_mapSurjective, D.fam_eq i]

end HullSC
end GroupApproximation
