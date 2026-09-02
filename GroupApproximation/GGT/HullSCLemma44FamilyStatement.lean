import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullSCLemma44QuotientRelGenSet

/-!
# Hull Lemma 4.4 for an arbitrary labelled peripheral family

Hull's printed Lemma 4.4 is applied to one relative alphabet containing every
peripheral that must survive the quotient.  For Osin's Theorem 2.4 this is the
combined family

`original peripherals ⊕ selected elementary closures`.

The base is the original finite relative base, enlarged by the target and its
inverse.  The original peripheral letters remain labelled family letters; the
selected elementary closures are additional labelled family letters.  This is
why the hypothesis below is containment of Hull's alphabet in the *full
relative alphabet*.  Requiring containment in the base would be false for an
infinite original peripheral and would contradict
`RelGenSet.not_isHyperbolicallyEmbedded_of_fam_subset_base`.

The quotient relative generating set is canonical: its base is the image of
the source base and each peripheral is the corresponding subgroup image.  Thus
a finite source base stays finite, the original peripheral family remains
relatively hyperbolic in the quotient, and union injectivity applies at once to
both the original and selected parts of the combined family.

`hullLemma44CanonicalQuotientStatement_of_family` specializes this arbitrary
form to the existing selected-family interface.  The conversion uses the
canonical base equality and `AuxiliaryPeripheralFamily.fam_eq`; no quotient is
chosen again.  The bijective and empty-relator lemmas are model tests for the
new output structure.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Canonical preservation -/

/-- The canonical quotient image of an arbitrary labelled peripheral family. -/
structure CanonicalQuotientFamilyPreservation
    {G : Type u} [Group G] {Lambda : Type w} {Q : Type u} [Group Q]
    (q : G →* Q) (D : GGT.RelGenSet G Lambda) where
  /-- The quotient relative structure. -/
  rel : GGT.RelGenSet Q Lambda
  /-- Its base is exactly the image of the source base. -/
  base_map : rel.base = q '' D.base
  /-- Its labelled peripherals are the corresponding subgroup images. -/
  fam_map : ∀ lam : Lambda, rel.fam lam = (D.fam lam).map q
  /-- The quotient family remains hyperbolically embedded. -/
  embedded : rel.IsHyperbolicallyEmbedded
  /-- The quotient is injective on the union of all source peripherals. -/
  injOn_peripheralUnion :
    Set.InjOn q (⋃ lam : Lambda, (D.fam lam : Set G))

namespace CanonicalQuotientFamilyPreservation

variable {G : Type u} [Group G] {Lambda : Type w} {Q : Type u} [Group Q]
  {q : G →* Q} {D : GGT.RelGenSet G Lambda}

/-- Union injectivity restricts to each labelled peripheral. -/
theorem injOn_fam (P : CanonicalQuotientFamilyPreservation q D)
    (lam : Lambda) : Set.InjOn q (D.fam lam : Set G) := by
  intro x hx y hy hxy
  exact P.injOn_peripheralUnion
    (Set.mem_iUnion.mpr ⟨lam, hx⟩)
    (Set.mem_iUnion.mpr ⟨lam, hy⟩) hxy

/-- A finite source relative base has finite image base in the quotient. -/
theorem base_finite (P : CanonicalQuotientFamilyPreservation q D)
    (hfinite : D.base.Finite) : P.rel.base.Finite := by
  rw [P.base_map]
  exact hfinite.image q

/-- Inversion closure of the source base passes to the canonical image base. -/
theorem base_inv (P : CanonicalQuotientFamilyPreservation q D)
    (hinv : ∀ x ∈ D.base, x⁻¹ ∈ D.base) :
    ∀ y ∈ P.rel.base, y⁻¹ ∈ P.rel.base := by
  intro y hy
  rw [P.base_map] at hy ⊢
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x⁻¹, hinv x hx, by simp⟩

end CanonicalQuotientFamilyPreservation

/-! ## Arbitrary-family Lemma 4.4 -/

/-- **Hull Lemma 4.4, canonical quotient, arbitrary-family form.**

The source family may have any index type.  Hull's chosen alphabet only has to
map into the full relative alphabet, which is exactly the condition satisfied
by the combined original-and-selected family.  The constants retain the
printed order: source geometry and requested ball first, relators and quotient
afterwards. -/
def HullLemma44CanonicalQuotientFamilyStatement : Prop :=
  ∀ {G : Type u} [Group G] {Lambda : Type w}
    (A : HullGeneratingSet G) (D : GGT.RelGenSet G Lambda),
      A.alphabet.carrier ⊆ D.alphabet.carrier →
      (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
      D.IsHyperbolicallyEmbedded →
      ∀ R : ℕ,
        ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
          ∀ (W : Set (List (GGT.RelLetter G Lambda)))
            {Q : Type u} [Group Q] (q : G →* Q),
            RelWord.IsLemma44Input D W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (CanonicalQuotientFamilyPreservation q D)

/-! ## Model tests -/

/-- A bijective homomorphism canonically preserves every source family. -/
theorem canonicalQuotientFamilyPreservation_of_bijective
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (hD : D.IsHyperbolicallyEmbedded)
    {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Bijective q) :
    Nonempty (CanonicalQuotientFamilyPreservation q D) := by
  refine ⟨{
    rel := D.mapSurjective q hq.2
    base_map := rfl
    fam_map := fun _ => rfl
    embedded := GGT.RelGenSet.isHyperbolicallyEmbedded_mapSurjective_of_bijective
      D hD q hq
    injOn_peripheralUnion := hq.1.injOn }⟩

/-- Empty relators force a surjective natural quotient to be bijective, so the
full arbitrary family and every requested Cayley ball are preserved. -/
theorem hullLemma44CanonicalFamily_empty
    {G : Type u} [Group G] {Lambda : Type w}
    (A : HullGeneratingSet G) (D : GGT.RelGenSet G Lambda)
    (hD : D.IsHyperbolicallyEmbedded) (R : ℕ)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hsurj : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure
      (GGT.RelLetter.listVal ''
        (∅ : Set (List (GGT.RelLetter G Lambda))))) :
    Set.InjOn q (cayleyBall A.alphabet R) ∧
      Nonempty (CanonicalQuotientFamilyPreservation q D) := by
  have hbot : q.ker = ⊥ := by
    simpa using hker
  have hinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hbot
  exact ⟨hinj.injOn,
    canonicalQuotientFamilyPreservation_of_bijective D hD q ⟨hinj, hsurj⟩⟩

/-! ## Specialization to the selected auxiliary family -/

/-- Canonical arbitrary-family preservation specializes to the existing
selected-family record. -/
def CanonicalQuotientFamilyPreservation.toAuxiliary
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {Q : Type u} [Group Q] {q : G →* Q}
    (P : CanonicalQuotientFamilyPreservation q D.rel) :
    QuotientPeripheralPreservation q D where
  rel := P.rel
  base_image := by
    intro a ha
    rw [P.base_map]
    exact ⟨a, D.base_le ha, rfl⟩
  fam_map := by
    intro i
    rw [P.fam_map i, D.fam_eq i]
  embedded := P.embedded
  injOn_peripheralUnion := by
    intro x hx y hy hxy
    apply P.injOn_peripheralUnion
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨i, by rwa [D.fam_eq i]⟩
    · obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hy
      exact Set.mem_iUnion.mpr ⟨i, by rwa [D.fam_eq i]⟩
    · exact hxy

/-- The arbitrary-family statement implies the existing canonical statement
by applying it to the selected family itself. -/
theorem hullLemma44CanonicalQuotientStatement_of_family
    (h44 : HullLemma44CanonicalQuotientFamilyStatement.{u, 0}) :
    HullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S D R
  have halphabet : A.alphabet.carrier ⊆ D.rel.alphabet.carrier :=
    D.base_le.trans (Set.subset_union_left)
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    h44 A D.rel halphabet D.base_inv D.embedded R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨hinj, ⟨P⟩⟩ := hgood W q hinput hsurj hker
  exact ⟨hinj, ⟨P.toAuxiliary D⟩⟩

end HullSC
end GroupApproximation
