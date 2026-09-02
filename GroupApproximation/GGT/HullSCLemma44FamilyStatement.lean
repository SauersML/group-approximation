import GroupApproximation.GGT.HullSCCanonicalQuotientPublished
import GroupApproximation.GGT.HullSCLemma44QuotientRelGenSet
import GroupApproximation.GGT.OsinTheorem54SepSymmetric

/-!
# Hull Lemma 4.4 with a preserved peripheral family

Hull's small-cancellation relators are read in the relative alphabet of the
finitely many elementary closures selected inside the suitable subgroups.  In
the relatively hyperbolic application, there is a second relative structure:
the original peripheral family.  Its relative Cayley alphabet is Hull's
generating alphabet, and Lemma 4.4 preserves it through the same quotient.

These two structures must remain distinct.  Putting an original infinite
peripheral both in Hull's alphabet and in the family of a relative generating
set whose base contains that alphabet violates local finiteness: the peripheral
then lies in its own radius-one relative ball through base-labelled edges.  The
checked obstruction is
`RelGenSet.not_isHyperbolicallyEmbedded_of_fam_subset_base`.

`HullLemma44CanonicalQuotientFamilyStatement` consequently quantifies over:

* an `AuxiliaryPeripheralFamily`, whose letters spell the relator; and
* an arbitrary hyperbolically embedded `preserved` family whose relative
  alphabet equals Hull's alphabet.

The output for the preserved family is the canonical surjective image relative
generating set.  Its base is exactly `q '' preserved.base`, so finiteness of an
Osin relative base survives the quotient.  The selected auxiliary elementary
closures are preserved at the same time through the existing
`QuotientPeripheralPreservation` record.

Specializing the preserved family to the empty family recovers
`HullLemma44CanonicalQuotientStatement`.  Thus the family statement is a strict
extension of the existing interface and remains usable by all Hull consumers.
The bijective and empty-relator theorems below are model tests for every field
of the new conclusion.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Preservation of the original family -/

/-- The canonical quotient image of an arbitrary source peripheral family.

The base equality is part of the conclusion because it is the bridge from a
finite relative base in `G` to a finite relative base in the quotient. -/
structure CanonicalQuotientFamilyPreservation
    {G : Type u} [Group G] {Lambda : Type w} {Q : Type u} [Group Q]
    (q : G →* Q) (D : GGT.RelGenSet G Lambda) where
  /-- The quotient relative structure. -/
  rel : GGT.RelGenSet Q Lambda
  /-- Its base is the image of the source relative base. -/
  base_map : rel.base = q '' D.base
  /-- Its labelled peripherals are the subgroup images. -/
  fam_map : ∀ lam : Lambda, rel.fam lam = (D.fam lam).map q
  /-- The image family is hyperbolically embedded. -/
  embedded : rel.IsHyperbolicallyEmbedded
  /-- The quotient is injective on the union of the source peripherals. -/
  injOn_peripheralUnion :
    Set.InjOn q (⋃ lam : Lambda, (D.fam lam : Set G))

namespace CanonicalQuotientFamilyPreservation

variable {G : Type u} [Group G] {Lambda : Type w} {Q : Type u} [Group Q]
  {q : G →* Q} {D : GGT.RelGenSet G Lambda}

/-- Preservation of the union implies injectivity on each labelled member. -/
theorem injOn_fam (P : CanonicalQuotientFamilyPreservation q D)
    (lam : Lambda) : Set.InjOn q (D.fam lam : Set G) := by
  intro x hx y hy hxy
  exact P.injOn_peripheralUnion
    (Set.mem_iUnion.mpr ⟨lam, hx⟩)
    (Set.mem_iUnion.mpr ⟨lam, hy⟩) hxy

/-- The quotient base is finite whenever the source base is finite. -/
theorem base_finite (P : CanonicalQuotientFamilyPreservation q D)
    (hfinite : D.base.Finite) : P.rel.base.Finite := by
  rw [P.base_map]
  exact hfinite.image q

/-- The displayed quotient family is pointwise the mapped source family. -/
theorem fam_eq_map (P : CanonicalQuotientFamilyPreservation q D)
    (lam : Lambda) : P.rel.fam lam = (D.fam lam).map q :=
  P.fam_map lam

end CanonicalQuotientFamilyPreservation

/-! ## The two-structure statement -/

/-- **Hull Lemma 4.4, canonical quotient, arbitrary preserved-family form.**

`selected` is the finite elementary-closure family used to spell the
small-cancellation relators.  `preserved` is an arbitrary hyperbolically
embedded family whose relative Cayley alphabet is Hull's chosen alphabet.  The
same natural quotient preserves both families and is injective on the requested
Cayley ball and on the union of the original peripherals. -/
def HullLemma44CanonicalQuotientFamilyStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (preserved : GGT.RelGenSet G Lambda),
      preserved.alphabet = A.alphabet →
      preserved.IsHyperbolicallyEmbedded →
      ∀ R : ℕ,
        ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
          ∀ (W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))))
            {Q : Type u} [Group Q] (q : G →* Q),
            RelWord.IsLemma44Input selected.rel W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (QuotientPeripheralPreservation q selected) ∧
                Nonempty (CanonicalQuotientFamilyPreservation q preserved)

/-! ## Model tests -/

/-- A bijective homomorphism canonically preserves an arbitrary source family. -/
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

/-- Empty relators force the natural quotient to be bijective, so both the
selected family and any arbitrary original family are preserved together. -/
theorem hullLemma44CanonicalFamily_empty
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (preserved : GGT.RelGenSet G Lambda)
    (hpreserved : preserved.IsHyperbolicallyEmbedded) (R : ℕ)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hsurj : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure
      (GGT.RelLetter.listVal ''
        (∅ : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))))) :
    Set.InjOn q (cayleyBall A.alphabet R) ∧
      Nonempty (QuotientPeripheralPreservation q selected) ∧
      Nonempty (CanonicalQuotientFamilyPreservation q preserved) := by
  have hbot : q.ker = ⊥ := by
    simpa using hker
  have hinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hbot
  have hbij : Function.Bijective q := ⟨hinj, hsurj⟩
  exact ⟨hinj.injOn,
    quotientPeripheralPreservation_of_bijective selected q hbij,
    canonicalQuotientFamilyPreservation_of_bijective preserved hpreserved q hbij⟩

/-! ## Empty-family specialization -/

/-- The empty peripheral family whose base is exactly Hull's alphabet. -/
def emptyPreservedRelGenSet {G : Type u} [Group G]
    (A : HullGeneratingSet G) : GGT.RelGenSet G Empty where
  base := A.alphabet.carrier
  fam := Empty.elim
  symmetricGenerating := by
    simpa using A.alphabet.symmetricGenerating

/-- The empty-family relative alphabet is Hull's alphabet. -/
theorem emptyPreservedRelGenSet_alphabet {G : Type u} [Group G]
    (A : HullGeneratingSet G) :
    (emptyPreservedRelGenSet A).alphabet = A.alphabet := by
  apply GGT.OsinComponents.alphabet_eq_of_carrier_eq
  simp [emptyPreservedRelGenSet]

/-- The empty family is hyperbolically embedded precisely using the
hyperbolicity already bundled in Hull's generating set. -/
theorem emptyPreservedRelGenSet_embedded {G : Type u} [Group G]
    (A : HullGeneratingSet G) :
    (emptyPreservedRelGenSet A).IsHyperbolicallyEmbedded := by
  refine ⟨?_, ?_⟩
  · rw [emptyPreservedRelGenSet_alphabet A]
    exact ⟨A.delta, A.hyperbolic⟩
  · intro lam
    exact Empty.elim lam

/-- The arbitrary-family statement implies the existing canonical statement
by taking the second, preserved family to be empty. -/
theorem hullLemma44CanonicalQuotientStatement_of_family
    (h44 : HullLemma44CanonicalQuotientFamilyStatement.{u, 0}) :
    HullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S selected R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    h44 selected (emptyPreservedRelGenSet A)
      (emptyPreservedRelGenSet_alphabet A)
      (emptyPreservedRelGenSet_embedded A) R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨hinj, hselected, _hempty⟩ :=
    hgood W q hinput hsurj hker
  exact ⟨hinj, hselected⟩

end HullSC
end GroupApproximation
