import GroupApproximation.GGT.HullSCCanonicalQuotientPublished

/-!
# Hull Lemma 4.4 for an arbitrary peripheral family

Hull's printed Lemma 4.4 is not restricted to the finite family of elementary
closures chosen later in the filling construction.  It starts with an
arbitrary hyperbolically embedded family and says that a sufficiently strong
relative small-cancellation quotient preserves that whole family.  The
application to Osin's Theorem 2.4 needs exactly this quantifier: the original
peripheral family must remain present alongside the finitely many elementary
closures selected inside the suitable subgroup.

`HullLemma44CanonicalQuotientStatement` currently packages the special case
whose index type is `AuxiliaryPeripheralIndex k`.  This module states the
family form directly over an arbitrary index type `Λ`.  There are no new
geometric assumptions hidden in the wrapper:

* `D.IsHyperbolicallyEmbedded` is the source family in Hull's lemma;
* `A.alphabet.carrier ⊆ D.base` lets its requested Cayley ball be read in the
  relative base;
* inversion closure of `D.base` is the convention used by the diagram lemmas;
* the output contains the mapped family, its hyperbolic embeddedness, and
  injectivity on the union of every source peripheral.

The quotient is still the natural quotient by the values of `W`.  In
particular the family statement does not postulate an unrelated quotient and
does not alter the quantifier order of the small-cancellation constants.

`hullLemma44CanonicalQuotientStatement_of_family` proves that this is a genuine
generalisation of the existing interface by specializing `Λ` to
`AuxiliaryPeripheralIndex k`.  The conversion of the preservation records is
literal, using `AuxiliaryPeripheralFamily.fam_eq` only to change the displayed
name of each subgroup.

The empty-relator/bijective quotient lemmas are model tests for the new output
record.  They show that its fields can be inhabited simultaneously and that
the arbitrary-family conclusion has the expected identity-quotient model.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## 1. Preservation of an arbitrary indexed family -/

/-- The family-valued output of Hull Lemma 4.4.

Unlike `QuotientPeripheralPreservation`, this record does not mention the
chosen elementary cores.  Its source is an arbitrary relative generating set,
so it can preserve the original relatively hyperbolic peripheral family and
the selected elementary closures in one application. -/
structure CanonicalQuotientFamilyPreservation
    {G : Type u} [Group G] {Λ : Type w} {Q : Type u} [Group Q]
    (A : HullGeneratingSet G) (q : G →* Q) (D : GGT.RelGenSet G Λ) where
  /-- The quotient relative generating set, with the same labels. -/
  rel : GGT.RelGenSet Q Λ
  /-- The old Hull alphabet maps into the quotient relative base. -/
  base_image : ∀ a ∈ A.alphabet.carrier, q a ∈ rel.base
  /-- The quotient relative base retains the symmetric-base convention used
  by the arbitrary-index almost-malnormality theorem. -/
  base_inv : ∀ x ∈ rel.base, x⁻¹ ∈ rel.base
  /-- Every quotient peripheral is the image of its source peripheral. -/
  fam_map : ∀ lam : Λ, rel.fam lam = (D.fam lam).map q
  /-- The entire mapped family remains hyperbolically embedded. -/
  embedded : rel.IsHyperbolicallyEmbedded
  /-- No two elements belonging to the union of source peripherals collapse. -/
  injOn_peripheralUnion :
    Set.InjOn q (⋃ lam : Λ, (D.fam lam : Set G))

namespace CanonicalQuotientFamilyPreservation

variable {G : Type u} [Group G] {Λ : Type w} {Q : Type u} [Group Q]
  {A : HullGeneratingSet G} {q : G →* Q} {D : GGT.RelGenSet G Λ}

/-- The preservation record immediately gives injectivity on any one member
of the source family. -/
theorem injOn_fam (P : CanonicalQuotientFamilyPreservation A q D)
    (lam : Λ) : Set.InjOn q (D.fam lam : Set G) := by
  intro x hx y hy hxy
  exact P.injOn_peripheralUnion
    (Set.mem_iUnion.mpr ⟨lam, hx⟩)
    (Set.mem_iUnion.mpr ⟨lam, hy⟩) hxy

/-- The preserved family is pointwise the mapped source family. -/
theorem fam_eq_map (P : CanonicalQuotientFamilyPreservation A q D)
    (lam : Λ) : P.rel.fam lam = (D.fam lam).map q :=
  P.fam_map lam

end CanonicalQuotientFamilyPreservation

/-! ## 2. The arbitrary-family statement -/

/-- **Hull Lemma 4.4, canonical quotient, arbitrary-family form.**

The constants are chosen after the source relative structure and requested
ball radius, but before the relator family and quotient.  This is the printed
quantifier order.  The conclusion simultaneously supplies ball injectivity
and preservation of every labelled peripheral. -/
def HullLemma44CanonicalQuotientFamilyStatement : Prop :=
  ∀ {G : Type u} [Group G] {Λ : Type w}
    (A : HullGeneratingSet G) (D : GGT.RelGenSet G Λ),
      A.alphabet.carrier ⊆ D.base →
      (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
      D.IsHyperbolicallyEmbedded →
      ∀ R : ℕ,
        ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
          ∀ (W : Set (List (GGT.RelLetter G Λ)))
            {Q : Type u} [Group Q] (q : G →* Q),
            RelWord.IsLemma44Input D W eps mu rho →
            Function.Surjective q →
            q.ker = Subgroup.normalClosure (GGT.RelLetter.listVal '' W) →
              Set.InjOn q (cayleyBall A.alphabet R) ∧
                Nonempty (CanonicalQuotientFamilyPreservation A q D)

/-! ## 3. Model tests -/

/-- A bijective homomorphism transports an arbitrary preserved family.  This
is the identity-quotient model of the family output record. -/
theorem canonicalQuotientFamilyPreservation_of_bijective_of_embedded
    {G : Type u} [Group G] {Λ : Type w}
    (A : HullGeneratingSet G) (D : GGT.RelGenSet G Λ)
    (hbase : A.alphabet.carrier ⊆ D.base)
    (hbaseInv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hemb : D.IsHyperbolicallyEmbedded)
    {Q : Type u} [Group Q] (q : G →* Q) (hq : Function.Bijective q) :
    Nonempty (CanonicalQuotientFamilyPreservation A q D) := by
  let e : G ≃* Q := MulEquiv.ofBijective q hq
  refine ⟨{
    rel := D.mapMulEquiv e
    base_image := ?_
    base_inv := ?_
    fam_map := fun _ => rfl
    embedded := hemb.mapMulEquiv e
    injOn_peripheralUnion := hq.1.injOn }⟩
  · intro a ha
    change q a ∈ q '' D.base
    exact ⟨a, hbase ha, rfl⟩
  · intro y hy
    change y⁻¹ ∈ (e : G →* Q) '' D.base
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x⁻¹, hbaseInv x hx, by simp⟩

/-- Empty relators force a surjective natural quotient to be bijective, so the
full arbitrary-family conclusion holds.  This checks the ball and peripheral
parts together at the smallest relator family. -/
theorem hullLemma44CanonicalFamily_empty
    {G : Type u} [Group G] {Λ : Type w}
    (A : HullGeneratingSet G) (D : GGT.RelGenSet G Λ)
    (hbase : A.alphabet.carrier ⊆ D.base)
    (hbaseInv : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (hemb : D.IsHyperbolicallyEmbedded) (R : ℕ)
    {Q : Type u} [Group Q] (q : G →* Q)
    (hsurj : Function.Surjective q)
    (hker : q.ker = Subgroup.normalClosure
      (GGT.RelLetter.listVal ''
        (∅ : Set (List (GGT.RelLetter G Λ))))) :
    Set.InjOn q (cayleyBall A.alphabet R) ∧
      Nonempty (CanonicalQuotientFamilyPreservation A q D) := by
  have hbot : q.ker = ⊥ := by
    simpa using hker
  have hinj : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp hbot
  exact ⟨hinj.injOn,
    canonicalQuotientFamilyPreservation_of_bijective_of_embedded
      A D hbase hbaseInv hemb q ⟨hinj, hsurj⟩⟩

/-! ## 4. Specialisation to the existing auxiliary-family interface -/

/-- Convert arbitrary-family preservation at `D.rel` to the existing record
whose family is displayed through `D.cores.peripheral`. -/
def CanonicalQuotientFamilyPreservation.toAuxiliary
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (D : AuxiliaryPeripheralFamily A N S)
    {Q : Type u} [Group Q] {q : G →* Q}
    (P : CanonicalQuotientFamilyPreservation A q D.rel) :
    QuotientPeripheralPreservation q D where
  rel := P.rel
  base_image := P.base_image
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

/-- The arbitrary-family Lemma 4.4 implies the existing canonical auxiliary
statement by literal specialization.  Downstream Hull modules therefore need
no compatibility layer and can continue consuming their current named Prop. -/
theorem hullLemma44CanonicalQuotientStatement_of_family
    (h44 : HullLemma44CanonicalQuotientFamilyStatement.{u, 0}) :
    HullLemma44CanonicalQuotientStatement.{u} := by
  intro G _ A N k S D R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ :=
    h44 A D.rel D.base_le D.base_inv D.embedded R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W Q _ q hinput hsurj hker
  obtain ⟨hinj, ⟨P⟩⟩ := hgood W q hinput hsurj hker
  exact ⟨hinj, ⟨P.toAuxiliary D⟩⟩

end HullSC
end GroupApproximation
