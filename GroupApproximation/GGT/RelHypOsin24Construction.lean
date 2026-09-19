import GroupApproximation.GGT.RelHypOsinTheorem24Verbatim
import GroupApproximation.GroupTheory.FiniteRelatorQuotient

/-!
# The literal finite-relator quotient in Osin's Theorem 2.4

This module formalizes the algebraic construction in the proof of Osin,
*Small cancellations over relatively hyperbolic groups and embedding theorems*,
Theorem 2.4.  For a finite set of prescribed elements, the proof chooses one
element of the suitable subgroup for each prescribed element and adds the
corresponding relation

```
  t_i h_i⁻¹ = 1.
```

The quotient below is literally the quotient by the normal closure of that
finite family.  It follows without any geometric input that the quotient map
is onto, that every prescribed element maps into the image of the suitable
subgroup, and that its kernel is finitely normally generated.

The geometric input from Osin's proof is deliberately split into its three
source conclusions rather than being hidden in a new quotient-existence
assumption:

* `IsOsin24RelativeQuotientConclusion` is Lemma 4.4 together with the
  relative-hyperbolicity conclusion of Theorem 4.1 at the chosen quotient;
* `IsOsin24SuitabilityConclusion` is the elementary-subgroup and almost-
  malnormality argument in the proof of Theorem 2.4;
* `IsOsin24TorsionConclusion` is Lemma 5.1.

Each is a predicate at one already-constructed map, and each has an identity
map model.  Thus none is an alternative formulation of the theorem being
proved.  `osin24FinitePresentationAddendum_of_tiedRelators` is the forward
assembly from those three source conclusions.  The still-unformalized step is
their proof for Osin's long small-cancellation ties, not the finite-presentation
addendum.

The retired weighted leaves are not imported: they quantify over a different
two-factor setup and are not a theorem of the relative-hyperbolic pair used
here.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open FiniteRelatorQuotient

universe u v w

/-! ## 1.  The three geometric conclusions at a fixed quotient -/

section Conclusions

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {ι : Type w}

/-- The relative-hyperbolicity and peripheral-faithfulness conclusions at one
quotient map.  This is the output used from Osin's Theorem 4.1 and Lemma 4.4.
The finite relator construction below proves neither conjunct. -/
def IsOsin24RelativeQuotientConclusion (Hfam : ι → Subgroup G)
    (eta : G →* Q) : Prop :=
  IsRelativelyHyperbolic Q (fun l => (Hfam l).map eta) ∧
    Set.InjOn eta (⋃ l, (Hfam l : Set G))

/-- The suitability conclusion at one quotient map.  In Osin's proof it comes
after peripheral faithfulness, from preservation of the two cyclic maximal
elementary subgroups and relative almost malnormality. -/
def IsOsin24SuitabilityConclusion (Hfam : ι → Subgroup G) (H : Subgroup G)
    (eta : G →* Q) : Prop :=
  IsSuitableSubgroup (fun l => (Hfam l).map eta) (H.map eta)

/-- The finite-order lifting conclusion at one quotient map.  This is exactly
Lemma 5.1 in the form consumed by Theorem 2.4(5). -/
def IsOsin24TorsionConclusion (eta : G →* Q) : Prop :=
  ∀ q : Q, (∃ n : ℕ, 0 < n ∧ q ^ n = 1) →
    ∃ g : G, (∃ m : ℕ, 0 < m ∧ g ^ m = 1) ∧ eta g = q

/-! ### Identity-map models -/

omit [Group Q] in
/-- The relative quotient conclusion has the identity-map model. -/
theorem isOsin24RelativeQuotientConclusion_id (Hfam : ι → Subgroup G)
    (h : IsRelativelyHyperbolic G Hfam) :
    IsOsin24RelativeQuotientConclusion Hfam (MonoidHom.id G) := by
  refine ⟨?_, ?_⟩
  · simpa only [Subgroup.map_id] using h
  · intro x _ y _ hxy
    exact hxy

omit [Group Q] in
/-- The suitability conclusion has the identity-map model. -/
theorem isOsin24SuitabilityConclusion_id (Hfam : ι → Subgroup G)
    (H : Subgroup G) (h : IsSuitableSubgroup Hfam H) :
    IsOsin24SuitabilityConclusion Hfam H (MonoidHom.id G) := by
  have map_id (K : Subgroup G) : K.map (MonoidHom.id G) = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold IsOsin24SuitabilityConclusion
  rw [map_id H, show (fun l => (Hfam l).map (MonoidHom.id G)) = Hfam by
    funext l
    exact map_id (Hfam l)]
  exact h

omit [Group Q] in
/-- The torsion conclusion has the identity-map model. -/
theorem isOsin24TorsionConclusion_id :
    IsOsin24TorsionConclusion (MonoidHom.id G) := by
  intro q hq
  exact ⟨q, hq, rfl⟩

end Conclusions

/-! ## 2.  One literal relation per prescribed element -/

section TiedQuotients

variable {G : Type} [Group G] {ι : Type}

/-- The quotient map for the finite family of ties indexed by `t`.  The target
is definitionally the quotient by the normal closure of the displayed tied
relators, so finite normal generation below is a theorem about this quotient
itself. -/
abbrev osin24TiedQuotientMap (H : Subgroup G) (t : Finset G)
    (route : TieChoice H t) :
    G →* FiniteRelatorQuotient.Quotient (tiedRelators H t route) :=
  quotientMap (tiedRelators H t route)

/-- The map in the literal construction is surjective. -/
theorem osin24TiedQuotientMap_surjective (H : Subgroup G) (t : Finset G)
    (route : TieChoice H t) :
    Function.Surjective (osin24TiedQuotientMap H t route) :=
  quotientMap_surjective _

/-- The relation indexed by `x` sends `x` to its chosen element of `H`.  This
is Osin's Theorem 2.4(2), before any diagram argument. -/
theorem osin24TiedQuotientMap_mem_image (H : Subgroup G) (t : Finset G)
    (route : TieChoice H t) (x : {x : G // x ∈ t}) :
    osin24TiedQuotientMap H t route (x : G) ∈
      H.map (osin24TiedQuotientMap H t route) :=
  quotientMap_tied_mem_map H t route x

/-- The kernel of the literal tied quotient is finitely normally generated.
The generating set is the finite set of values of the ties, so this is the
finite-presentation addendum read from Osin's proof. -/
theorem osin24TiedQuotientMap_ker_isFinitelyNormallyGenerated
    (H : Subgroup G) (t : Finset G) (route : TieChoice H t) :
    (osin24TiedQuotientMap H t route).ker.IsFinitelyNormallyGenerated :=
  tiedQuotient_ker_isFinitelyNormallyGenerated H t route

/-! ## 3.  Forward assembly at the actual quotient -/

/-- The five stated clauses of Osin's Theorem 2.4 for the literal finite tied
quotient, from the three geometric source conclusions at that quotient.

Surjectivity and the prescribed-element clause are theorems of the construction.
The remaining clauses are exactly the three named source conclusions of section
1. -/
theorem isOsin24Quotient_of_tiedRelators (Hfam : ι → Subgroup G)
    (H : Subgroup G) (t : Finset G) (route : TieChoice H t)
    (hrelative : IsOsin24RelativeQuotientConclusion Hfam
      (osin24TiedQuotientMap H t route))
    (hsuitable : IsOsin24SuitabilityConclusion Hfam H
      (osin24TiedQuotientMap H t route))
    (htorsion : IsOsin24TorsionConclusion (osin24TiedQuotientMap H t route)) :
    IsOsin24Quotient Hfam H (t : Set G)
      (FiniteRelatorQuotient.Quotient (tiedRelators H t route))
      (osin24TiedQuotientMap H t route) := by
  obtain ⟨hrelHyp, hinjective⟩ := hrelative
  refine ⟨osin24TiedQuotientMap_surjective H t route, hrelHyp, ?_,
    hinjective, hsuitable, htorsion⟩
  intro x hx
  exact osin24TiedQuotientMap_mem_image H t route ⟨x, hx⟩

/-- **Osin Theorem 2.4 with the finite-presentation addendum, at a literal
finite family of ties.**  The quotient is not postulated: it is
`G ⧸ ⟪{t_i h_i⁻¹}⟫`, and its kernel finite normal generation follows from that
definition. -/
theorem osin24FinitePresentationAddendum_of_tiedRelators
    (Hfam : ι → Subgroup G) (H : Subgroup G) (t : Finset G)
    (route : TieChoice H t)
    (hrelative : IsOsin24RelativeQuotientConclusion Hfam
      (osin24TiedQuotientMap H t route))
    (hsuitable : IsOsin24SuitabilityConclusion Hfam H
      (osin24TiedQuotientMap H t route))
    (htorsion : IsOsin24TorsionConclusion (osin24TiedQuotientMap H t route)) :
    IsOsin24Quotient Hfam H (t : Set G)
        (FiniteRelatorQuotient.Quotient (tiedRelators H t route))
        (osin24TiedQuotientMap H t route) ∧
      (MonoidHom.ker (osin24TiedQuotientMap H t route)).IsFinitelyNormallyGenerated :=
  ⟨isOsin24Quotient_of_tiedRelators Hfam H t route hrelative hsuitable htorsion,
    osin24TiedQuotientMap_ker_isFinitelyNormallyGenerated H t route⟩

/-! ## 4.  Passing from a finite set to its finite enumeration -/

/-- A finite prescribed set can be fed to the literal construction through its
canonical finset.  This lemma is only the set/finset bridge; choosing `route`
and proving the three geometric conclusions remain the source-theorem work. -/
theorem osin24FinitePresentationAddendum_of_tiedRelators_toFinset
    (Hfam : ι → Subgroup G) (H : Subgroup G) (t : Set G) (ht : t.Finite)
    (route : TieChoice H ht.toFinset)
    (hrelative : IsOsin24RelativeQuotientConclusion Hfam
      (osin24TiedQuotientMap H ht.toFinset route))
    (hsuitable : IsOsin24SuitabilityConclusion Hfam H
      (osin24TiedQuotientMap H ht.toFinset route))
    (htorsion : IsOsin24TorsionConclusion
      (osin24TiedQuotientMap H ht.toFinset route)) :
    ∃ (Q : Type) (_ : Group Q) (eta : G →* Q),
      IsOsin24Quotient Hfam H t Q eta ∧ eta.ker.IsFinitelyNormallyGenerated := by
  refine ⟨FiniteRelatorQuotient.Quotient (tiedRelators H ht.toFinset route), inferInstance,
    osin24TiedQuotientMap H ht.toFinset route, ?_⟩
  have hmain := osin24FinitePresentationAddendum_of_tiedRelators Hfam H
    ht.toFinset route hrelative hsuitable htorsion
  simpa only [Set.Finite.coe_toFinset] using hmain

end TiedQuotients

end RelHyp
end GGT
end GroupApproximation
