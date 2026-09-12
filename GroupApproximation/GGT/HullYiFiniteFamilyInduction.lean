import GroupApproximation.GGT.HullSCFillingNonElementary

/-!
# Hull's finite-family `yi` theorem is a local finite-avoidance theorem

Hull's Corollary 5.7 is stated for an arbitrary finite number of witnesses.
For the simultaneous filling construction, however, the useful induction step
is local: inside one suitable subgroup choose two witnesses which avoid all
commensurability classes represented by a prescribed finite set.

`HullSCFillingNonElementary` proves the forward implication.  A family of
`|F| + 2` witnesses contains two classes outside `F`, by finite counting.  This
file proves the converse.  Iterate the local step over the constant family of
`m` copies of the same suitable subgroup, then retain the `false` member of
each chosen pair.  Pairwise non-commensurability of the larger flattened family
passes immediately to this subfamily.

Thus the manuscript's all-`m` statement has exactly one local proof boundary;
there is no additional infinitary choice or simultaneous-selection theorem
hidden in its quantifier.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-- The one-sided form of finite commensurability avoidance.  The reverse
orientation is automatic because `AreCommensurable` is symmetric. -/
def AvoidsFiniteCommensurabilityOneSided {G : Type u} [Group G]
    (F : Finset G) (a : G) : Prop :=
  ∀ x ∈ F, ¬ AreCommensurable a x

/-- One-sided and two-sided finite avoidance are equivalent.  Keeping this
lemma explicit means the geometric producer only has to exclude one orientation
of the conjugate-power equation. -/
theorem avoidsFiniteCommensurability_iff_oneSided
    {G : Type u} [Group G] {F : Finset G} {a : G} :
    AvoidsFiniteCommensurability F a ↔
      AvoidsFiniteCommensurabilityOneSided F a := by
  constructor
  · intro h x hx
    exact (h x hx).1
  · intro h x hx
    refine ⟨h x hx, ?_⟩
    intro hxa
    exact h x hx (areCommensurable_symm hxa)

/-- The minimal local producer: choose a cyclic Yi pair for one suitable
subgroup, with each member avoiding the commensurability classes represented
by a prescribed finite set.  Only one orientation of commensurability is
requested; symmetry supplies the other one. -/
def YiSuitablePairAvoidingFiniteOneSided : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) {T : Subgroup G},
    Suitable A.alphabet T → ∀ F : Finset G,
      ∃ g : Bool → G, (∀ b, g b ∈ T) ∧
        (∀ b, IsLoxodromic (g b) (Cayley.base A.alphabet)) ∧
        PairwiseNonCommensurable g ∧
        (∀ b, GGT.Elementary.elementaryClosure (g b) =
          Subgroup.zpowers (g b)) ∧
        ∀ b, AvoidsFiniteCommensurabilityOneSided F (g b)

/-- The one-sided local producer gives the existing two-sided induction step. -/
theorem yiSuitablePairAvoidingFinite_of_oneSided
    (hstep : YiSuitablePairAvoidingFiniteOneSided.{u}) :
    YiSuitablePairAvoidingFinite.{u} := by
  intro G _ A T hT F
  obtain ⟨g, hgT, hglox, hgnc, hgcyc, hgavoid⟩ := hstep A hT F
  exact ⟨g, hgT, hglox, hgnc, hgcyc,
    fun b => avoidsFiniteCommensurability_iff_oneSided.mpr (hgavoid b)⟩

/-- The existing two-sided local step trivially gives the one-sided form. -/
theorem yiSuitablePairAvoidingFiniteOneSided_of_twoSided
    (hstep : YiSuitablePairAvoidingFinite.{u}) :
    YiSuitablePairAvoidingFiniteOneSided.{u} := by
  intro G _ A T hT F
  obtain ⟨g, hgT, hglox, hgnc, hgcyc, hgavoid⟩ := hstep A hT F
  exact ⟨g, hgT, hglox, hgnc, hgcyc,
    fun b => avoidsFiniteCommensurability_iff_oneSided.mp (hgavoid b)⟩

/-- A local Yi pair avoiding every prescribed finite set produces Hull's
printed all-`m` finite-family theorem.

The induction itself is already available as
`exists_yiSuitablePairs_fin_of_avoiding`.  Applying it to `m` constant copies
of `T` gives `2m` jointly non-commensurable witnesses; selecting one member of
each pair gives the required `m` witnesses. -/
theorem yiSuitableFiniteFamily_of_pairAvoidingFinite
    (hstep : YiSuitablePairAvoidingFinite.{u}) :
    YiSuitableFiniteFamily.{u} := by
  intro G _ A T hT m
  let targets : Fin m → Subgroup G := fun _ => T
  obtain ⟨pairs, hpairsT, hpairsLox, hpairsNc, hpairsCyc⟩ :=
    exists_yiSuitablePairs_fin_of_avoiding hstep A m targets (fun _ => hT)
  let g : Fin m → G := fun i => pairs (i, false)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hpairsT (i, false)
  · intro i
    exact hpairsLox (i, false)
  · intro i j hij p q hp hq t
    have hij' : (i, false) ≠ (j, false) := by
      intro heq
      exact hij (congrArg Prod.fst heq)
    exact hpairsNc (i, false) (j, false) hij' p q hp hq t
  · intro i
    exact hpairsCyc (i, false)

/-- Hull's all-`m` finite-family statement is equivalent to its local
finite-avoidance form.

The forward direction uses the proved finite counting lemma: among `|F| + 2`
pairwise non-commensurable candidates, at least two avoid every class
represented in `F`.  The reverse direction is the finite induction above. -/
theorem yiSuitableFiniteFamily_iff_pairAvoidingFinite :
    YiSuitableFiniteFamily.{u} ↔ YiSuitablePairAvoidingFinite.{u} := by
  constructor
  · intro hyi
    exact yiSuitablePairAvoidingFinite_of_family_of_avoidance hyi
      finiteCommensurabilityAvoidance
  · exact yiSuitableFiniteFamily_of_pairAvoidingFinite

/-- Final sharp reduction: Hull's all-`m` finite-family theorem is equivalent
to producing one cyclic pair avoiding a finite list, and the producer need
exclude only one orientation of commensurability. -/
theorem yiSuitableFiniteFamily_iff_pairAvoidingFiniteOneSided :
    YiSuitableFiniteFamily.{u} ↔
      YiSuitablePairAvoidingFiniteOneSided.{u} := by
  rw [yiSuitableFiniteFamily_iff_pairAvoidingFinite]
  constructor
  · exact yiSuitablePairAvoidingFiniteOneSided_of_twoSided
  · exact yiSuitablePairAvoidingFinite_of_oneSided

end HullSC
end GroupApproximation
