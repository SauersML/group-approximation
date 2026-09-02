import GroupApproximation.GGT.DGOProposition435
import GroupApproximation.GGT.HullSCLemma44FamilyInclusionStatement
import GroupApproximation.GGT.HullSCFillingSelectionTheorem316

/-!
# The joint peripheral family of Hull's Lemma 4.4, from Proposition 4.35

`HullSC.JointAuxiliaryPeripheralEmbedding` is the input the repaired Lemma 4.4
statement binds: for a selected auxiliary family and an original hyperbolically
embedded family, a *joint* hyperbolically embedded family over the sum index.
This module derives it from the transitivity statement
`GGT.RelHyp.DGOProposition435Statement`, and says exactly which extra data the
derivation needs.

## Two alphabet conditions, and why neither can be dropped

`DGOProposition435Statement` combines `D` and `E` under the base equation
`E.base = D.alphabet.carrier`.  The filling lane offers two inclusions instead:

* `AuxiliaryPeripheralFamily.base_le` gives only
  `A.alphabet.carrier ⊆ selected.rel.base`, because `adjoinPair` adds the
  target letters and Osin's Theorem 5.4 then enlarges the base further.  The
  cure is to build the joint family from the family *before* those two steps,
  which is what `HullSC.SimultaneousAuxiliaryPeripheralSelectionAtHullAlphabet`
  produces: it cones off Hull's alphabet itself, so its base is
  `A.alphabet.carrier` on the nose.  `adjoinPair` and Theorem 5.4 keep the
  cores, and the joint conclusion mentions only the cores, so nothing is lost.
* `RelativeHullContinuationData.rel_alphabet_subset` gives only
  `rel.alphabet.carrier ⊆ hull.alphabet.carrier`.  Here there is no cure
  inside this file: `GGT.RelHyp.not_isHyperbolicallyEmbedded_of_base_splits`
  shows that a strictly larger base can destroy local finiteness of the
  original family, and Corollary 4.27 repairs only finite enlargements.  So
  the equality `original.alphabet.carrier = A.alphabet.carrier` is carried as
  a hypothesis, and it is exactly what `RelativeHullData` (the first filling
  step) supplies and `RelativeHullContinuationData` does not.

`JointAuxiliaryPeripheralEmbeddingAtHullAlphabet` is
`HullSC.JointAuxiliaryPeripheralEmbedding` with those two conditions written
in; `jointAuxiliaryPeripheralEmbeddingAtHullAlphabet_of_dgoProposition435`
proves it, and `jointAuxiliaryPeripheralEmbedding_of_atHullAlphabet` records
that the two Props differ by nothing else.

## The symmetric base

Both joint interfaces ask the joint base to be closed under inversion, and a
`GGT.RelGenSet` carries symmetry only for its whole alphabet.  A relative base
that is *finite* — which is what `RelativeHullContinuationData.base_finite`
gives — can always be symmetrised without changing the alphabet, by
`GGT.OsinComponents.exists_symmetric_base_of_base_finite`.  That is the
general-family companion of `exists_symmetric_base'`, which needs `Λ` finite
for the same step.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **A finite relative base can be symmetrised**, at a general family.

`exists_symmetric_base'` needs `[Finite Λ]` at exactly one step: the letters
`x ∈ X` with `x⁻¹ ∉ X` lie in `X ∩ H_λ` for some `λ`, each such intersection
is finite, and their union is finite only when there are finitely many of
them.  A finite base makes that step trivial, with no hypothesis on `Λ`. -/
theorem exists_symmetric_base_of_base_finite (D : RelGenSet G Λ)
    (hfin : D.base.Finite) (hemb : D.IsHyperbolicallyEmbedded) :
    ∃ D' : RelGenSet G Λ, D.base ⊆ D'.base ∧ D'.fam = D.fam ∧
      (∀ x ∈ D'.base, x⁻¹ ∈ D'.base) ∧ D'.IsHyperbolicallyEmbedded ∧
        D'.alphabet = D.alphabet := by
  have hsub : D.base ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))
      ⊆ {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ∪
        (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := by
    rintro y (hy | hy)
    · exact Or.inl (Or.inl hy)
    · exact Or.inr hy
  have hgen : IsSymmetricGeneratingSet
      ({x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base} ∪
        (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G))) := by
    constructor
    · rintro y (hy | hy)
      · rcases hy with hy | hy
        · refine Or.inl (Or.inr ?_)
          rwa [inv_inv]
        · exact Or.inl (Or.inl hy)
      · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hy
        have hlam' : y ∈ D.fam lam := hlam
        exact Or.inr (Set.mem_iUnion.mpr ⟨lam, inv_mem hlam'⟩)
    · have hmono := Subgroup.closure_mono hsub
      rw [D.symmetricGenerating.closure_eq] at hmono
      exact top_le_iff.mp hmono
  have hN : ∀ x ∈ {x : G | x ∉ D.base ∧ x⁻¹ ∈ D.base},
      ∃ mu : Λ, x ∈ D.fam mu := by
    rintro x ⟨hxn, hxi⟩
    have hxinvA : x⁻¹ ∈ D.alphabet.carrier := Set.mem_union_left _ hxi
    have hxA : x ∈ D.base ∪ (⋃ lam : Λ, ((D.fam lam : Subgroup G) : Set G)) := by
      have hstep := D.symmetricGenerating.inv_mem x⁻¹ hxinvA
      rwa [inv_inv] at hstep
    rcases hxA with hb | hf
    · exact absurd hb hxn
    · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hf
      exact ⟨lam, hlam⟩
  have hNfin : {x : G | x ∉ D.base ∧ x⁻¹ ∈ D.base}.Finite := by
    refine (hfin.image (fun y : G => y⁻¹)).subset ?_
    rintro x ⟨-, hxi⟩
    exact ⟨x⁻¹, hxi, inv_inv x⟩
  have hbase' : {x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}
      ⊆ D.base ∪ {x : G | x ∉ D.base ∧ x⁻¹ ∈ D.base} := by
    intro x hx
    by_cases hxb : x ∈ D.base
    · exact Or.inl hxb
    · rcases hx with hx | hx
      · exact absurd hx hxb
      · exact Or.inr ⟨hxb, hx⟩
  have halph : (⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ :
      RelGenSet G Λ).alphabet = D.alphabet :=
    alphabet_eq_of_carrier_eq
      (alphabet_eq_of_symmetrizedBase' D
        ⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ rfl rfl)
  have htransport : ∀ P Q : Alphabet G, P = Q →
      (∃ delta : ℝ, IsHyperbolicSpace delta (Cayley Q)) →
        ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley P) := by
    intro P Q hPQ hQ
    subst hPQ
    exact hQ
  have hembD' : (⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ :
      RelGenSet G Λ).IsHyperbolicallyEmbedded := by
    constructor
    · exact htransport _ _ halph hemb.hyperbolic
    · intro lam n
      exact relBall_finite_of_base_subset' D
        ⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩ lam rfl hN hNfin
        hbase' (fun m => hemb.locallyFinite lam m) n
  refine ⟨⟨{x : G | x ∈ D.base ∨ x⁻¹ ∈ D.base}, D.fam, hgen⟩,
    ?_, rfl, ?_, hembD', halph⟩
  · intro y hy
    exact Or.inl hy
  · intro y hy
    rcases hy with hy | hy
    · refine Or.inr ?_
      rwa [inv_inv]
    · exact Or.inl hy

end OsinComponents
end GGT

namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The joint family, from the transitivity statement -/

/-- **The joint hyperbolically embedded family**, from Proposition 4.35's
joint direction.

`E` is the auxiliary family coned off over Hull's alphabet, `original` is the
relatively hyperbolic peripheral family over the same alphabet, and the joint
family is their labelled sum over the symmetrised original base.  Its base is
inversion-closed, it restricts to the two given families, and it is
hyperbolically embedded. -/
theorem exists_joint_of_dgoProposition435
    (h435 : GGT.RelHyp.DGOProposition435Statement.{u, w, 0})
    {G : Type u} [Group G] {k : ℕ}
    (E : GGT.RelGenSet G (AuxiliaryPeripheralIndex k))
    (hEemb : E.IsHyperbolicallyEmbedded)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (halph : E.base = original.alphabet.carrier)
    (hfin : original.base.Finite)
    (horig : original.IsHyperbolicallyEmbedded) :
    ∃ joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)),
      (∀ x ∈ joint.base, x⁻¹ ∈ joint.base) ∧
        (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) ∧
          (∀ i : AuxiliaryPeripheralIndex k,
            joint.fam (Sum.inr i) = E.fam i) ∧
            joint.IsHyperbolicallyEmbedded := by
  obtain ⟨D', -, hfam', hinv', hemb', halph'⟩ :=
    GGT.OsinComponents.exists_symmetric_base_of_base_finite original hfin horig
  have hbase : E.base = D'.alphabet.carrier := by
    rw [halph, halph']
  refine ⟨GGT.RelHyp.combinedRelGenSet D' E, hinv', ?_, fun _ => rfl,
    h435 D' E hbase hemb' hEemb⟩
  intro lam
  show D'.fam lam = original.fam lam
  rw [hfam']

/-! ## The repaired joint-selection input -/

/-- **The joint-selection input with both alphabet conditions written in.**

This is `JointAuxiliaryPeripheralEmbedding` with the two facts the derivation
needs and the current statement omits: the original relative alphabet *is*
Hull's alphabet, and the original relative base is finite.  The auxiliary
family is supplied at Hull's alphabet, before the target letters are adjoined
and before Osin's Theorem 5.4 enlarges the base; its cores are the ones the
conclusion talks about. -/
def JointAuxiliaryPeripheralEmbeddingAtHullAlphabet : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S),
      selected.rel.base = A.alphabet.carrier →
      ∀ {Lambda : Type w} (original : GGT.RelGenSet G Lambda),
        original.alphabet.carrier = A.alphabet.carrier →
        original.base.Finite →
        original.IsHyperbolicallyEmbedded →
          ∃ joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)),
            (∀ x ∈ joint.base, x⁻¹ ∈ joint.base) ∧
              (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) ∧
                (∀ i : AuxiliaryPeripheralIndex k,
                  joint.fam (Sum.inr i) = selected.cores.peripheral i) ∧
                  joint.IsHyperbolicallyEmbedded

/-- **Proposition 4.35's joint direction gives the repaired input.** -/
theorem jointAuxiliaryPeripheralEmbeddingAtHullAlphabet_of_dgoProposition435
    (h435 : GGT.RelHyp.DGOProposition435Statement.{u, w, 0}) :
    JointAuxiliaryPeripheralEmbeddingAtHullAlphabet.{u, w} := by
  intro G _ A N k S selected hselbase Lambda original halph hfin horig
  obtain ⟨joint, hinv, horiginal, hsel, hemb⟩ :=
    exists_joint_of_dgoProposition435 h435 selected.rel selected.embedded
      original (by rw [hselbase, halph]) hfin horig
  refine ⟨joint, hinv, horiginal, ?_, hemb⟩
  intro i
  rw [hsel i, selected.fam_eq i]

/-- **The two joint-selection inputs differ only by the alphabet
conditions.**  Adding them back is what makes the leaf flip work. -/
theorem jointAuxiliaryPeripheralEmbedding_of_atHullAlphabet
    (h : JointAuxiliaryPeripheralEmbeddingAtHullAlphabet.{u, w})
    {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    (hselbase : selected.rel.base = A.alphabet.carrier)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (halph : original.alphabet.carrier = A.alphabet.carrier)
    (hfin : original.base.Finite)
    (horig : original.IsHyperbolicallyEmbedded) :
    ∃ joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)),
      (∀ x ∈ joint.base, x⁻¹ ∈ joint.base) ∧
        (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) ∧
          (∀ i : AuxiliaryPeripheralIndex k,
            joint.fam (Sum.inr i) = selected.cores.peripheral i) ∧
            joint.IsHyperbolicallyEmbedded :=
  h selected hselbase original halph hfin horig

/-! ## The joint family from the landed selection producer -/

/-- **The joint family, with only Proposition 4.35 and Hull's `yi` statement
as inputs.**

The finite-family `yi` statement and the proved Theorem 3.16 assembly build the
auxiliary family by coning off Hull's alphabet itself, so its base is
`A.alphabet.carrier` on the nose.  With the original relative alphabet equal to
that alphabet, Proposition 4.35's joint direction then gives the joint family
with no further input, and it is the family Hull's repaired Lemma 4.4 binds. -/
theorem exists_joint_of_finiteYi_of_dgoProposition435
    (hyi : YiSuitableFiniteFamily.{u})
    (h435 : GGT.RelHyp.DGOProposition435Statement.{u, w, 0})
    {G : Type u} [Group G] (A : HullGeneratingSet G) {N : Subgroup G}
    {k : ℕ} (S : Fin k → Subgroup G) (hN : Suitable A.alphabet N)
    (hS : ∀ j : Fin k, Suitable A.alphabet (S j))
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (halph : original.alphabet.carrier = A.alphabet.carrier)
    (hfin : original.base.Finite)
    (horig : original.IsHyperbolicallyEmbedded) :
    ∃ (selected : AuxiliaryPeripheralFamily A N S)
      (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k))),
      (∀ x ∈ joint.base, x⁻¹ ∈ joint.base) ∧
        (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) ∧
          (∀ i : AuxiliaryPeripheralIndex k,
            joint.fam (Sum.inr i) = selected.cores.peripheral i) ∧
            joint.IsHyperbolicallyEmbedded := by
  obtain ⟨selected, hselbase⟩ :=
    simultaneousAuxiliaryPeripheralSelectionAtHullAlphabet_of_finiteYi_theorem316
      hyi A S hN hS
  obtain ⟨joint, hinv, horiginal, hsel, hemb⟩ :=
    exists_joint_of_dgoProposition435 h435 selected.rel selected.embedded
      original (by rw [hselbase, halph]) hfin horig
  refine ⟨selected, joint, hinv, horiginal, ?_, hemb⟩
  intro i
  rw [hsel i, selected.fam_eq i]

end HullSC
end GroupApproximation
