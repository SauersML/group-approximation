import GroupApproximation.GGT.HullSCLemma44RespellingBinders
import GroupApproximation.GGT.HullSCLemma44OriginalExpansion
import GroupApproximation.Meta.AxiomGuard

/-!
# Hull's §6 re-spelling at one relator, from the residual metric estimate

`GGT/HullSCLemma44RespellingBinders.lean` discharges the joint half of the
re-spelling leaf and leaves `OriginalRelatorRespellingStatement` as the only
input.  That statement is still asked for **every** relator family `W` meeting
the thresholds, and the machinery below it is not: `OriginalRelatorExpansion`
(`GGT/HullSCLemma44OriginalExpansion.lean`) is stated for **one** word, and
`relatorRespellingAt_original_of_expansion` produces the original half for
`RelWord.symmetrized v` alone.

Hull's construction produces one relator.  `HullSC.AuxiliaryPeripheralFamily`'s
`exists_auxiliaryRelatorOfBaseLetterPublished_exact` chooses a single word `v`
after every constant is fixed, and the family fed to Lemma 4.4 is
`RelWord.symmetrized v`.  So this file states the leaf at that generality and
proves it from the residual estimate — which by
`OriginalRelatorExpansion.ofSpelling` is **four metric clauses for a single word
over the original relative alphabet**: depth, the two piece bounds, and the
quasi-geodesic chain.  Symmetrization, strong boundedness, admissibility, length
and the agreement of the normal closures are all discharged already.

## The chain, and which way each link points

`HullRelatorRespellingStatement` (the leaf, `HullSCLemma44FamilyAssembly`)
  ⟹ `HullRelatorRespellingBaseCompatibleStatement` (`HullSCLemma44RespellingBinders`)
  ⟹ `HullRelatorRespellingOneRelatorStatement` (here)
  ⟸ `OriginalRelatorExpansionStatement` (here).

Both implications are **narrowings**, proved here and in the previous file
rather than asserted, so nobody reads the chain as a strengthening.  What the
narrowing buys is that the residue is now a statement whose only content is
metric and whose only object is one word: no quotient, no diagram, no
isoperimetric inequality, no second peripheral family.

`GGT/HullSCLemma44OriginalExpansion.lean` was unwired — nothing applied
`ofSpelling`, `canonical` or `relatorRespellingAt_original_of_expansion`, as its
own neighbouring header records.  This file is what applies it.

## What is still missing at the top

Three clauses separate `HullRelatorRespellingOneRelatorStatement` from the leaf
as `TheoremCAssembly` consumes it, and all three are properties of Hull's
construction rather than open mathematics:

* `joint.base ⊆ selected.rel.base` — one word in the family form's binder, by
  `jointBase_subset_selectedBase_of_baseAdjoined`;
* the relator family is `RelWord.symmetrized v` for a single `v`;
* the base letters of `v` lie in `joint.base` — for Hull's relator that is
  `t⁻¹ ∈ joint.base`, since `t⁻¹` is its only base letter.

The inverse-closure of `joint.base` used below to lift the third clause to the
symmetrized family is already a binder of
`HullLemma44CanonicalQuotientFamilyInclusionJointStatement`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## Base letters survive symmetrization -/

/-- **`baseLetters_symmetrized_mem` without the single-letter hypothesis.**

The published form asks that every base letter of the relator be one fixed
element `t⁻¹`, which is what Hull's §6 relator satisfies.  Nothing in the proof
uses that: an inverse-closed set containing all the relator's base letters
contains all the base letters of its symmetrized closure. -/
theorem baseLetters_symmetrized_mem_of_baseLetters {G : Type u} [Group G]
    {Lambda : Type w} (R : List (GGT.RelLetter G Lambda)) (B : Set G)
    (hbase : ∀ x : G, GGT.RelLetter.base x ∈ R → x ∈ B)
    (hinv : ∀ x ∈ B, x⁻¹ ∈ B) :
    ∀ v ∈ RelWord.symmetrized R, ∀ x : G,
      GGT.RelLetter.base x ∈ v → x ∈ B := by
  intro v hv x hx
  rcases RelWord.Sym.letters (RelWord.mem_symmetrized.mp hv)
      (GGT.RelLetter.base x) hx with hmem | hmem
  · exact hbase x hmem
  · have hmem' : GGT.RelLetter.base x⁻¹ ∈ R := hmem
    have hinvB := hinv _ (hbase _ hmem')
    rwa [inv_inv] at hinvB

/-! ## The leaf at one relator -/

/-- **Hull's §6 re-spelling for a single relator.**

`HullRelatorRespellingBaseCompatibleStatement` with the relator family taken to
be the symmetrized closure of one word, which is the family Hull's construction
feeds to Lemma 4.4.  The side condition is now a condition on that one word.

The inverse-closure clause on `joint.base` is a binder of
`HullLemma44CanonicalQuotientFamilyInclusionJointStatement` already; it is what
lifts the side condition from `v` to `RelWord.symmetrized v`. -/
def HullRelatorRespellingOneRelatorStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k))),
    original.alphabet.carrier ⊆ A.alphabet.carrier →
    original.IsHyperbolicallyEmbedded →
    joint.IsHyperbolicallyEmbedded →
    joint.base ⊆ selected.rel.base →
    (∀ x ∈ joint.base, x⁻¹ ∈ joint.base) →
    (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) →
    (∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i) →
    ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 1000 →
      ∀ eps0 rho0 : ℕ,
        ∃ eps rho : ℕ,
          ∀ v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)),
            (∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base) →
            RelWord.IsLemma44Input selected.rel (RelWord.symmetrized v)
                eps mu rho →
              RelatorRespellingAt original (RelWord.symmetrized v)
                  eps0 rho0 mu ∧
                RelatorRespellingAt joint (RelWord.symmetrized v)
                  eps0 rho0 mu

/-- **The one-relator form is the weaker one.**  Recorded as a proof, so that
the chain of narrowings is visible and nothing below is mistaken for a
strengthening of the leaf. -/
theorem hullRelatorRespellingOneRelatorStatement_of_baseCompatible
    (h : HullRelatorRespellingBaseCompatibleStatement.{u, w}) :
    HullRelatorRespellingOneRelatorStatement.{u, w} := by
  intro G _ A N k S selected Lambda original joint hA horiginal hjoint hbaseSub
    hjointInv hinl hinr mu hmu hmuUpper eps0 rho0
  obtain ⟨eps, rho, hres⟩ :=
    h selected original joint hA horiginal hjoint hbaseSub hinl hinr mu hmu
      hmuUpper eps0 rho0
  refine ⟨eps, rho, ?_⟩
  intro v hvbase hsc
  exact hres (RelWord.symmetrized v)
    (baseLetters_symmetrized_mem_of_baseLetters v joint.base hvbase hjointInv)
    hsc

/-! ## The residual metric estimate -/

/-- **What the original half of the re-spelling costs, for one relator.**

For thresholds `eps0`, `rho0` prescribed in advance there are source thresholds
such that every relator meeting them expands over the original relative alphabet
with target parameters above the prescribed ones.  `OriginalRelatorExpansion`
carries four metric clauses and nothing else — depth, the two piece bounds and
the quasi-geodesic chain — because `ofSpelling` discharges the expansion's
legality, value and length from any spelling of the selected letters, and
`isLemma44Input` and `normalClosure_eq` discharge the symmetrization and the
normal-closure bookkeeping.

The `20 * (eps + 1) ≤ rho` clause is `RelatorRespellingAt`'s own and is asked
here so that the estimate can be handed to it unchanged. -/
def OriginalRelatorExpansionStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda),
    original.IsHyperbolicallyEmbedded →
    original.alphabet.carrier ⊆ A.alphabet.carrier →
    ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 1000 →
      ∀ eps0 rho0 : ℕ,
        ∃ epsS rhoS : ℕ,
          ∀ v : List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)),
            RelWord.IsLemma44Input selected.rel (RelWord.symmetrized v)
                epsS mu rhoS →
              ∃ eps rho : ℕ, eps0 ≤ eps ∧ rho0 ≤ rho ∧
                20 * (eps + 1) ≤ rho ∧
                Nonempty (OriginalRelatorExpansion original v eps rho mu)

/-- **The re-spelling leaf at Hull's generality, from the metric estimate
alone.**

Both halves are discharged: the joint one by the index relabelling of
`HullSCLemma44RespellingBinders`, the original one by the expansion.  Nothing
else is assumed — no quotient, no reduced diagram, no isoperimetric inequality.

The thresholds are merged as everywhere else in this chain: the source
thresholds are raised to `max eps0 epsS` and a `rho` large enough to carry both
`rho0`, `rhoS` and `RelatorRespellingAt`'s `20 * (eps + 1)` clause, and the
input is monotonicity-lowered back to `(epsS, rhoS)` before the estimate is
applied. -/
theorem hullRelatorRespellingOneRelatorStatement_of_expansion
    (h : OriginalRelatorExpansionStatement.{u, w}) :
    HullRelatorRespellingOneRelatorStatement.{u, w} := by
  intro G _ A N k S selected Lambda original joint hA horiginal _hjoint hbaseSub
    hjointInv hinl hinr mu hmu hmuUpper eps0 rho0
  obtain ⟨epsS, rhoS, hE⟩ :=
    h selected original horiginal hA mu hmu hmuUpper eps0 rho0
  refine ⟨max eps0 epsS,
    max (max rho0 rhoS) (20 * (max eps0 epsS + 1)), ?_⟩
  intro v hvbase hsc
  have hepsS : epsS ≤ max eps0 epsS := Nat.le_max_right _ _
  have hrhoS : rhoS ≤ max (max rho0 rhoS) (20 * (max eps0 epsS + 1)) :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  obtain ⟨eps, rho, heps, hrho, h20, hE'⟩ :=
    hE v (hsc.mono_parameters hepsS le_rfl hrhoS)
  obtain ⟨E⟩ := hE'
  refine ⟨relatorRespellingAt_original_of_expansion E heps hrho h20, ?_⟩
  exact relatorRespellingAt_joint_of_familyBinders selected original joint hA
    hbaseSub hinl hinr (Nat.le_max_left _ _)
    (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
    (Nat.le_max_right _ _)
    (baseLetters_symmetrized_mem_of_baseLetters v joint.base hvbase hjointInv)
    hsc

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.baseLetters_symmetrized_mem_of_baseLetters
#audit_axioms GroupApproximation.HullSC.hullRelatorRespellingOneRelatorStatement_of_baseCompatible
#audit_axioms GroupApproximation.HullSC.hullRelatorRespellingOneRelatorStatement_of_expansion
