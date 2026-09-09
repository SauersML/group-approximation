import GroupApproximation.GGT.HullSCLemma44JointRelabel
import GroupApproximation.Meta.AxiomGuard

/-!
# The joint half of Hull's §6 re-spelling, from the family form's own binders

`HullSC.HullRelatorRespellingStatement` (`GGT/HullSCLemma44FamilyAssembly.lean`)
is one of the four open leaves of `Manuscript/NonMF/TheoremCAssembly.lean`.  Its
joint half is a relabelling and `jointRelatorRespellingStatement_proved`
discharges it — but at **four structural hypotheses and one side condition on
the relator family** that the leaf itself does not carry, which is why proving
`OriginalRelatorRespellingStatement` alone would not close the leaf.

This file measures that gap exactly.  Of the six obligations of
`relatorRespellingAt_joint`, **four are theorems of the leaf's own binders** and
are proved here:

* `famInr_eq_selectedFam` — `hfamInr`, from the leaf's `joint.fam (Sum.inr i) =
  selected.cores.peripheral i` together with `AuxiliaryPeripheralFamily.fam_eq`;
* `famInl_mem_selectedBase` — `hfamInl`, from the leaf's `joint.fam (Sum.inl
  lam) = original.fam lam`, `RelGenSet.fam_subset_alphabet`, the leaf's
  `original.alphabet.carrier ⊆ A.alphabet.carrier` and
  `AuxiliaryPeripheralFamily.base_le`;
* `jointAlphabet_subset_selectedAlphabet` — `halphabet`, from `hbaseSub` and the
  two above;
* `baseLetters_mem_jointBase_of_baseSubset` — the side condition on `W`, from
  the reverse base containment `selected.rel.base ⊆ joint.base`.

**Two are not.**  `joint.base ⊆ selected.rel.base` is one word away: the family
form binds `∃ T, T.Finite ∧ T ⊆ selected.rel.alphabet.carrier ∧ joint.base ⊆
original.base ∪ T`, and `jointBase_subset_selectedBase_of_baseAdjoined`
(`GGT/HullSCLemma44QuasiGeodesicBridge.lean`) closes it as soon as `T` is asked
to land in the base rather than the alphabet.  The side condition on `W` is
further away, and it is the one that matters.

## The side condition is where the leaf is over-general

`RelWord.IsLemma44Input selected.rel W eps mu rho` says nothing about **where**
the base letters of `W` live beyond `selected.rel.base`, and `selected.rel.base`
contains all of `A.alphabet.carrier`, which the joint base need not.  The leaf
fixes `eps` and `rho` first and then quantifies over every `W` meeting them, so
an adversarial `W` using a base letter outside `joint.base` has no relabelled
re-spelling at all: the relabelling is the identity on base letters, and the
image word is then not admissible over `joint`.

Hull does not quantify that way.  His §6 relator is chosen after every constant
is fixed, and **every base letter of it is the single adjoined element `t⁻¹`**
— which is exactly what `baseLetters_symmetrized_mem` records, and why
`JointRelatorRespellingStatement` carries the side condition per relator family
instead of as a containment of bases.

So `HullRelatorRespellingBaseCompatibleStatement` below is the leaf **restricted
to relator families whose base letters are joint base letters**, and it is
proved here from `OriginalRelatorRespellingStatement` alone.  It is a genuine
**narrowing**, not the kind of repair
`relativeIsoperimetricBridgeStatement_of_quasiGeodesicBridge` performs, and
`hullRelatorRespellingBaseCompatibleStatement_of_hullRelatorRespelling` proves
the direction: the unrestricted leaf implies this one, not conversely.  Closing
this statement therefore does **not** close the leaf's `sorry` as the assembly
currently consumes it; what it does is reduce the joint half to a clause that
Hull's construction supplies and the leaf's own statement does not.

Nothing here refutes `HullRelatorRespellingStatement`.  A refutation needs an
`AuxiliaryPeripheralFamily` and none is constructed in this repository, since
`SimultaneousAuxiliaryPeripheralSelection` is itself reached only through
`hullYiSuitableFiniteFamily`; the same wall stopped
`GGT/HullSCLemma44RespellingWitness.lean` from turning its collapse into a
refutation.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

/-! ## The three structural obligations that are theorems -/

/-- **`hfamInr` is free.**  The leaf binds the joint peripherals on the `inr`
side to the auxiliary *cores*; `AuxiliaryPeripheralFamily.fam_eq` identifies
those with the selected relative family. -/
theorem famInr_eq_selectedFam {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hinr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    (i : AuxiliaryPeripheralIndex k) :
    joint.fam (Sum.inr i) = selected.rel.fam i := by
  rw [hinr i, selected.fam_eq i]

/-- **`hfamInl` is free.**  An original peripheral element is an original
alphabet letter, hence a letter of Hull's generating set by the leaf's own
containment, hence a letter of the selected relative base. -/
theorem famInl_mem_selectedBase {G : Type u} [Group G] {A : HullGeneratingSet G}
    {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (hinl : ∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam)
    (lam : Lambda) (x : G) (hx : x ∈ joint.fam (Sum.inl lam)) :
    x ∈ selected.rel.base := by
  rw [hinl lam] at hx
  exact selected.base_le
    (hA (GGT.RelGenSet.fam_subset_alphabet original lam hx))

/-- **`halphabet` is free once the base containment is available.**  The joint
alphabet is its base together with the two halves of its family; the base and
the `inl` half land in the selected base, the `inr` half is the selected
family. -/
theorem jointAlphabet_subset_selectedAlphabet {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hfamInl : ∀ (lam : Lambda) (x : G),
      x ∈ joint.fam (Sum.inl lam) → x ∈ selected.rel.base)
    (hfamInr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.rel.fam i) :
    joint.alphabet.carrier ⊆ selected.rel.alphabet.carrier := by
  intro x hx
  have hx' : x ∈ joint.base ∪ ⋃ s : Sum Lambda (AuxiliaryPeripheralIndex k),
      ((joint.fam s : Subgroup G) : Set G) := hx
  rcases hx' with hbase | hfam
  · exact GGT.base_subset_alphabet_carrier selected.rel (hbaseSub hbase)
  · obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hfam
    cases s with
    | inl lam =>
        exact GGT.base_subset_alphabet_carrier selected.rel (hfamInl lam x hs)
    | inr i =>
        rw [hfamInr i] at hs
        exact GGT.RelGenSet.fam_subset_alphabet selected.rel i hs

/-- **The side condition on `W` is free from the reverse base containment.**
Every base letter of a Lemma 4.4 input over the selected family is a selected
base letter, so `selected.rel.base ⊆ joint.base` supplies the clause for every
`W` at once.  Hull's construction supplies the clause the other way, from the
relator: its only base letter is `t⁻¹`. -/
theorem baseLetters_mem_jointBase_of_baseSubset {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hbaseSup : selected.rel.base ⊆ joint.base)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps rho : ℕ} {mu : ℝ}
    (hsc : RelWord.IsLemma44Input selected.rel W eps mu rho) :
    ∀ v ∈ W, ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base := by
  intro v hv x hx
  exact hbaseSup
    (show x ∈ selected.rel.base from
      hsc.admissible v hv (GGT.RelLetter.base x) hx)

/-! ## The joint half at the leaf's binders -/

/-- **The joint re-spelling, from the leaf's own binders plus two clauses.**

`relatorRespellingAt_joint` asks for four structural hypotheses; three of them
are supplied here by the three theorems above.  What remains is the base
containment and the side condition on `W`. -/
theorem relatorRespellingAt_joint_of_familyBinders {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S) {Lambda : Type w}
    (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k)))
    (hA : original.alphabet.carrier ⊆ A.alphabet.carrier)
    (hbaseSub : joint.base ⊆ selected.rel.base)
    (hinl : ∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam)
    (hinr : ∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i)
    {W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k)))}
    {eps0 rho0 eps rho : ℕ} {mu : ℝ}
    (heps : eps0 ≤ eps) (hrho : rho0 ≤ rho) (h20 : 20 * (eps + 1) ≤ rho)
    (hWbase : ∀ v ∈ W, ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base)
    (hsc : RelWord.IsLemma44Input selected.rel W eps mu rho) :
    RelatorRespellingAt joint W eps0 rho0 mu :=
  relatorRespellingAt_joint selected joint hbaseSub
    (famInl_mem_selectedBase selected original joint hA hinl)
    (famInr_eq_selectedFam selected joint hinr)
    (jointAlphabet_subset_selectedAlphabet selected joint hbaseSub
      (famInl_mem_selectedBase selected original joint hA hinl)
      (famInr_eq_selectedFam selected joint hinr))
    heps hrho h20 hWbase hsc

/-! ## The leaf at Hull's own generality -/

/-- **Hull's §6 re-spelling, at the generality his construction has.**

This is `HullRelatorRespellingStatement` with the two clauses the joint half
cannot do without: the joint base is contained in the selected base, and the
relator family's base letters are joint base letters.  Both hold for Hull's
construction — the first by `jointBase_subset_selectedBase_of_baseAdjoined` once
the adjoined letters are base letters, the second by
`baseLetters_symmetrized_mem`, since the only base letter of his relator is
`t⁻¹`.

It is **weaker** than the leaf; see the module header.  It is stated so that the
open mathematics of the leaf's joint half is visible as what it is: not a
missing lemma but two clauses of Hull's construction that the leaf's statement
drops. -/
def HullRelatorRespellingBaseCompatibleStatement : Prop :=
  ∀ {G : Type u} [Group G] {A : HullGeneratingSet G} {N : Subgroup G}
    {k : ℕ} {S : Fin k → Subgroup G}
    (selected : AuxiliaryPeripheralFamily A N S)
    {Lambda : Type w} (original : GGT.RelGenSet G Lambda)
    (joint : GGT.RelGenSet G (Sum Lambda (AuxiliaryPeripheralIndex k))),
    original.alphabet.carrier ⊆ A.alphabet.carrier →
    original.IsHyperbolicallyEmbedded →
    joint.IsHyperbolicallyEmbedded →
    joint.base ⊆ selected.rel.base →
    (∀ lam : Lambda, joint.fam (Sum.inl lam) = original.fam lam) →
    (∀ i : AuxiliaryPeripheralIndex k,
      joint.fam (Sum.inr i) = selected.cores.peripheral i) →
    ∀ mu : ℝ, 0 < mu → mu ≤ 1 / 1000 →
      ∀ eps0 rho0 : ℕ,
        ∃ eps rho : ℕ,
          ∀ W : Set (List (GGT.RelLetter G (AuxiliaryPeripheralIndex k))),
            (∀ v ∈ W, ∀ x : G, GGT.RelLetter.base x ∈ v → x ∈ joint.base) →
            RelWord.IsLemma44Input selected.rel W eps mu rho →
              RelatorRespellingAt original W eps0 rho0 mu ∧
                RelatorRespellingAt joint W eps0 rho0 mu

/-- **The narrowing is a narrowing.**  The unrestricted leaf gives the
base-compatible form by forgetting the side condition, so no strength is claimed
for the statement below that the leaf does not already have. -/
theorem hullRelatorRespellingBaseCompatibleStatement_of_hullRelatorRespelling
    (h : HullRelatorRespellingStatement.{u, w}) :
    HullRelatorRespellingBaseCompatibleStatement.{u, w} := by
  intro G _ A N k S selected Lambda original joint hA horiginal hjoint _hbaseSub
    hinl hinr mu hmu hmuUpper eps0 rho0
  obtain ⟨eps, rho, hres⟩ :=
    h selected original joint hA horiginal hjoint hinl hinr mu hmu hmuUpper
      eps0 rho0
  exact ⟨eps, rho, fun W _ hsc => hres W hsc⟩

/-- **The joint half is discharged: at Hull's generality the re-spelling leaf
reduces to `OriginalRelatorRespellingStatement` and nothing else.**

Every structural hypothesis of `relatorRespellingAt_joint` other than the two
clauses the statement now carries is derived from the statement's own binders,
so the only input left is the original half — one named proposition, matching
Hull §6.  The thresholds are merged exactly as `relatorRespellings_of_original`
merges its own, with the `20 * (eps + 1) ≤ rho` clause of `RelatorRespellingAt`
forced into `rho`. -/
theorem hullRelatorRespellingBaseCompatibleStatement_of_original
    (h : OriginalRelatorRespellingStatement.{u, w}) :
    HullRelatorRespellingBaseCompatibleStatement.{u, w} := by
  intro G _ A N k S selected Lambda original joint hA horiginal _hjoint hbaseSub
    hinl hinr mu hmu hmuUpper eps0 rho0
  obtain ⟨epsO, rhoO, hO⟩ :=
    h selected original horiginal hA mu hmu hmuUpper eps0 rho0
  refine ⟨max eps0 epsO,
    max (max rho0 rhoO) (20 * (max eps0 epsO + 1)), ?_⟩
  intro W hWbase hsc
  have heps0 : eps0 ≤ max eps0 epsO := Nat.le_max_left _ _
  have hepsO : epsO ≤ max eps0 epsO := Nat.le_max_right _ _
  have hrho0 : rho0 ≤ max (max rho0 rhoO) (20 * (max eps0 epsO + 1)) :=
    le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hrhoO : rhoO ≤ max (max rho0 rhoO) (20 * (max eps0 epsO + 1)) :=
    le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have h20 : 20 * (max eps0 epsO + 1) ≤
      max (max rho0 rhoO) (20 * (max eps0 epsO + 1)) := Nat.le_max_right _ _
  refine ⟨hO W (hsc.mono_parameters hepsO le_rfl hrhoO), ?_⟩
  exact relatorRespellingAt_joint_of_familyBinders selected original joint hA
    hbaseSub hinl hinr heps0 hrho0 h20 hWbase hsc

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.famInr_eq_selectedFam
#audit_axioms GroupApproximation.HullSC.famInl_mem_selectedBase
#audit_axioms GroupApproximation.HullSC.jointAlphabet_subset_selectedAlphabet
#audit_axioms GroupApproximation.HullSC.baseLetters_mem_jointBase_of_baseSubset
#audit_axioms GroupApproximation.HullSC.relatorRespellingAt_joint_of_familyBinders
#audit_axioms GroupApproximation.HullSC.hullRelatorRespellingBaseCompatibleStatement_of_hullRelatorRespelling
#audit_axioms GroupApproximation.HullSC.hullRelatorRespellingBaseCompatibleStatement_of_original
