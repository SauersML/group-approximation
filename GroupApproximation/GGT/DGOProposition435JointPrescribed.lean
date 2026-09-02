import GroupApproximation.GGT.DGOProposition435InclusionFinite
import GroupApproximation.GGT.HullSCConeOffHeavyQuasiconvex
import GroupApproximation.GGT.HullYiAlphabetTransfer
import GroupApproximation.GGT.HullSCLemma44FamilyInclusionStatement

/-!
# The joint family at a prescribed relative base

The joint form of Proposition 4.35 that the filling lane needs is, in the
relatively hyperbolic setting, Osin's theorem on elementary subgroups:

> Let `G` be a group hyperbolic relative to a collection of subgroups
> `{H_λ}`, `g` a hyperbolic element of infinite order of `G`.  Then the element
> `g` is contained in a unique maximal elementary subgroup `E_G(g)`, and the
> group `G` is hyperbolic relative to the collection `{H_λ} ∪ {E_G(g)}`.

That is Theorem `E(g)` of Osin, *Peripheral fillings of relatively hyperbolic
groups* (arXiv `math/0411039`, `embed-final.tex:236`), where it is quoted from
Osin, *Elementary subgroups of relatively hyperbolic groups and bounded
generation*, Theorem 4.3 and Corollary 1.7.  Osin uses it exactly as the
filling lane does, and he adjoins the filling target to the relative generating
set first: *"Passing to a new relative generating set `X' = X ∪ {t}` if
necessary, we may assume that `t ∈ X`"* (`embed-final.tex:1937`).  That is the
adjoined form of `GGT/DGOProposition435.lean`.

Note that this is NOT Dahmani--Guirardel--Osin's Theorem 6.8, which has no
original family and produces an unspecified relative generating set.

## What is proved here

The prescribed-base form splits as Hull's Theorem 3.16 assembly splits, and the
first clause is now a theorem rather than an input.

* **Clause (a)**, hyperbolicity of `Γ(G, X ⊔ ℋ ⊔ ℰ)`, is
  `jointHyperbolic_of_isLoxodromic_relative`.  The joint alphabet is the
  cone-off of the *relative* alphabet along the cyclic subgroups, and
  `HullSC.exists_hyperbolic_coneOffFamily_zpowers_of_fourPoint` cones off an
  arbitrary alphabet along the cyclic subgroups of elements loxodromic on it.
  The relative alphabet is hyperbolic because the original family is
  hyperbolically embedded, and the selected elements are loxodromic on it
  because they are loxodromic on Hull's larger alphabet and loxodromy passes to
  a smaller alphabet (`HullSC.isLoxodromic_base_of_subset`, Hull's Lemma A.1).
  No finite-excess hypothesis and no matched alphabet is needed.
* **Clause (b)**, local finiteness of the auxiliary metrics, is the auxiliary
  family's own hyperbolic embeddedness.
* **Clause (c)**, local finiteness of the original peripheral metrics in the
  joint alphabet, is Proposition 4.14 together with the isolated-witness
  statement, both already in place.

`isHyperbolicallyEmbedded_jointRelGenSet_of_isLoxodromic_relative` assembles
the three, so the joint family is hyperbolically embedded with Proposition 4.14
as the only input.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

variable {G : Type u} [Group G] {Λ : Type v}

/-! ## Clause (a): the joint graph is a cone-off of the relative graph -/

/-- **The joint alphabet is the cone-off of the relative alphabet along the
cyclic subgroups.** -/
theorem jointRelGenSet_alphabet_carrier_eq_coneOff {I : Type}
    (D : RelGenSet G Λ) (E : RelGenSet G I) (g : I → G)
    (hfam : ∀ i : I, E.fam i = Subgroup.zpowers (g i)) :
    (jointRelGenSet D E).alphabet.carrier =
      (HullSC.coneOffFamily D.alphabet
        (fun i => Subgroup.zpowers (g i))).alphabet.carrier := by
  rw [jointRelGenSet_alphabet_carrier D E]
  show D.alphabet.carrier ∪ (⋃ i : I, ((E.fam i : Subgroup G) : Set G))
    = D.alphabet.carrier ∪
      (⋃ i : I, ((Subgroup.zpowers (g i) : Subgroup G) : Set G))
  congr 1
  refine Set.iUnion_congr ?_
  intro i
  rw [hfam i]

/-- **Clause (a) of the prescribed-base joint form.**

The original family is hyperbolically embedded, so its relative Cayley graph is
hyperbolic; the selected elements are loxodromic on it; and coning off the
cyclic subgroups of elements loxodromic on a hyperbolic Cayley graph leaves it
hyperbolic.  So the joint relative Cayley graph is hyperbolic, with no
condition relating the two bases. -/
theorem jointHyperbolic_of_isLoxodromic_relative {I : Type} [Fintype I]
    (D : RelGenSet G Λ) (E : RelGenSet G I) (g : I → G)
    (hfam : ∀ i : I, E.fam i = Subgroup.zpowers (g i))
    (hlox : ∀ i : I, IsLoxodromic (g i) (Cayley.base D.alphabet))
    (hD : D.IsHyperbolicallyEmbedded) :
    ∃ delta : ℝ,
      IsHyperbolicSpace delta (Cayley (jointRelGenSet D E).alphabet) := by
  obtain ⟨delta, hdelta⟩ := hD.hyperbolic
  refine exists_isHyperbolicSpace_of_alphabet_eq
    (OsinComponents.alphabet_eq_of_carrier_eq
      (jointRelGenSet_alphabet_carrier_eq_coneOff D E g hfam)) ?_
  exact HullSC.exists_hyperbolic_coneOffFamily_zpowers_of_fourPoint D.alphabet
    hdelta g hlox

/-! ## The prescribed-base joint form -/

/-- **The joint family at a prescribed relative base.**

Osin's theorem on elementary subgroups, in the form the filling lane consumes:
the original family together with the cyclic subgroups of the selected
loxodromic elements is hyperbolically embedded over the original relative base.
Proposition 4.14 is the only input; clause (a) is
`jointHyperbolic_of_isLoxodromic_relative` and clause (c) is the finite form,
whose isolated-witness half is a theorem. -/
theorem isHyperbolicallyEmbedded_jointRelGenSet_of_isLoxodromic_relative
    (h414 : OsinComponents.DGOProposition414Uniform.{u, 0})
    {I : Type} [Fintype I] (D : RelGenSet G Λ) (E : RelGenSet G I) (g : I → G)
    (hfam : ∀ i : I, E.fam i = Subgroup.zpowers (g i))
    (hlox : ∀ i : I, IsLoxodromic (g i) (Cayley.base D.alphabet))
    (hbase : D.alphabet.carrier ⊆ E.base)
    (hEsymm : OsinComponents.DGO421BaseSymmetric E)
    (hD : D.IsHyperbolicallyEmbedded) (hE : E.IsHyperbolicallyEmbedded) :
    (jointRelGenSet D E).IsHyperbolicallyEmbedded :=
  isHyperbolicallyEmbedded_jointRelGenSet_of_proposition414Uniform h414
    dgoProposition435IsolatedWitness D E hbase hEsymm hD hE
    (jointHyperbolic_of_isLoxodromic_relative D E g hfam hlox hD)

/-- The loxodromy hypothesis is supplied by loxodromy on any larger alphabet,
which is Hull's Lemma A.1.  The filling lane selects its elements loxodromic on
Hull's alphabet, and the relative alphabet is contained in it. -/
theorem isLoxodromic_relative_of_isLoxodromic_hull {I : Type}
    (D : RelGenSet G Λ) (A : Alphabet G)
    (hA : D.alphabet.carrier ⊆ A.carrier) {g : I → G}
    (hlox : ∀ i : I, IsLoxodromic (g i) (Cayley.base A)) :
    ∀ i : I, IsLoxodromic (g i) (Cayley.base D.alphabet) :=
  fun i => HullSC.isLoxodromic_base_of_subset hA (hlox i)

end RelHyp
end GGT

namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

/-! ## The filling lane's instance -/

/-- The loxodromic generator attached to each auxiliary core. -/
def AuxiliaryNonElementaryCores.lox {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ} {S : Fin k → Subgroup G}
    (C : AuxiliaryNonElementaryCores A N S) : AuxiliaryPeripheralIndex k → G
  | (none, b) => C.coreN.lox b
  | (some j, b) => (C.coreS j).lox b

/-- Each auxiliary peripheral is the cyclic subgroup of its generator. -/
theorem AuxiliaryNonElementaryCores.peripheral_eq_zpowers {G : Type u}
    [Group G] {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (C : AuxiliaryNonElementaryCores A N S)
    (i : AuxiliaryPeripheralIndex k) :
    C.peripheral i = Subgroup.zpowers (C.lox i) := by
  rcases i with ⟨j, b⟩
  cases j with
  | none => exact C.cyclicN b
  | some j => exact C.cyclicS j b

/-- Each generator is loxodromic on Hull's Cayley graph. -/
theorem AuxiliaryNonElementaryCores.isLoxodromic_lox {G : Type u} [Group G]
    {A : HullGeneratingSet G} {N : Subgroup G} {k : ℕ}
    {S : Fin k → Subgroup G} (C : AuxiliaryNonElementaryCores A N S)
    (i : AuxiliaryPeripheralIndex k) :
    IsLoxodromic (C.lox i) (Cayley.base A.alphabet) := by
  rcases i with ⟨j, b⟩
  cases j with
  | none => exact C.coreN.lox_isLoxodromic b
  | some j => exact (C.coreS j).lox_isLoxodromic b

/-- **The joint-family selection input, from Proposition 4.14 alone.**

The selected auxiliary peripherals are the cyclic subgroups of elements
loxodromic on Hull's alphabet, hence loxodromic on the smaller original
relative alphabet, so the joint relative Cayley graph is a cone-off of a
hyperbolic graph along quasiconvex cyclic orbits and is hyperbolic.  With that,
the only remaining input of the joint family is Proposition 4.14. -/
theorem jointAuxiliaryPeripheralEmbedding_of_proposition414Uniform
    (h414 : GGT.OsinComponents.DGOProposition414Uniform.{u, 0}) :
    JointAuxiliaryPeripheralEmbedding.{u, w} := by
  intro G _ A N k S selected Lambda original hA horig
  have hfam : ∀ i : AuxiliaryPeripheralIndex k,
      selected.rel.fam i = Subgroup.zpowers (selected.cores.lox i) := by
    intro i
    rw [selected.fam_eq i, selected.cores.peripheral_eq_zpowers i]
  have hlox : ∀ i : AuxiliaryPeripheralIndex k,
      IsLoxodromic (selected.cores.lox i) (Cayley.base original.alphabet) :=
    fun i => isLoxodromic_base_of_subset hA (selected.cores.isLoxodromic_lox i)
  have hbase : original.alphabet.carrier ⊆ selected.rel.base :=
    hA.trans selected.base_le
  refine ⟨GGT.RelHyp.jointRelGenSet original selected.rel,
    GGT.RelHyp.jointRelGenSet_base_inv original selected.rel,
    fun _ => rfl, fun i => selected.fam_eq i,
    GGT.RelHyp.isHyperbolicallyEmbedded_jointRelGenSet_of_isLoxodromic_relative
      h414 original selected.rel selected.cores.lox hfam hlox hbase
      selected.base_inv horig selected.embedded,
    ∅, Set.finite_empty, ?_⟩
  intro x hx
  exact Or.inl (GGT.RelHyp.properBase_subset_base original hx)

/-- **The unrepaired family-inclusion leaf, from Proposition 4.14 and the
repaired joint leaf.**

This is the whole of Proposition 4.35's contribution to the assembly, in one
step: the joint-selection input is a theorem, so the only inputs left are
Proposition 4.14 and Hull's Lemma 4.4 in its repaired joint form. -/
theorem hullLemma44CanonicalQuotientFamilyInclusionStatement_of_proposition414Uniform
    (h414 : GGT.OsinComponents.DGOProposition414Uniform.{u, 0})
    (h44 : HullLemma44CanonicalQuotientFamilyInclusionJointStatement.{u, w}) :
    HullLemma44CanonicalQuotientFamilyInclusionStatement.{u, w} :=
  hullLemma44CanonicalQuotientFamilyInclusionStatement_of_joint
    (jointAuxiliaryPeripheralEmbedding_of_proposition414Uniform h414) h44

end HullSC
end GroupApproximation
