import GroupApproximation.GGT.HullSCCommonQuotient
import GroupApproximation.GGT.HyperbolicFreeGroupAH
import GroupApproximation.Higman.CoprodTorsion
import GroupApproximation.Kazhdan.FreeGroupSharpProfile

/-!
# The free product input of Corollary 7.4 is false as stated, and its repair

`HullSC.hullCommonQuotient_of_tower` proves Hull's Corollary 7.4 from Hull's
Theorem 7.1 and one further input, `HullSC.FreeProductStatement`: the free
product `Γ = E ∗ H₀` carries a Hull alphabet in which *both* free factors are
suitable.

**That statement is false**, and `not_freeProductStatement` proves it.  Its
hypotheses on the second factor are `Group.IsFinitelyPresented`,
`IsPowerTorsionFree` and `Infinite`, and the infinite cyclic group meets all
three.  A homomorphic image of a cyclic group is cyclic, so every two of its
elements have a common nonzero power, and
`HullSC.eq_zero_of_common_zpow_of_independent` forbids that for two independent
loxodromics: no cyclic subgroup ever acts non-elementarily, on any space, so
`FreeProductInput.suitable'` cannot be met.  `FreeGroup (Fin 1)` is the witness
this repository already has the four clauses for
(`Hyperbolic.freeGroup_sharpProfile`), and `FreeGroup (Fin 2)` is an
acylindrically hyperbolic first factor
(`GGT.instIsAcylindricallyHyperbolicFreeGroupFinTwo`).

`not_nonempty_freeProductInput_freeGroupFinOne` is the sharper statement: *no*
first factor admits a `FreeProductInput` over an infinite cyclic second factor.

## What the refutation is not

It is not a defect of Hull's Corollary 7.4, and it is not a defect of
`hullCommonQuotient_of_tower`, whose proof is untouched.  It is a missing
hypothesis: Corollary 7.4 is applied to a second factor that is a non-elementary
hyperbolic group, and non-elementarity is what the statement dropped.  In the
manuscript's `HullCommonQuotientStatement` the second factor carries `Infinite`,
`GroupApproximation.Hyperbolic.IsHyperbolicGroup` and `HasKazhdanPropertyT`, and
the last two were discarded before reaching the free product input --- the `_`
in the `intro` pattern of `hullCommonQuotient_of_tower`.  An infinite group with
property `(T)` is not virtually cyclic, since a quotient map to `Multiplicative
ℤ` would carry `(T)` to a group that does not have it
(`Hyperbolic.not_hasKazhdanPropertyT_multiplicative_int`); that is exactly what
rules the counterexample out.

`FreeProductStatementCorrected` is `FreeProductStatement` with those two
hypotheses restored, and `hullCommonQuotient_of_tower_corrected` is the same
proof over it, so nothing downstream of Corollary 7.4 changes.

## The other correction: the free factors are elliptic on the Bass-Serre tree

The module header of `GGT/HullSCCommonQuotient.lean` justifies the two
suitability fields by

> its Bass-Serre tree has trivial edge stabilizers, so `Γ` is acylindrically
> hyperbolic (Minasyan-Osin), and each free factor acts non-elementarily on it

and the second half of that sentence is false: in the Bass-Serre tree of
`E ∗ H₀` the factor `E` fixes the vertex `E`, so it acts *elliptically*, and the
same holds for `H₀`.  Every element of a free factor has syllable length one, so
the same failure is visible in the Cayley graph `Γ(Γ, E ∪ H₀)`, whose word
metric is the syllable length: the factors are bounded there.  So no
tree-shaped alphabet can witness `FreeProductStatement`, corrected or not.  What
does witness it is an alphabet built from acylindrical actions of the factors
themselves --- the tree of spaces obtained by replacing each vertex of the
Bass-Serre tree by a copy of `Γ(E, A_E)` or `Γ(H₀, A_{H₀})` --- in which the
factors act non-elementarily because they already do on their own vertex space,
and the tree structure is what keeps the whole hyperbolic and the action
acylindrical.  Whoever discharges `FreeProductStatementCorrected` has to build
that; the Bass-Serre tree alone will not do it.

## What is left, and it is one alphabet

`FreeProductAlphabetStatement` is the residue, and
`freeProductStatementCorrected_of_alphabet` proves that it is the whole of it.
The ambient group is pinned to `Monoid.Coprod E H` --- `FreeProductInput.Gamma`
is an arbitrary type, so the abstract input never had to be the free product ---
and the four fields that are not geometry are proved: finite presentation of a
free product, torsion-freeness (`Higman.isPowerTorsionFree_coprod`), the
embedding of the first factor (`coprod_inl_injective`), and the third clause of
Hull's Definition 1.4, which is free over a torsion-free ambient group.  So
Corollary 7.4 is owed exactly one alphabet on `E ∗ H₀` with two independent
loxodromics in each factor: `hullCommonQuotient_of_oneStep_of_alphabet`.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## A cyclic subgroup never acts non-elementarily -/

/-- **A subgroup whose elements are all powers of one element never acts
non-elementarily.**

Two elements `c^a` and `c^b` satisfy `(c^a)^b = (c^b)^a`, so if they are
independent loxodromics then `eq_zero_of_common_zpow_of_independent` forces
`a = b = 0`; but then they are trivial, and a loxodromic element has infinite
order.  Nothing about the space is used beyond the isometry of the action. -/
theorem not_actsNonElementarily_of_zpowers {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (hiso : IsIsometricAction G X)
    {S : Subgroup G} {c : G} (hS : ∀ y ∈ S, ∃ n : ℤ, y = c ^ n) {x : X} :
    ¬ ActsNonElementarily S x := by
  rintro ⟨g, hgS, h, hhS, hg, hh, hind⟩
  obtain ⟨a, rfl⟩ := hS g hgS
  obtain ⟨b, rfl⟩ := hS h hhS
  have hmk : (c ^ a) ^ b = (c ^ b) ^ a := by
    rw [← zpow_mul, ← zpow_mul, mul_comm a b]
  obtain ⟨-, ha⟩ := eq_zero_of_common_zpow_of_independent hiso hg hh hind hmk
  refine not_isOfFinOrder_of_isLoxodromic hg ?_
  rw [ha, zpow_zero]
  exact isOfFinOrder_one

/-- **The image of an infinite cyclic group is a group of powers.**  The
generator of `FreeGroup (Fin 1)` is `FreeGroup.of 0`, and `FreeGroup.of` has a
one-point range there, so its closure being everything says exactly that every
element is a power of `FreeGroup.of 0`. -/
theorem exists_zpow_of_mem_range_freeGroupFinOne {G : Type} [Group G]
    (f : FreeGroup (Fin 1) →* G) :
    ∀ y ∈ f.range, ∃ n : ℤ, y = f (FreeGroup.of (0 : Fin 1)) ^ n := by
  have hrange : Set.range (FreeGroup.of : Fin 1 → FreeGroup (Fin 1))
      = ({FreeGroup.of (0 : Fin 1)} : Set (FreeGroup (Fin 1))) := by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi⟩
      rw [← hi, Fin.eq_zero i]
    · intro hy
      exact ⟨0, hy.symm⟩
  have htop : Subgroup.closure
      ({FreeGroup.of (0 : Fin 1)} : Set (FreeGroup (Fin 1))) = ⊤ := by
    rw [← hrange]
    exact FreeGroup.closure_range_of (Fin 1)
  intro y hy
  obtain ⟨x, hxy⟩ := MonoidHom.mem_range.mp hy
  have hx : x ∈ Subgroup.closure
      ({FreeGroup.of (0 : Fin 1)} : Set (FreeGroup (Fin 1))) := by
    rw [htop]
    exact Subgroup.mem_top x
  obtain ⟨n, hn⟩ := Subgroup.mem_closure_singleton.mp hx
  refine ⟨n, ?_⟩
  rw [← hxy, ← hn, map_zpow]

/-! ## The refutation -/

/-- **No group has a free product input over an infinite cyclic second
factor.**  The second suitability field asks the image of `FreeGroup (Fin 1)` to
act non-elementarily, and that image is a group of powers of one element. -/
theorem not_nonempty_freeProductInput_freeGroupFinOne {E : Type} [Group E] :
    ¬ Nonempty (FreeProductInput E (FreeGroup (Fin 1))) := by
  rintro ⟨I⟩
  exact not_actsNonElementarily_of_zpowers I.alphabet.isometric
    (exists_zpow_of_mem_range_freeGroupFinOne I.emb')
    I.suitable'.actsNonElementarily

/-- **`FreeProductStatement` is false.**

`FreeGroup (Fin 2)` is finitely presented, torsion-free and acylindrically
hyperbolic; `FreeGroup (Fin 1)` is finitely presented, torsion-free and
infinite.  Those are all the hypotheses of the statement, and its conclusion at
that pair is refuted by `not_nonempty_freeProductInput_freeGroupFinOne`.

The missing hypothesis is non-elementarity of the second factor;
`FreeProductStatementCorrected` restores it in the two forms the manuscript
supplies, and `hullCommonQuotient_of_tower_corrected` proves Corollary 7.4 over
that. -/
theorem not_freeProductStatement : ¬ FreeProductStatement := by
  intro hfree
  obtain ⟨-, hEfp, hEtf, -⟩ := Hyperbolic.freeGroup_sharpProfile (Fin 2) ⟨0⟩
  obtain ⟨hHinf, hHfp, hHtf, -⟩ := Hyperbolic.freeGroup_sharpProfile (Fin 1) ⟨0⟩
  exact not_nonempty_freeProductInput_freeGroupFinOne
    (hfree (FreeGroup (Fin 2)) (FreeGroup (Fin 1)) hEfp hHfp hEtf hHtf
      inferInstance hHinf)

/-! ## The corrected statement -/

/-! ## `FreeProductStatementCorrected` and `hullCommonQuotient_of_tower_corrected`

Both now live in `GGT/HullSCCommonQuotient.lean`, next to the statement they
correct and the theorem they supersede, by team-lead's routing call.  This
module keeps what only it can carry: the refutation of `FreeProductStatement`,
the one-way implication between the two statements, the `m = 1` composition,
and the four `FreeProductInput` fields that are theorems. -/

/-- The false statement implies the corrected one: the repair only adds
hypotheses.  Recorded so that the direction of the correction is visible --- the
corrected statement is weaker, and `not_freeProductStatement` says the
implication cannot be reversed. -/
theorem freeProductStatementCorrected_of_freeProductStatement
    (h : FreeProductStatement) : FreeProductStatementCorrected := by
  intro E H instE instH hEfp hHfp hEtf hHtf hEah hHinf _ _
  letI := instE
  letI := instH
  exact h E H hEfp hHfp hEtf hHtf hEah hHinf

/-- **Hull's Corollary 7.4 from Hull's Theorem 7.1 for one relator**, over the
corrected free product input.  This is the form that composes with the rest of
the lane: `HullSC.hullOneStep_of_relator_of_quotient` proves
`HullOneStepStatement` from Hull's §5 and §6, and
`Manuscript.NonMF.TheoremC.hullCommonQuotient` is then owed only
`FreeProductStatementCorrected`. -/
theorem hullCommonQuotient_of_oneStep_corrected (h : HullOneStepStatement.{0})
    (hfree : FreeProductStatementCorrected) :
    Manuscript.NonMF.TheoremC.HullCommonQuotientStatement :=
  hullCommonQuotient_of_tower_corrected (hullTowerStatement_of_oneStep h) hfree

/-! ## The free product itself: everything but the alphabet is a theorem -/

/-- **A free factor embeds in the binary free product.**  `Monoid.Coprod.lift`
of the identity and the trivial homomorphism retracts `Monoid.Coprod E H` onto
`E` along `inl`. -/
theorem coprod_inl_injective {E H : Type} [Group E] [Group H] :
    Function.Injective (Monoid.Coprod.inl : E →* Monoid.Coprod E H) := by
  intro a b hab
  have h : (Monoid.Coprod.lift (MonoidHom.id E) (1 : H →* E))
        (Monoid.Coprod.inl a)
      = (Monoid.Coprod.lift (MonoidHom.id E) (1 : H →* E))
        (Monoid.Coprod.inl b) := by
    rw [hab]
  rwa [Monoid.Coprod.lift_apply_inl, Monoid.Coprod.lift_apply_inl,
    MonoidHom.id_apply, MonoidHom.id_apply] at h

/-- **The geometric residue of the free product input.**

`FreeProductStatementCorrected` asks for a whole `FreeProductInput`; this asks
only for Hull's alphabet on the free product itself, together with the two
clauses that say the free factors are non-elementary on it.  Everything else
`FreeProductInput` records is a theorem about `Monoid.Coprod E H`:

* finite presentation --- the free product of two finitely presented groups;
* torsion-freeness --- `Higman.isPowerTorsionFree_coprod`, Kurosh's theorem in
  the form this repository proves it;
* the embedding of the first factor --- `coprod_inl_injective`;
* the third clause of Hull's Definition 1.4 for both factors --- free over a
  torsion-free ambient group, `suitable_of_torsionFree`.

`freeProductStatementCorrected_of_alphabet` supplies all four, so this is what
Hull's Corollary 7.4 is still owed, and nothing more.  Pinning the ambient group
to `Monoid.Coprod E H` is part of the sharpening: `FreeProductInput.Gamma` is an
arbitrary type, so the abstract statement does not commit to the free product at
all. -/
def FreeProductAlphabetStatement : Prop :=
  ∀ (E H : Type) [Group E] [Group H],
    Group.IsFinitelyPresented E → Group.IsFinitelyPresented H →
      IsPowerTorsionFree E → IsPowerTorsionFree H →
        IsAcylindricallyHyperbolic E → Infinite H →
          GroupApproximation.Hyperbolic.IsHyperbolicGroup H →
            HasKazhdanPropertyT.{0, 0} H →
              ∃ A : HullGeneratingSet (Monoid.Coprod E H),
                ActsNonElementarily
                    (Monoid.Coprod.inl : E →* Monoid.Coprod E H).range
                    (Cayley.base A.alphabet) ∧
                  ActsNonElementarily
                    (Monoid.Coprod.inr : H →* Monoid.Coprod E H).range
                    (Cayley.base A.alphabet)

/-- **The corrected free product input, from the alphabet alone.**  The
remaining four fields are proved here rather than asked for. -/
theorem freeProductStatementCorrected_of_alphabet
    (h : FreeProductAlphabetStatement) : FreeProductStatementCorrected := by
  intro E H instE instH hEfp hHfp hEtf hHtf hEah hHinf hHhyp hHT
  letI := instE
  letI := instH
  haveI := hEfp
  haveI := hHfp
  obtain ⟨A, hEne, hHne⟩ :=
    h E H hEfp hHfp hEtf hHtf hEah hHinf hHhyp hHT
  have htf : IsPowerTorsionFree (Monoid.Coprod E H) :=
    Higman.isPowerTorsionFree_coprod hEtf hHtf
  exact ⟨{ Gamma := Monoid.Coprod E H
           group := inferInstance
           fp := inferInstance
           torsionFree := htf
           emb := Monoid.Coprod.inl
           emb' := Monoid.Coprod.inr
           inj := coprod_inl_injective
           alphabet := A
           suitable := suitable_of_torsionFree htf hEne
           suitable' := suitable_of_torsionFree htf hHne }⟩

/-- **Hull's Corollary 7.4 from his §5 and §6 and one alphabet.**  The sharpest
form the reduction takes: `HullOneStepStatement` is Hull's Theorem 7.1 for a
single relator, which `HullSC.hullOneStep_of_relator_of_quotient` proves from
his Theorem 5.1 and his §6, and `FreeProductAlphabetStatement` is a statement
about one generating set of `E ∗ H₀`. -/
theorem hullCommonQuotient_of_oneStep_of_alphabet (h : HullOneStepStatement.{0})
    (halph : FreeProductAlphabetStatement) :
    Manuscript.NonMF.TheoremC.HullCommonQuotientStatement :=
  hullCommonQuotient_of_oneStep_corrected h
    (freeProductStatementCorrected_of_alphabet halph)

end HullSC
end GroupApproximation
