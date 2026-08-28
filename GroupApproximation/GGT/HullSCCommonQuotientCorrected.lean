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

/-- **The free product input, with the hypotheses that make it true.**

`FreeProductStatement` with the two clauses `HullCommonQuotientStatement`
supplies about `H₀` and `hullCommonQuotient_of_tower` throws away: that it is
hyperbolic and that it has property `(T)`.  Together with `Infinite H` the
second of them makes `H` non-elementary --- an infinite virtually cyclic group
has an infinite cyclic quotient and property `(T)` would descend to it --- which
is what `FreeProductInput.suitable'` needs and what
`not_freeProductStatement` shows cannot be dispensed with.

Nothing else changes: the conclusion is the same `FreeProductInput`, so the
construction asked for is the same one, the free product with an alphabet in
which both factors are suitable. -/
def FreeProductStatementCorrected : Prop :=
  ∀ (E H : Type) [Group E] [Group H],
    Group.IsFinitelyPresented E → Group.IsFinitelyPresented H →
      IsPowerTorsionFree E → IsPowerTorsionFree H →
        IsAcylindricallyHyperbolic E → Infinite H →
          GroupApproximation.Hyperbolic.IsHyperbolicGroup H →
            HasKazhdanPropertyT.{0, 0} H →
              Nonempty (FreeProductInput E H)

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

/-! ## Corollary 7.4 over the corrected input -/

/-- **Hull's Corollary 7.4**, in the form
`Manuscript.NonMF.TheoremC.HullCommonQuotientStatement` records it, from Hull's
Theorem 7.1 and the *corrected* free product input.

This is `hullCommonQuotient_of_tower` with the two hypotheses on `H₀` that its
`intro` pattern discards passed on to the free product input instead.  The proof
is otherwise unchanged: two applications of Theorem 7.1, the first absorbing all
of `Γ` into the image of `E`, the second absorbing all of `Q₁` into the image of
`H₀`, which is legitimate because the tower keeps a prescribed suitable subgroup
suitable (`HullStep.suitable_map_family`). -/
theorem hullCommonQuotient_of_tower_corrected (htower : HullTowerStatement.{0})
    (hfree : FreeProductStatementCorrected) :
    Manuscript.NonMF.TheoremC.HullCommonQuotientStatement := by
  classical
  intro E instE H₀ instH₀ hEfp hEtf hEah hH₀inf hH₀fp hH₀tf hH₀hyp hH₀T F
  letI := instE
  letI := instH₀
  -- `Γ = E ∗ H₀`, with both factors suitable.
  obtain ⟨I⟩ := hfree E H₀ hEfp hH₀fp hEtf hH₀tf hEah hH₀inf hH₀hyp hH₀T
  -- a ball of `Γ(Γ, 𝒜)` containing the image of the prescribed finite set
  have hFfin : ((I.emb : E → I.Gamma) '' (F : Set E)).Finite :=
    Set.Finite.image _ F.finite_toSet
  obtain ⟨R₁, hR₁⟩ := exists_subset_cayleyBall I.alphabet.alphabet hFfin
  -- a finite generating family of `Γ`
  obtain ⟨m, t, htop⟩ := exists_finite_generating_family I.Gamma
  -- **First application**: absorb all of `Γ` into the image of `E`.
  obtain ⟨D₁⟩ := htower (S := fun _ : Fin 1 => I.emb'.range) I.alphabet
    I.suitable (fun _ => I.suitable') t R₁
  have hq₁top : I.emb.range.map D₁.step.q = ⊤ :=
    map_eq_top_of_generators_mem D₁.step.q D₁.step.surjective htop D₁.mem_map
  have hQ₁tf : IsPowerTorsionFree D₁.step.Q :=
    torsionFree_of_finiteOrder_lift I.torsionFree D₁.step.q
      D₁.step.finiteOrder_lift
  obtain ⟨T₁, -, hT₁ker⟩ := D₁.kerNormallyGenerated
  haveI : Group.IsFinitelyPresented D₁.step.Q :=
    Group.IsFinitelyPresented.of_surjective D₁.step.q D₁.step.surjective
      ⟨(T₁ : Set I.Gamma), T₁.finite_toSet, hT₁ker.symm⟩
  -- a ball of `Γ(Q₁, 𝒜₁)` containing the image of the prescribed finite set
  have hFfin₂ : ((D₁.step.q : I.Gamma → D₁.step.Q) ''
      ((I.emb : E → I.Gamma) '' (F : Set E))).Finite := hFfin.image _
  obtain ⟨R₂, hR₂⟩ :=
    exists_subset_cayleyBall D₁.step.hullSet.alphabet hFfin₂
  -- a finite generating family of `Q₁`
  obtain ⟨m₂, t₂, htop₂⟩ := exists_finite_generating_family D₁.step.Q
  -- **Second application**: absorb all of `Q₁` into the image of `H₀`.
  obtain ⟨D₂⟩ := htower (S := fun j : Fin 0 => Fin.elim0 j) D₁.step.hullSet
    (D₁.step.suitable_map_family 0) (fun j : Fin 0 => Fin.elim0 j) t₂ R₂
  have hq₂top : (I.emb'.range.map D₁.step.q).map D₂.step.q = ⊤ :=
    map_eq_top_of_generators_mem D₂.step.q D₂.step.surjective htop₂ D₂.mem_map
  have hQ₂tf : IsPowerTorsionFree D₂.step.Q :=
    torsionFree_of_finiteOrder_lift hQ₁tf D₂.step.q D₂.step.finiteOrder_lift
  obtain ⟨T₂, -, hT₂ker⟩ := D₂.kerNormallyGenerated
  haveI hQ₂fp : Group.IsFinitelyPresented D₂.step.Q :=
    Group.IsFinitelyPresented.of_surjective D₂.step.q D₂.step.surjective
      ⟨(T₂ : Set D₁.step.Q), T₂.finite_toSet, hT₂ker.symm⟩
  -- the composite `Γ ↠ Q₂`
  have hcomp : ∀ (K : Subgroup I.Gamma),
      (K.map D₁.step.q).map D₂.step.q
        = K.map (D₂.step.q.comp D₁.step.q) := by
    intro K
    rw [Subgroup.map_map]
  -- `E ↠ Q₂`
  have hEtop : I.emb.range.map (D₂.step.q.comp D₁.step.q) = ⊤ := by
    rw [← hcomp, hq₁top]
    exact Subgroup.map_top_of_surjective D₂.step.q D₂.step.surjective
  -- `H₀ ↠ Q₂`
  have hHtop : I.emb'.range.map (D₂.step.q.comp D₁.step.q) = ⊤ := by
    rw [← hcomp]
    exact hq₂top
  have hsurj : ∀ (K : Type) [Group K] (e : K →* I.Gamma),
      e.range.map (D₂.step.q.comp D₁.step.q) = ⊤ →
        Function.Surjective ((D₂.step.q.comp D₁.step.q).comp e) := by
    intro K _ e hK y
    have hy : y ∈ e.range.map (D₂.step.q.comp D₁.step.q) := by
      rw [hK]
      exact Subgroup.mem_top y
    obtain ⟨g, hg, hgy⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hg
    refine ⟨x, ?_⟩
    show (D₂.step.q.comp D₁.step.q) (e x) = y
    rw [hx]
    exact hgy
  -- property (T) travels along `H₀ ↠ Q₂`
  have hQ₂T : HasKazhdanPropertyT.{0, 0} D₂.step.Q :=
    HasKazhdanPropertyT.of_surjective ((D₂.step.q.comp D₁.step.q).comp I.emb')
      (hsurj H₀ I.emb' hHtop) hH₀T
  refine ⟨D₂.step.Q, D₂.step.group,
    (D₂.step.q.comp D₁.step.q).comp I.emb,
    hsurj E I.emb hEtop, hQ₂fp, hQ₂tf, hQ₂T,
    isAcylindricallyHyperbolic_of_hullGeneratingSet D₂.step.hullSet, ?_⟩
  -- injectivity on the prescribed finite set
  intro x hx y hy hxy
  have hx₁ : I.emb x ∈ cayleyBall I.alphabet.alphabet R₁ :=
    hR₁ (Set.mem_image_of_mem _ hx)
  have hy₁ : I.emb y ∈ cayleyBall I.alphabet.alphabet R₁ :=
    hR₁ (Set.mem_image_of_mem _ hy)
  have hx₂ : D₁.step.q (I.emb x) ∈ cayleyBall D₁.step.hullSet.alphabet R₂ :=
    hR₂ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hx))
  have hy₂ : D₁.step.q (I.emb y) ∈ cayleyBall D₁.step.hullSet.alphabet R₂ :=
    hR₂ (Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hy))
  have hstep₂ : D₂.step.q (D₁.step.q (I.emb x))
      = D₂.step.q (D₁.step.q (I.emb y)) := hxy
  have hstep₁ : D₁.step.q (I.emb x) = D₁.step.q (I.emb y) :=
    D₂.step.injOn hx₂ hy₂ hstep₂
  exact I.inj (D₁.step.injOn hx₁ hy₁ hstep₁)

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
