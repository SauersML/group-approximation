import GroupApproximation.Sofic.CliffordWitnessDirectDefect
import GroupApproximation.Sofic.CliffordLampNormalForm
import GroupApproximation.Manuscript.OneSidedMFRadical.AffineCliffordTrace
import GroupApproximation.Algebra.PermutationalWreath
import GroupApproximation.Meta.AxiomGuard

/-!
# Printed sentences of `prop:clifford-self-embedding` and the concrete instance

`non_mf_groups_exist.tex` lines 1387-1550 cover the construction of the affine Clifford witness
`W`, Proposition `prop:clifford-self-embedding` and its proof, Proposition `prop:clifford-locally-rf`
and its proof, the concrete instance `Γ̄ = ℤ³ ⋊ SL₃(ℤ)`, and the proof of Theorem
`thm:amenable-trace`.  Most of these printed sentences already have carriers:
`Sofic/CliffordConstructionSentences.lean` covers the `Cl(X)` construction and the first half of
`prop:clifford-self-embedding`'s proof; `Sofic/CliffordWitnessSoficSentences.lean` covers
`prop:clifford-locally-rf`'s proof and the proof of `thm:amenable-trace`; the two propositions'
own statements, and several individual proof clauses, already have exact named carriers in
`Sofic/CliffordWitnessDirectDefect.lean`, `Manuscript/OneSidedMFRadical/AffineCliffordTrace.lean`,
and elsewhere (see the sentence-census rows for this module).

This module supplies `manuscriptSentence_<slug>` carriers for the printed sentences in that range
that had no carrier yet: the middle of `prop:clifford-self-embedding`'s proof (the root lamp's
centralizing/fixing clause, the distinct-lamps-are-involutions-with-nontrivial-commutator clause,
the `d = [x,a] = xy`, `d² = [x,y] = ε` factorization, and the "`⟨ε⟩` is central, normal, finite,
hence has `(T)`" clause), the "killing `ε`" central-extension clause for `Cl(X)`, and the
concrete instance's "`α` is injective, has index eight, and `a` escapes its range" clause at the
literal `gammaBar`/`conjD` model used by the rest of the development (as opposed to the
independent matrix model `Monsters/AffineSL3Doubling.lean` feeds into the index computation).
Every proof below is a direct projection from already-landed declarations: no new mathematics.
-/

namespace GroupApproximation
namespace AmenableTraceSentencesB

open MarkedCompression CliffordLamp CliffordWitnessDirectDefect
open scoped commutatorElement

noncomputable section

/-! ## `prop:clifford-self-embedding`'s proof, first sentence -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1443-1445`).

> Identify `Γ` with its level-zero copy in `V ≤ W`, and let `c` be the lamp at the root coset
> `Γ ∈ X`; it centralizes `Γ`, which fixes that coset.

`c` is `cAmbient α hα`, the lamp at the root coset (`rootCoset α hα`); it centralizes the copy of
`Γ` (`comm_c`), and that copy fixes the root coset (`iotaVertical_smul_rootCoset`). -/
theorem manuscriptSentence_rootLampCentralizesFixesCoset
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α) :
    (∀ γ : Γ, Commute (cAmbient α hα) (iotaAmbient α hα γ)) ∧
      (∀ γ : Γ, iotaVertical α hα γ • rootCoset α hα = rootCoset α hα) :=
  ⟨comm_c α hα, iotaVertical_smul_rootCoset α hα⟩

/-! ## `prop:clifford-self-embedding`'s proof, the two central algebraic sentences -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1448-1449`).

> so `x = tct^{-1}` and `y = axa^{-1}` are distinct lamps, involutions with `[x,y] = ε ≠ 1`.

`x` is `compressionRoot α hα`; `y` is its `ι(a)`-conjugate.  Both are involutions
(`compressionRoot_sq`, and `conj_sq_eq_one` applied to it); their commutator is the central sign
(`commutator_conjugate_eq_commutator_sq_of_sq_eq_one` composed with `sign_eq_pointDefect_sq`,
which is the same identity the manuscript's next sentence names `d²`); the sign is nontrivial
(`signAmbient_ne_one`); and `x ≠ y` because `x = y` would force `⁅x,y⁆ = ⁅x,x⁆ = 1 ≠ ε`. -/
theorem manuscriptSentence_distinctInvolutionsCommutatorSign
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    {a : Γ} (ha : a ∉ Set.range α) :
    compressionRoot α hα ≠
        iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹ ∧
      compressionRoot α hα ^ 2 = 1 ∧
      (iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹) ^ 2 = 1 ∧
      ⁅compressionRoot α hα,
          iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ =
        signAmbient α hα ∧
      signAmbient α hα ≠ 1 := by
  have hxsq : compressionRoot α hα ^ 2 = 1 := compressionRoot_sq α hα
  have hysq : (iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹) ^ 2 = 1 :=
    conj_sq_eq_one (compressionRoot α hα) (iotaAmbient α hα a) hxsq
  have hcomm : ⁅compressionRoot α hα,
      iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ =
        signAmbient α hα := by
    rw [commutator_conjugate_eq_commutator_sq_of_sq_eq_one (compressionRoot α hα)
      (iotaAmbient α hα a) hxsq]
    exact (sign_eq_pointDefect_sq α hα ha).symm
  have hsignne : signAmbient α hα ≠ 1 := signAmbient_ne_one α hα
  refine ⟨fun heq ↦ ?_, hxsq, hysq, hcomm, hsignne⟩
  apply hsignne
  have hxy :
      (⁅compressionRoot α hα,
          iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ :
            Ambient α hα) =
        ⁅iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹,
            iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ :=
    congrArg (fun z ↦ ⁅z, iotaAmbient α hα a * compressionRoot α hα *
      (iotaAmbient α hα a)⁻¹⁆) heq
  rw [← hcomm, hxy, commutatorElement_def]
  group

/-- **Printed sentence** (`non_mf_groups_exist.tex:1450`).

> Then `d = [x,a] = xy` and `d² = xyxy = [x,y] = ε`,

`d` is `pointDefect α hα a := ⁅compressionRoot α hα, ι(a)⁆`.  The factorization `d = xy` is
`commutator_eq_mul_conj`; the reading of `d²` as `[x,y]` is
`commutator_conjugate_eq_commutator_sq_of_sq_eq_one`; and `d² = ε` is `sign_eq_pointDefect_sq`. -/
theorem manuscriptSentence_defectFactorization
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)
    {a : Γ} (ha : a ∉ Set.range α) :
    pointDefect α hα a =
        compressionRoot α hα *
          (iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹) ∧
      pointDefect α hα a ^ 2 =
        ⁅compressionRoot α hα,
            iotaAmbient α hα a * compressionRoot α hα * (iotaAmbient α hα a)⁻¹⁆ ∧
      pointDefect α hα a ^ 2 = signAmbient α hα :=
  ⟨commutator_eq_mul_conj (compressionRoot α hα) (iotaAmbient α hα a) (compressionRoot_sq α hα),
    (commutator_conjugate_eq_commutator_sq_of_sq_eq_one (compressionRoot α hα)
      (iotaAmbient α hα a) (compressionRoot_sq α hα)).symm,
    (sign_eq_pointDefect_sq α hα ha).symm⟩

/-! ## `prop:clifford-self-embedding`'s proof, the sign subgroup -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1453-1454`).

> The subgroup `⟨ε⟩` is central, so normal, and it is finite, so it has property `(T)`.

`⟨ε⟩` is `signSubgroup α hα`; centrality of its generator is `signAmbient_central`, normality is
the instance `signSubgroup_normal`, finiteness is the instance `signSubgroup_finite`, and every
finite group has property `(T)` (`hasKazhdanPropertyT_of_finite`). -/
theorem manuscriptSentence_signSubgroupCentralNormalFiniteHasT
    {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α) :
    (∀ g : Ambient α hα, Commute (signAmbient α hα) g) ∧
      (signSubgroup α hα).Normal ∧
      Finite (signSubgroup α hα) ∧
      HasKazhdanPropertyT.{0, 0} (signSubgroup α hα) :=
  ⟨signAmbient_central α hα, signSubgroup_normal α hα, signSubgroup_finite α hα,
    hasKazhdanPropertyT_of_finite (signSubgroup α hα)⟩

/-! ## The `Cl(X)` construction, the "killing `ε`" clause -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1421-1424`, first half).

> Killing `ε` leaves `F₂^{(X)} ≅ ⊕_X C₂`, so `Cl(X)` is a central extension of `⊕_X C₂` by `C₂`.

The "killing `ε`" map is `config ∘ toModel X : Cl(X) → (X →₀ ZMod 2)`, the second coordinate of
the printed isomorphism `toModel X` (`Sofic/CliffordLampGroup.lean`, proved bijective in
`Sofic/CliffordLampNormalForm.lean`).  It is surjective onto the printed `F₂^{(X)} = X →₀ ZMod 2`
(every finitely supported function is `(toModel X)`'s second coordinate at some group element,
since `toModel X` is onto `SignedModel X`), its fibre over `0` is exactly `{1, ε}` (case-splitting
on the two elements of `ZMod 2` and using injectivity of `toModel X`), and `ε` is central
(`sign_commute`).  This is the printed central extension `1 → ⟨ε⟩ → Cl(X) → F₂^{(X)} → 1`.  The
second half of the printed sentence, that `W` itself is a central extension of the permutational
wreath product `C₂ ≀_X V` by `⟨ε⟩`, is `manuscriptSentence_wCentralExtensionOfWreath` below. -/
theorem manuscriptSentence_cliffordLampKillSignCentralExtension
    {X : Type} [LinearOrder X] :
    Function.Surjective (fun w : CliffordLamp X ↦ (toModel X w).config) ∧
      (∀ w : CliffordLamp X, (toModel X w).config = 0 ↔ w = 1 ∨ w = sign X) ∧
      (∀ g : CliffordLamp X, Commute (sign X) g) := by
  obtain ⟨hbij, -, -⟩ := CliffordLampNormalForm.toModel_bijective_printed (X := X)
  refine ⟨fun f ↦ ?_, fun w ↦ ⟨fun hcfg ↦ ?_, ?_⟩, sign_commute X⟩
  · obtain ⟨w, hw⟩ := hbij.surjective (⟨0, f⟩ : SignedModel X)
    exact ⟨w, by simp [hw]⟩
  · have hZ2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases hZ2 (toModel X w).signPart with h0 | h1
    · refine Or.inl (hbij.injective ?_)
      rw [map_one]
      apply SignedModel.ext <;> simp [h0, hcfg]
    · refine Or.inr (hbij.injective ?_)
      rw [toModel_sign]
      apply SignedModel.ext <;> simp [h1, hcfg, modelSign]
  · rintro (rfl | rfl)
    · simp [map_one, one_def]
    · simp [toModel_sign, modelSign]

/-! ## The concrete instance, the doubling data -/

/-- **Printed sentence** (`non_mf_groups_exist.tex:1538-1541`).

> This is injective, and its image consists of the affine matrices whose translation coordinates
> are all even, so `[Γ̄ : α(Γ̄)] = 8`.  Translation `a` by the first standard basis vector lies
> outside `α(Γ̄)`.

At the literal model `gammaBar`/`conjD` (`Monsters/ExplicitLinearModel.lean`,
`Sofic/LiteralNonMFLinearWitness.lean`) that the rest of the development uses for `Γ̄` and `α`:
injectivity is `ExplicitLinearModel.conjD_injective`; the index-eight and escaping-translation
facts are exactly `AmenableTraceTheorem.manuscriptAffineCliffordHypotheses`.  (The even-translation
image description is proved at the *independent* matrix model `Monsters/AffineSL3Doubling.lean`,
which feeds the same index-eight computation via `Sofic/LiteralAffineRangeIndexEight.lean`:
`AffineSL3Doubling.mem_range_alpha_iff`.) -/
theorem manuscriptSentence_concreteInstanceDoubling :
    Function.Injective ExplicitLinearModel.conjD ∧
      AmenableTraceTheorem.PrintedAffineCliffordHypotheses :=
  ⟨ExplicitLinearModel.conjD_injective, AmenableTraceTheorem.manuscriptAffineCliffordHypotheses⟩

/-! ## `W` is a central extension of `C₂ ≀_X V` by `⟨ε⟩`

The remaining half of the printed sentence at `non_mf_groups_exist.tex:1421-1428` (`Killing ε
leaves F₂^{(X)} ≅ ⊕_X C₂, so Cl(X) is a central extension of ⊕_X C₂ by C₂, and W below is a
central extension of the permutational wreath product C₂ ≀_X V by ⟨ε⟩`) is built here at the
literal permutational wreath product `Algebra/PermutationalWreath.lean` already supplies for an
arbitrary lamp group: `Wreath K G X := Lamp K X ⋊[lampActionHom] G` for `[MulAction G X]`, with
`K := Multiplicative (ZMod 2)` giving the printed `C₂`.  `killWreath` is the "kill ε" map into
this lamp group, built exactly as `toModel`/`permMap` are built in `CliffordLampGroup.lean` (via
`PresentedGroup.toGroup`), and `lampAut_single` (proved there) makes its equivariance under `V`
immediate, so `killWreath` and the identity assemble via `SemidirectProduct.map` into a
homomorphism `W → C₂ ≀_X V` whose kernel is exactly `⟨ε⟩`. -/

noncomputable instance instDecidableEqCosets {Γ : Type} [Group Γ] (α : Γ →* Γ)
    (hα : Function.Injective α) : DecidableEq (Cosets α hα) :=
  Classical.decEq _

/-- A well-order on the coset space, exactly as `CliffordLamp.sign_ne_one` conjures one locally
(`IsWellOrder.linearOrder WellOrderingRel`): needed to invoke the `toModel`/`SignedModel` normal
form at this concrete `X = Cosets α hα`. -/
noncomputable instance instLinearOrderCosets {Γ : Type} [Group Γ] (α : Γ →* Γ)
    (hα : Function.Injective α) : LinearOrder (Cosets α hα) :=
  IsWellOrder.linearOrder WellOrderingRel

variable {Γ : Type} [Group Γ] (α : Γ →* Γ) (hα : Function.Injective α)

/-- The generator map into the permutational wreath lamp group: `ε ↦ 1`, `c_x ↦` the lamp with
the nontrivial value of `Multiplicative (ZMod 2)` at `x`. -/
noncomputable def killWreathGenerator :
    Generator (Cosets α hα) → Lamp (Multiplicative (ZMod 2)) (Cosets α hα) :=
  Sum.elim (fun _ ↦ 1) (fun x ↦ Lamp.single x (Multiplicative.ofAdd (1 : ZMod 2)))

theorem killWreathGenerator_kills :
    ∀ w ∈ relators (Cosets α hα),
      FreeGroup.lift (killWreathGenerator α hα) w = 1 := by
  intro w hw
  change IsRelator (Cosets α hα) w at hw
  cases hw with
  | sign_sq =>
      rw [map_pow, FreeGroup.lift_apply_of]
      show (1 : Lamp (Multiplicative (ZMod 2)) (Cosets α hα)) ^ 2 = 1
      rw [one_pow]
  | lamp_sq x =>
      rw [map_pow, FreeGroup.lift_apply_of]
      show (Lamp.single x (Multiplicative.ofAdd (1 : ZMod 2))) ^ 2 = 1
      have hgg : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
      rw [pow_two, ← Lamp.single_mul, hgg, Lamp.single_one]
  | sign_comm x =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      exact (Commute.one_left _).commutator_eq
  | @braiding x y h =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅Lamp.single x (Multiplicative.ofAdd (1 : ZMod 2)),
          Lamp.single y (Multiplicative.ofAdd (1 : ZMod 2))⁆ * (1 : Lamp _ _)⁻¹ = 1
      have hcomm : Commute (Lamp.single x (Multiplicative.ofAdd (1 : ZMod 2)))
          (Lamp.single y (Multiplicative.ofAdd (1 : ZMod 2))) :=
        Lamp.single_commute h (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1)
      rw [hcomm.commutator_eq, inv_one, mul_one]

/-- **The "kill ε" map into the permutational wreath lamp group.** -/
noncomputable def killWreath :
    CliffordLamp (Cosets α hα) →* Lamp (Multiplicative (ZMod 2)) (Cosets α hα) :=
  PresentedGroup.toGroup (killWreathGenerator_kills α hα)

@[simp] theorem killWreath_sign :
    killWreath α hα (sign (Cosets α hα)) = 1 :=
  PresentedGroup.toGroup.of _

@[simp] theorem killWreath_lamp (x : Cosets α hα) :
    killWreath α hα (lamp (Cosets α hα) x) =
      Lamp.single x (Multiplicative.ofAdd (1 : ZMod 2)) :=
  PresentedGroup.toGroup.of _

/-- **`killWreath` is onto.**  Every finitely supported configuration is hit by a product of the
generators over its (finite) support. -/
theorem killWreath_surjective : Function.Surjective (killWreath α hα) := by
  classical
  have key : ∀ S : Finset (Cosets α hα), ∃ n : CliffordLamp (Cosets α hα),
      ∀ x, (killWreath α hα n).toFun x =
        if x ∈ S then Multiplicative.ofAdd (1 : ZMod 2) else 1 := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, fun x ↦ by rw [map_one]; simp⟩
    | @insert a S ha ih =>
        obtain ⟨n, hn⟩ := ih
        refine ⟨lamp (Cosets α hα) a * n, fun x ↦ ?_⟩
        rw [map_mul, killWreath_lamp]
        by_cases hxa : x = a
        · subst hxa
          rw [Lamp.mul_apply, Lamp.single_apply_self, hn, if_neg ha, mul_one,
            if_pos (Finset.mem_insert_self x S)]
        · rw [Lamp.mul_apply, Lamp.single_apply_of_ne hxa, one_mul, hn]
          congr 1
          simp [Finset.mem_insert, hxa]
  intro f
  obtain ⟨n, hn⟩ := key f.2.toFinset
  refine ⟨n, Lamp.ext fun x ↦ ?_⟩
  rw [hn]
  have hK2 : ∀ z : Multiplicative (ZMod 2), z = 1 ∨ z = Multiplicative.ofAdd (1 : ZMod 2) := by
    decide
  by_cases hx : x ∈ f.2.toFinset
  · rw [if_pos hx]
    have hne : f.toFun x ≠ 1 := (Set.Finite.mem_toFinset _).mp hx
    rcases hK2 (f.toFun x) with h1 | hg
    · exact absurd h1 hne
    · exact hg.symm
  · rw [if_neg hx]
    have heq : f.toFun x = 1 := by
      by_contra hne
      exact hx ((Set.Finite.mem_toFinset _).mpr hne)
    exact heq.symm

/-- The "evaluate at site `x₀`" character, landing directly in `Multiplicative (ZMod 2)`: the
same generator map as `killWreathGenerator`, composed with evaluation at `x₀`. -/
noncomputable def evalSiteGenerator (x₀ : Cosets α hα) :
    Generator (Cosets α hα) → Multiplicative (ZMod 2) :=
  Sum.elim (fun _ ↦ 1) (fun x ↦ if x = x₀ then Multiplicative.ofAdd (1 : ZMod 2) else 1)

theorem evalSiteGenerator_kills (x₀ : Cosets α hα) :
    ∀ w ∈ relators (Cosets α hα),
      FreeGroup.lift (evalSiteGenerator α hα x₀) w = 1 := by
  intro w hw
  change IsRelator (Cosets α hα) w at hw
  cases hw with
  | sign_sq =>
      rw [map_pow, FreeGroup.lift_apply_of]
      show (1 : Multiplicative (ZMod 2)) ^ 2 = 1
      rw [one_pow]
  | lamp_sq x =>
      rw [map_pow, FreeGroup.lift_apply_of]
      show (if x = x₀ then Multiplicative.ofAdd (1 : ZMod 2) else 1) ^ 2 = 1
      split
      · have hgg : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
        rw [pow_two, hgg]
      · rw [one_pow]
  | sign_comm x =>
      rw [map_commutatorElement, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      exact (Commute.one_left _).commutator_eq
  | @braiding x y h =>
      rw [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of,
        FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
      show ⁅(if x = x₀ then Multiplicative.ofAdd (1 : ZMod 2) else 1),
          (if y = x₀ then Multiplicative.ofAdd (1 : ZMod 2) else 1)⁆ *
          (1 : Multiplicative (ZMod 2))⁻¹ = 1
      have hcomm : Commute (if x = x₀ then Multiplicative.ofAdd (1 : ZMod 2) else 1)
          (if y = x₀ then Multiplicative.ofAdd (1 : ZMod 2) else 1) := Commute.all _ _
      rw [hcomm.commutator_eq, inv_one, mul_one]

/-- The evaluation character at a site, as a homomorphism out of `Cl(X)`. -/
noncomputable def evalSite (x₀ : Cosets α hα) :
    CliffordLamp (Cosets α hα) →* Multiplicative (ZMod 2) :=
  PresentedGroup.toGroup (evalSiteGenerator_kills α hα x₀)

@[simp] theorem evalSite_sign (x₀ : Cosets α hα) :
    evalSite α hα x₀ (sign (Cosets α hα)) = 1 :=
  PresentedGroup.toGroup.of _

@[simp] theorem evalSite_lamp (x₀ x : Cosets α hα) :
    evalSite α hα x₀ (lamp (Cosets α hα) x) =
      if x = x₀ then Multiplicative.ofAdd (1 : ZMod 2) else 1 :=
  PresentedGroup.toGroup.of _

/-- **`killWreath`, evaluated at a site, is the site character.** -/
theorem evalHom_killWreath (x₀ : Cosets α hα) (n : CliffordLamp (Cosets α hα)) :
    evalHom x₀ (killWreath α hα n) = evalSite α hα x₀ n := by
  have h : (evalHom x₀).comp (killWreath α hα) = evalSite α hα x₀ := by
    apply PresentedGroup.ext
    intro j
    match j with
    | Sum.inl () =>
        show evalHom x₀ (killWreath α hα (sign (Cosets α hα))) =
          evalSite α hα x₀ (sign (Cosets α hα))
        rw [killWreath_sign, evalSite_sign]
        rfl
    | Sum.inr x =>
        show evalHom x₀ (killWreath α hα (lamp (Cosets α hα) x)) =
          evalSite α hα x₀ (lamp (Cosets α hα) x)
        rw [killWreath_lamp, evalSite_lamp]
        by_cases hx : x = x₀
        · rw [if_pos hx]
          show (Lamp.single x (Multiplicative.ofAdd (1 : ZMod 2))).toFun x₀ =
            Multiplicative.ofAdd (1 : ZMod 2)
          rw [hx, Lamp.single_apply_self]
        · rw [if_neg hx]
          show (Lamp.single x (Multiplicative.ofAdd (1 : ZMod 2))).toFun x₀ = 1
          rw [Lamp.single_apply_of_ne (Ne.symm hx)]
  exact DFunLike.congr_fun h n

/-- The site character factors through `toModel`'s `config` coordinate. -/
noncomputable def configHom :
    SignedModel (Cosets α hα) →* Multiplicative (Cosets α hα →₀ ZMod 2) :=
  MonoidHom.mk' (fun p ↦ Multiplicative.ofAdd p.config) (fun p q ↦ by simp [mul_def])

theorem evalSite_eq_config (x₀ : Cosets α hα) (n : CliffordLamp (Cosets α hα)) :
    evalSite α hα x₀ n =
      Multiplicative.ofAdd ((toModel (Cosets α hα) n).config x₀) := by
  have h : evalSite α hα x₀ =
      (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom (M := ZMod 2) x₀)).comp
        ((configHom α hα).comp (toModel (Cosets α hα))) := by
    apply PresentedGroup.ext
    intro j
    match j with
    | Sum.inl () =>
        show evalSite α hα x₀ (sign (Cosets α hα)) =
          (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom (M := ZMod 2) x₀))
            (configHom α hα (toModel (Cosets α hα) (sign (Cosets α hα))))
        rw [evalSite_sign, toModel_sign]
        show (1 : Multiplicative (ZMod 2)) =
          (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom (M := ZMod 2) x₀))
            (configHom α hα (modelSign (Cosets α hα)))
        simp [configHom, modelSign]
    | Sum.inr x =>
        show evalSite α hα x₀ (lamp (Cosets α hα) x) =
          (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom (M := ZMod 2) x₀))
            (configHom α hα (toModel (Cosets α hα) (lamp (Cosets α hα) x)))
        rw [evalSite_lamp, toModel_lamp]
        show (if x = x₀ then Multiplicative.ofAdd (1 : ZMod 2) else 1) =
          (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom (M := ZMod 2) x₀))
            (configHom α hα (modelLamp (Cosets α hα) x))
        by_cases hx : x = x₀
        · rw [if_pos hx]
          simp [configHom, modelLamp, toAdd_ofAdd, Finsupp.applyAddHom_apply, hx]
        · rw [if_neg hx]
          simp [configHom, modelLamp, toAdd_ofAdd, Finsupp.applyAddHom_apply,
            Finsupp.single_eq_of_ne (Ne.symm hx)]
  rw [h]
  show (AddMonoidHom.toMultiplicative (Finsupp.applyAddHom (M := ZMod 2) x₀))
      (configHom α hα (toModel (Cosets α hα) n)) = _
  simp [configHom]

/-- **The kernel of `killWreath` is exactly `⟨ε⟩`.** -/
theorem killWreath_ker_iff (n : CliffordLamp (Cosets α hα)) :
    killWreath α hα n = 1 ↔ n = 1 ∨ n = sign (Cosets α hα) := by
  have hcfg := manuscriptSentence_cliffordLampKillSignCentralExtension (X := Cosets α hα)
  rw [← hcfg.2.1 n]
  constructor
  · intro hker
    apply Finsupp.ext
    intro x₀
    have := evalHom_killWreath α hα x₀ n
    rw [hker, evalSite_eq_config] at this
    have h1 : evalHom x₀ (1 : Lamp (Multiplicative (ZMod 2)) (Cosets α hα)) = 1 := by
      simp [evalHom_apply]
    rw [h1] at this
    have hz : (toModel (Cosets α hα) n).config x₀ = 0 := by
      by_contra hne
      have hone : (toModel (Cosets α hα) n).config x₀ = 1 := by
        have hZ2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
        rcases hZ2 ((toModel (Cosets α hα) n).config x₀) with h0 | h1'
        · exact absurd h0 hne
        · exact h1'
      rw [hone] at this
      exact absurd this.symm (by decide)
    simpa using hz
  · intro hz
    apply Lamp.ext
    intro x₀
    have heval := evalHom_killWreath α hα x₀ n
    rw [evalSite_eq_config, hz] at heval
    show evalHom x₀ (killWreath α hα n) =
      (1 : Lamp (Multiplicative (ZMod 2)) (Cosets α hα)).toFun x₀
    rw [heval]
    simp

/-- **`killWreath` is `V`-equivariant.** -/
theorem killWreath_lampAction_comp (v : Vertical α hα) :
    (killWreath α hα).comp (lampAction α hα v).toMonoidHom =
      (lampActionHom v :
          MulAut (Lamp (Multiplicative (ZMod 2)) (Cosets α hα))).toMonoidHom.comp
        (killWreath α hα) := by
  apply PresentedGroup.ext
  intro j
  match j with
  | Sum.inl () =>
      show killWreath α hα (lampAction α hα v (sign (Cosets α hα))) =
        lampActionHom v (killWreath α hα (sign (Cosets α hα)))
      rw [lampAction_apply_sign, killWreath_sign, map_one]
  | Sum.inr x =>
      show killWreath α hα (lampAction α hα v (lamp (Cosets α hα) x)) =
        lampActionHom v (killWreath α hα (lamp (Cosets α hα) x))
      rw [lampAction_apply_lamp, killWreath_lamp, killWreath_lamp]
      exact (lampAut_single v x (Multiplicative.ofAdd (1 : ZMod 2))).symm

theorem killWreath_lampAction (v : Vertical α hα) (n : CliffordLamp (Cosets α hα)) :
    killWreath α hα (lampAction α hα v n) = lampActionHom v (killWreath α hα n) :=
  DFunLike.congr_fun (killWreath_lampAction_comp α hα v) n

/-- **The printed sentence.**  `W` maps onto the permutational wreath product `C₂ ≀_X V`, killing
exactly the central sign. -/
noncomputable def wreathMap :
    Ambient α hα →* Wreath (Multiplicative (ZMod 2)) (Vertical α hα) (Cosets α hα) :=
  SemidirectProduct.map (killWreath α hα) (MonoidHom.id (Vertical α hα))
    (fun v ↦ killWreath_lampAction_comp α hα v)

theorem wreathMap_surjective : Function.Surjective (wreathMap α hα) := by
  intro w
  obtain ⟨m, v⟩ := w
  obtain ⟨n, hn⟩ := killWreath_surjective α hα m
  exact ⟨⟨n, v⟩, SemidirectProduct.ext (by rw [wreathMap, SemidirectProduct.map_left]; exact hn)
    (by rw [wreathMap, SemidirectProduct.map_right]; rfl)⟩

theorem wreathMap_ker : (wreathMap α hα).ker = signSubgroup α hα := by
  ext w
  obtain ⟨n, v⟩ := w
  rw [MonoidHom.mem_ker, signSubgroup, mem_centralInvolutionSubgroup_iff]
  have hleft : (wreathMap α hα ⟨n, v⟩).left = killWreath α hα n := by
    rw [wreathMap, SemidirectProduct.map_left]
  have hright : (wreathMap α hα ⟨n, v⟩).right = v := by
    rw [wreathMap, SemidirectProduct.map_right]; rfl
  constructor
  · intro heq
    have hv : v = 1 := by
      have := congrArg SemidirectProduct.right heq
      rwa [hright, SemidirectProduct.one_right] at this
    have hn : killWreath α hα n = 1 := by
      have := congrArg SemidirectProduct.left heq
      rwa [hleft, SemidirectProduct.one_left] at this
    subst hv
    rcases (killWreath_ker_iff α hα n).mp hn with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (heq | heq)
    · rw [heq]; exact map_one _
    · rw [heq]
      apply SemidirectProduct.ext
      · rw [wreathMap, SemidirectProduct.map_left]
        show killWreath α hα (SemidirectProduct.inl (sign (Cosets α hα)) : Ambient α hα).left = 1
        rw [SemidirectProduct.left_inl, killWreath_sign]
      · rw [wreathMap, SemidirectProduct.map_right]
        show (MonoidHom.id (Vertical α hα))
            (SemidirectProduct.inl (sign (Cosets α hα)) : Ambient α hα).right = 1
        rw [SemidirectProduct.right_inl, map_one]

/-- **Printed sentence** (`non_mf_groups_exist.tex:1421-1428`, the `W`-level half).

> and `W` below is a central extension of the permutational wreath product `C₂ ≀_X V` by `⟨ε⟩`.

`⟨ε⟩` (`signSubgroup α hα`) is central (`signAmbient_central`) and `W ⧸ ⟨ε⟩` is isomorphic to the
permutational wreath product `Wreath (Multiplicative (ZMod 2)) V X`, `X = Cosets α hα`: exactly
the printed `C₂ ≀_X V`. -/
theorem manuscriptSentence_wCentralExtensionOfWreath :
    (∀ g : Ambient α hα, Commute (signAmbient α hα) g) ∧
      Nonempty (Ambient α hα ⧸ signSubgroup α hα ≃*
        Wreath (Multiplicative (ZMod 2)) (Vertical α hα) (Cosets α hα)) := by
  refine ⟨signAmbient_central α hα, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq (wreathMap_ker α hα)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective (wreathMap α hα) (wreathMap_surjective α hα))

end

end AmenableTraceSentencesB
end GroupApproximation

open GroupApproximation
open GroupApproximation.AmenableTraceSentencesB

#audit_axioms manuscriptSentence_rootLampCentralizesFixesCoset
#audit_axioms manuscriptSentence_distinctInvolutionsCommutatorSign
#audit_axioms manuscriptSentence_defectFactorization
#audit_axioms manuscriptSentence_signSubgroupCentralNormalFiniteHasT
#audit_axioms manuscriptSentence_cliffordLampKillSignCentralExtension
#audit_axioms manuscriptSentence_concreteInstanceDoubling
#audit_axioms manuscriptSentence_wCentralExtensionOfWreath
