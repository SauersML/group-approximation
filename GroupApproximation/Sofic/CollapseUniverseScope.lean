import GroupApproximation.Kazhdan.KazhdanUniverse
import GroupApproximation.Sofic.CollapseUniverseScopeDefs
import GroupApproximation.Sofic.InvolutionCollapseEndpoint
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.Set
import GroupApproximation.Algebra.CountableInstances

/-!
# `thm:collapse` at the manuscript's scope

`non_mf_groups_exist.tex`, `thm:collapse`, quantifies over **all** countable
groups.  The Lean endpoint
`GroupApproximation.Sofic.InvolutionCollapseEndpoint` proves it only for ambient
groups in `Type 0`: its `InvolutiveDischarge` section opens with
`variable {E : Type}` and its property-`(T)` hypothesis is spelled
`HasKazhdanPropertyT.{0, 0}`.  The neighbouring radical wrappers — notably
`ManuscriptExactWrappers.manuscriptRadicalReductionToQuotient` — are stated at
`Type u`, so the collapse theorem does not compose with them at face value.
This is audit item **COL.40**.

This module removes the restriction, honestly rather than by fiat.  The route is
the one the mathematics dictates:

1. **Descent.**  Every countable group `G : Type u` is isomorphic to a countable
   group in `Type 0`: an injection `G ↪ ℕ` realizes `G` as a group structure on
   a subtype of `ℕ` (`exists_typeZero_mulEquiv`).
2. **Property `(T)` follows.**  Kazhdan's property is a statement about a group
   *and* a representation universe.  The representation half is already handled
   in-repo by `HasKazhdanPropertyT.liftUniverse`
   (`GroupApproximation/Kazhdan/KazhdanUniverse.lean`), which sends
   `HasKazhdanPropertyT.{u, u}` to `HasKazhdanPropertyT.{u, 0}` through the GNS
   construction; the group half is `HasKazhdanPropertyT.of_mulEquiv`
   (`GroupApproximation/Kazhdan/Kazhdan.lean`), which already allows the two
   groups to sit in different universes.  Composing the two turns
   `HasKazhdanPropertyT.{u, u} ↥L` into `HasKazhdanPropertyT.{0, 0} ↥(L.map e)`.
3. **The collapse data transports** along the isomorphism
   (`CollapseUniverseScopeDefs`).
4. **The MF radical transports**, because it is already functorial for
   homomorphisms between groups in *different* universes:
   `map_actualCoronaMFResidual_le` in
   `GroupApproximation/Sofic/ActualCoronaMFRadical.lean`.

Nothing analytic is redone, and nothing is weakened: `collapse_typeZero_agrees`
recovers the endpoint's own `Type 0` theorem verbatim from the `Type u` one.
-/

namespace GroupApproximation
namespace CollapseUniverseScope

open scoped commutatorElement

universe u v

/- Quotients of countable groups are countable.  Proved once as
`GroupApproximation.CountableInstances.quotientCountable` and taken here with
the same `local` scope the mirrored copy had. -/
attribute [local instance] GroupApproximation.CountableInstances.quotientCountable

/-! ## Step 1: universe descent for countable groups -/

/-- **Every countable group is isomorphic to a countable group in `Type 0`.**
A countable type injects into `ℕ`, so the group is isomorphic — as a group — to
the transported group structure on the range of that injection, which is a
subtype of `ℕ` and therefore lives in the smallest universe.  This is the
countable analogue of Mathlib's `Finite.exists_type_univ_nonempty_mulEquiv`, and
it is the only content behind the claim that the universe-`0` restriction on
`thm:collapse` costs no mathematics. -/
theorem exists_typeZero_mulEquiv (G : Type u) [Group G] [Countable G] :
    ∃ (G₀ : Type) (_ : Group G₀) (_ : Countable G₀), Nonempty (G ≃* G₀) := by
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat G
  let e : G ≃ ↥(Set.range f) := Equiv.ofInjective f hf
  letI groupG₀ : Group ↥(Set.range f) := e.symm.group
  exact ⟨↥(Set.range f), groupG₀, inferInstance,
    ⟨MulEquiv.symm <| e.symm.mulEquiv⟩⟩

/-! ## Step 2: the `Type 0` definitions are the specializations of these -/

/-- At `Type 0` the universe-polymorphic witness predicate is literally the
endpoint's. -/
theorem isInvolutiveCompressionWitness_iff {E : Type} [Group E]
    (L : Subgroup E) (s k : E) :
    IsInvolutiveCompressionWitness L s k ↔
      InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness L s k :=
  Iff.rfl

/-- At `Type 0` the universe-polymorphic collapse set is literally the
endpoint's. -/
@[simp] theorem involutiveCollapseSet_eq {E : Type} [Group E] (L : Subgroup E)
    (s : E) :
    involutiveCollapseSet L s =
      InvolutionCollapseEndpoint.involutiveCollapseSet L s := rfl

/-- At `Type 0` the universe-polymorphic collapse defect is literally the
endpoint's. -/
@[simp] theorem involutiveCollapseDefect_eq {E : Type} [Group E] (L : Subgroup E)
    (s : E) :
    involutiveCollapseDefect L s =
      InvolutionCollapseEndpoint.involutiveCollapseDefect L s := rfl

/-! ## Step 3: the collapse theorem at the manuscript's scope -/

/-- **Unconditional collapse of involutive witnesses, over a countable ambient
group in any universe.**  This is the element-level statement of
`thm:collapse`: for a countable ambient group `E`, a subgroup `L` with property
`(T)`, a one-sided compressor `s` of `L`, and an involutive witness `k`, the
collapse commutator `⁅γ, k⁆` is invisible in every norm-matrix C\*-corona
representation of `E`.

The proof is the transfer described in the module docstring: replace `E` by an
isomorphic countable group in `Type 0`, run the endpoint theorem there, and
carry the conclusion back along the inverse isomorphism using functoriality of
the MF radical.  No analytic step is repeated and none is weakened. -/
theorem actualCoronaMFInvisible_of_involutiveWitness {E : Type u} [Group E]
    [Countable E] {L : Subgroup E}
    (hkazhdan : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    {k : E} (hk : IsInvolutiveCompressionWitness L s k)
    {γ : E} (hγ : γ ∈ L) :
    ActualCoronaMFInvisible ⁅γ, k⁆ := by
  obtain ⟨E₀, _groupE₀, _countE₀, ⟨e⟩⟩ := exists_typeZero_mulEquiv E
  -- Property `(T)` descends: first the representation universe, then the group.
  have hlift : HasKazhdanPropertyT.{u, 0} ↥L :=
    HasKazhdanPropertyT.liftUniverse hkazhdan
  have hT₀ : HasKazhdanPropertyT.{0, 0} ↥(L.map (e : E →* E₀)) :=
    HasKazhdanPropertyT.of_mulEquiv (e.subgroupMap L).symm hlift
  -- The group-theoretic collapse data transports.
  have hcomp₀ : ∀ g ∈ L.map (e : E →* E₀),
      e s * g * (e s)⁻¹ ∈ L.map (e : E →* E₀) :=
    compresses_map hcomp e
  have hk₀ : InvolutionCollapseEndpoint.IsInvolutiveCompressionWitness
      (L.map (e : E →* E₀)) (e s) (e k) := hk.map e
  have hγ₀ : e γ ∈ L.map (e : E →* E₀) :=
    Subgroup.mem_map_of_mem (e : E →* E₀) hγ
  -- The endpoint theorem applies verbatim to the `Type 0` model.
  have h₀ : ActualCoronaMFInvisible ⁅e γ, e k⁆ :=
    InvolutionCollapseEndpoint.actualCoronaMFInvisible_of_involutiveWitness
      hT₀ hcomp₀ hk₀ hγ₀
  have hmem₀ : ⁅e γ, e k⁆ ∈ actualCoronaMFResidual E₀ := h₀
  -- Functoriality of the radical carries the conclusion back.
  have hpush : (e.symm : E₀ →* E) ⁅e γ, e k⁆ ∈ actualCoronaMFResidual E :=
    map_actualCoronaMFResidual_le (e.symm : E₀ →* E)
      ⟨⁅e γ, e k⁆, hmem₀, rfl⟩
  have hrw : (e.symm : E₀ →* E) ⁅e γ, e k⁆ = ⁅γ, k⁆ := by simp
  rw [hrw] at hpush
  exact hpush

/-- **`thm:collapse` at the manuscript's scope.**  For a countable ambient group
in *any* universe, the involutive collapse defect of a Kazhdan subgroup with a
one-sided compressor lies in the literal MF radical. -/
theorem involutiveCollapseDefect_le_actualCoronaMFResidual {E : Type u}
    [Group E] [Countable E] {L : Subgroup E}
    (hkazhdan : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) :
    involutiveCollapseDefect L s ≤ actualCoronaMFResidual E := by
  rw [involutiveCollapseDefect]
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨k, hk, γ, hγ, rfl⟩
  exact actualCoronaMFInvisible_of_involutiveWitness hkazhdan hcomp hk hγ

/-- **The generalization is conservative.**  Specializing the `Type u` collapse
theorem at `u = 0` returns the endpoint's own theorem, statement for statement:
the `Type 0` defect, the `Type 0` radical, and `HasKazhdanPropertyT.{0, 0}`.
Nothing was traded away to widen the scope. -/
theorem collapse_typeZero_agrees {E : Type} [Group E] [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{0, 0} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) :
    InvolutionCollapseEndpoint.involutiveCollapseDefect L s ≤
      actualCoronaMFResidual E := by
  rw [← involutiveCollapseDefect_eq]
  exact involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp

/-! ## Step 4: the radical reduction at the manuscript's scope -/

/-- **Reduction of the universal MF quotient, at any universe.**
Unconditionally, the MF radical of a countable ambient group is the full
preimage of the radical of the involutive defect quotient. -/
theorem actualCoronaMFResidual_eq_comap_involutive_quotient {E : Type u}
    [Group E] [Countable E] {L : Subgroup E}
    (hkazhdan : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L) :
    actualCoronaMFResidual E =
      (actualCoronaMFResidual (E ⧸ involutiveCollapseDefect L s)).comap
        (QuotientGroup.mk' (involutiveCollapseDefect L s)) :=
  TorsionCompressionCollapse.actualCoronaMFResidual_eq_comap_quotient _
    (involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp)

/-- **The exact MF radical, at any universe.**  When the involutive defect
quotient is itself MF, the literal MF radical of the ambient group is computed
exactly by the involutive collapse defect. -/
theorem actualCoronaMFResidual_eq_involutiveCollapseDefect {E : Type u}
    [Group E] [Countable E] {L : Subgroup E}
    (hkazhdan : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hquot : IsCDEOperatorMF (E ⧸ involutiveCollapseDefect L s)) :
    actualCoronaMFResidual E = involutiveCollapseDefect L s :=
  actualCoronaMFResidual_eq_of_le_and_quotient_isCDEOperatorMF
    (involutiveCollapseDefect L s)
    (involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp)
    hquot

/-! ## Step 5: defect saturation at the manuscript's scope

`thm:saturation` and `cor:collapsequot` are both stated "in the setting of
Theorem `thm:collapse`", so they inherit its quantification over all countable
groups.  `Sofic/DefectSaturation.lean` proves them for `E : Type` against
`HasKazhdanPropertyT.{0, 0}`; the four theorems below are those statements at
`Type u`, with the target group of a homomorphism allowed its own universe as
the printed "countable MF group" does.  Each proof is the `Type 0` proof
verbatim: nothing here needs the descent of Step 3, because the only inputs are
`involutiveCollapseDefect_le_actualCoronaMFResidual` (which already carries it)
and the two radical facts `map_actualCoronaMFResidual_le` and
`isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot`, both of which are
universe-polymorphic already. -/

/-- **Every homomorphism to a countable operator-MF group kills the collapse
defect**, for a countable ambient group in any universe and a target group in
any universe. -/
theorem involutiveCollapseDefect_le_ker_of_isCDEOperatorMF {E : Type u}
    [Group E] [Countable E] {L : Subgroup E}
    (hkazhdan : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    {Q : Type v} [Group Q] [Countable Q]
    (f : E →* Q) (hQ : IsCDEOperatorMF Q) :
    involutiveCollapseDefect L s ≤ f.ker := by
  refine le_trans
    (involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp) ?_
  intro x hx
  have hfx : f x ∈ actualCoronaMFResidual Q :=
    map_actualCoronaMFResidual_le f ⟨x, hx, rfl⟩
  have hbot : actualCoronaMFResidual Q = ⊥ :=
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hQ
  rw [hbot] at hfx
  exact Subgroup.mem_bot.mp hfx

/-- **Saturation gives the full MF radical**, at any universe: a collapse
defect equal to the whole group forces the literal MF radical to be the whole
group. -/
theorem actualCoronaMFResidual_eq_top_of_saturated {E : Type u} [Group E]
    [Countable E] {L : Subgroup E}
    (hkazhdan : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hsat : involutiveCollapseDefect L s = ⊤) :
    actualCoronaMFResidual E = ⊤ := by
  refine top_unique ?_
  rw [← hsat]
  exact involutiveCollapseDefect_le_actualCoronaMFResidual hkazhdan hcomp

/-- **The approximation black hole**, at any universe: with a saturated defect
every homomorphism to a countable operator-MF group is trivial. -/
theorem map_eq_one_of_saturated {E : Type u} [Group E] [Countable E]
    {L : Subgroup E} (hkazhdan : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hsat : involutiveCollapseDefect L s = ⊤)
    {Q : Type v} [Group Q] [Countable Q]
    (f : E →* Q) (hQ : IsCDEOperatorMF Q) (x : E) : f x = 1 := by
  have hker := involutiveCollapseDefect_le_ker_of_isCDEOperatorMF
    hkazhdan hcomp f hQ
  have hx : x ∈ involutiveCollapseDefect L s := by
    rw [hsat]
    trivial
  exact hker hx

/-- A nontrivial countable group in any universe with a saturated involutive
collapse defect is not operator-MF. -/
theorem not_isCDEOperatorMF_of_saturated {E : Type u} [Group E] [Countable E]
    [Nontrivial E] {L : Subgroup E}
    (hkazhdan : HasKazhdanPropertyT.{u, u} ↥L)
    {s : E} (hcomp : ∀ γ ∈ L, s * γ * s⁻¹ ∈ L)
    (hsat : involutiveCollapseDefect L s = ⊤) :
    ¬ IsCDEOperatorMF E := by
  intro hMF
  have hbot : actualCoronaMFResidual E = ⊥ :=
    isCDEOperatorMF_iff_actualCoronaMFResidual_eq_bot.mp hMF
  have htop := actualCoronaMFResidual_eq_top_of_saturated hkazhdan hcomp
    hsat
  rw [htop] at hbot
  obtain ⟨x, y, hxy⟩ := exists_pair_ne E
  apply hxy
  have hx : x * y⁻¹ ∈ (⊤ : Subgroup E) := trivial
  rw [hbot] at hx
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hx)

/-! ## Closed manuscript forms

Drop-in replacements for the `Type 0` wrappers in
`GroupApproximation.Sofic.ManuscriptExactWrappers`, with every binder after the
colon as the zero-input gate requires. -/

/-- Closed form of the involutive collapse theorem **at the manuscript's
quantification**: for every countable group in every universe, the involutive
collapse defect of a Kazhdan subgroup with a one-sided compressor lies in the
literal MF radical.  Replaces
`ManuscriptExactWrappers.manuscriptInvolutiveCollapse`, whose `{H : Type}` and
`HasKazhdanPropertyT.{0, 0}` were narrower than `thm:collapse`. -/
theorem manuscriptInvolutiveCollapse :
    ∀ {H : Type u} [Group H] [Countable H]
      (L : Subgroup H), HasKazhdanPropertyT.{u, u} ↥L →
      ∀ (s : H), (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      involutiveCollapseDefect L s ≤ actualCoronaMFResidual H := by
  intro H _ _ L hT s hcomp
  exact involutiveCollapseDefect_le_actualCoronaMFResidual hT hcomp

/-- Closed form of the involutive-collapse data at the manuscript's
quantification: the witness predicate is literally the displayed three
conditions, and the involutive collapse defect is literally the normal closure
of the displayed commutator set, normal in the ambient group. -/
theorem manuscriptInvolutiveCollapsePattern :
    ∀ {H : Type u} [Group H] (L : Subgroup H) (s : H),
    (∀ k : H,
      IsInvolutiveCompressionWitness L s k ↔
        (k * k = 1 ∧ (∀ γ ∈ L, Commute (s * γ * s⁻¹) k) ∧
          (∀ γ₁ ∈ L, ∀ γ₂ ∈ L,
            Commute (γ₁ * k * γ₁⁻¹) (γ₂ * k * γ₂⁻¹)))) ∧
      involutiveCollapseDefect L s =
        Subgroup.normalClosure
          {x | ∃ k : H, IsInvolutiveCompressionWitness L s k ∧
            ∃ γ ∈ L, x = ⁅γ, k⁆} ∧
      (involutiveCollapseDefect L s).Normal := by
  intro H _ L s
  exact ⟨fun _ ↦ Iff.rfl, rfl, inferInstance⟩

/-- Closed form of the collapse radical reduction at the manuscript's
quantification: unconditionally the literal MF radical is the full preimage of
the radical of the collapse quotient, and it equals the collapse defect exactly
when the quotient is operator-MF. -/
theorem manuscriptCollapseRadicalReduction :
    ∀ {H : Type u} [Group H] [Countable H]
      (L : Subgroup H) (s : H),
      HasKazhdanPropertyT.{u, u} ↥L →
      (∀ γ ∈ L, s * γ * s⁻¹ ∈ L) →
      letI : Countable (H ⧸ involutiveCollapseDefect L s) :=
        Function.Surjective.countable
          (QuotientGroup.mk'_surjective (involutiveCollapseDefect L s))
      actualCoronaMFResidual H =
        (actualCoronaMFResidual (H ⧸ involutiveCollapseDefect L s)).comap
          (QuotientGroup.mk' (involutiveCollapseDefect L s)) ∧
      (IsCDEOperatorMF (H ⧸ involutiveCollapseDefect L s) →
        actualCoronaMFResidual H = involutiveCollapseDefect L s) := by
  intro H _ _ L s hT hcomp
  exact
    ⟨actualCoronaMFResidual_eq_comap_involutive_quotient hT hcomp,
      fun hquot ↦
        actualCoronaMFResidual_eq_involutiveCollapseDefect hT hcomp hquot⟩

end CollapseUniverseScope
end GroupApproximation
