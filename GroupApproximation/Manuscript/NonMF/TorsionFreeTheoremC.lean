import GroupApproximation.Manuscript.NonMF.FournierFacioInput
import GroupApproximation.Manuscript.NonMF.Saturation
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# `lem:simple-in-defect` and Theorem C (`thm:torsion-free`)

`non_mf_groups_exist.tex`, Section "A torsion-free group with full MF radical".

This module carries three printed items and nothing else.

## 1.  The paragraph "Put `Γ = π(P)`, `t = π(u₁)`, `J = t⁻¹π(S)t`"

> Since `S` commutes with `P₁ = u₁Pu₁⁻¹`, the subgroup `J` centralizes `Γ`, and
> `tΓt⁻¹ = π(P₁) ≤ Γ`, so `t ∈ Comp_{G₀}(Γ)`.  Moreover `tJt⁻¹ = π(S) ≤ Γ`, and
> `Γ` has property (T) as a quotient of `P`.

one theorem per printed clause: `centralizes_core`, `t_mem_compressionSet`,
`conj_conj_simple`, `simpleRange_le_coreRange`, `kazhdan_coreRange`.

## 2.  `lem:simple-in-defect`

> Let `ρ : G₀ → L` be a surjective homomorphism with `ρ(π(S)) ≠ 1`.  Then
> `ρ(π(S)) ≤ 𝔇_L(ρ(Γ))`.

`manuscriptSimpleInDefect`, proved by the printed argument: the printed defect
generator `[t_L c t_L⁻¹, ℓ]` with `c = t_L⁻¹ ρ(π(x)) t_L ∈ J_L` and
`ℓ = ρ(π(y)) ∈ ρ(π(S)) ≤ Γ_L` is the commutator `[ρ(π(x)), ρ(π(y))]`, so the
commutator subgroup of `ρ(π(S))` lies in the defect; and `S` is perfect
(`commutator_eq_top_of_infinite_simple`), so all of `ρ(π(S))` does.

The printed hypotheses — surjectivity of `ρ` and nontriviality of `ρ(π(S))` —
are carried in the named proposition `PrintedSimpleInDefect` so that the Lean
statement is the printed one; the containment itself
(`map_simpleRange_le_printedDefect`) needs neither, exactly as
`Manuscript.NonMF.SimpleInDefect` already records at the
`FournierFacioDefectData` interface.

## 3.  `thm:torsion-free` (Theorem C)

> There is a two-generated, finitely presented, torsion-free, acylindrically
> hyperbolic group `Q` with property (T) and `Rad_MF(Q) = Q`.  Every nontrivial
> quotient of `Q` also equals its own MF radical; in particular, no nontrivial
> quotient of `Q` is MF.

`manuscriptTorsionFreeFullMFRadical`, proved along the printed proof:
`N = ⟪π(S)⟫`, `lem:saturation` at `F = {1, π(s)}`, `ρ = r ∘ q`,
`ρ(π(S)) ≠ 1`, `lem:simple-in-defect`, normality of the defect plus a normal
generating set, property (T) for `L` and for `ρ(Γ)`, then
`thm:compression-criterion` with `K = L`, then `r = id`.

`lem:saturation` itself is the parallel hull-saturation lane's
`Manuscript.NonMF.TorsionFree.saturation`, imported and used directly; no
wiring stub is needed.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

open scoped commutatorElement

/-! ## 1.  `Γ`, `t` and `J` -/

variable (C : Configuration)

/-- **"`tΓt⁻¹ = π(P₁) ≤ Γ`, so `t ∈ Comp_{G₀}(Γ)`."**  `Comp_{G₀}(Γ)` is the
development's `compressionSet`. -/
theorem t_mem_compressionSet : C.t ∈ compressionSet C.core.range := by
  intro y hy
  rw [MonoidHom.mem_range] at hy
  obtain ⟨p, rfl⟩ := hy
  obtain ⟨q, hq⟩ := C.t_compresses p
  exact MonoidHom.mem_range.mpr ⟨q, hq.symm⟩

/-- **"the subgroup `J` centralizes `Γ`"**, in element form: every element
`t⁻¹π(x)t` of `J = t⁻¹π(S)t` commutes with every element `π(p)` of `Γ`.  The
printed reason is `[S, P₁] = 1`. -/
theorem centralizes_core (x : C.Simple) (p : C.Core) :
    Commute (C.t⁻¹ * C.simple x * C.t) (C.core p) := by
  show (C.t⁻¹ * C.simple x * C.t) * C.core p
    = C.core p * (C.t⁻¹ * C.simple x * C.t)
  have h := (C.simple_commute_conj x p).eq
  calc (C.t⁻¹ * C.simple x * C.t) * C.core p
      = C.t⁻¹ * (C.simple x * (C.t * C.core p * C.t⁻¹)) * C.t := by group
    _ = C.t⁻¹ * ((C.t * C.core p * C.t⁻¹) * C.simple x) * C.t := by rw [h]
    _ = C.core p * (C.t⁻¹ * C.simple x * C.t) := by group

/-- **"`tJt⁻¹ = π(S)`"**, in element form. -/
theorem conj_conj_simple (x : C.Simple) :
    C.t * (C.t⁻¹ * C.simple x * C.t) * C.t⁻¹ = C.simple x := by
  group

/-- **"`π(S) ≤ Γ`"**. -/
theorem simpleRange_le_coreRange : C.simple.range ≤ C.core.range := by
  rintro y hy
  rw [MonoidHom.mem_range] at hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨p, hp⟩ := C.core_mem_of_simple x
  exact MonoidHom.mem_range.mpr ⟨p, hp.symm⟩

/-- **"`Γ` has property (T) as a quotient of `P`."** -/
theorem kazhdan_coreRange : HasKazhdanPropertyT.{0, 0} ↥C.core.range :=
  HasKazhdanPropertyT.of_surjective C.core.rangeRestrict
    C.core.rangeRestrict_surjective C.kazhdanCore

/-! ## 2.  `lem:simple-in-defect` -/

section SimpleInDefect

variable {L : Type} [Group L] (rho : C.Ambient →* L)

/-- `t_L = ρ(t)` compresses `Γ_L = ρ(Γ)`: the first sentence of the printed
proof. -/
theorem map_t_mem_compressionSet :
    rho C.t ∈ compressionSet (C.core.range.map rho) := by
  intro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  rw [MonoidHom.mem_range] at hz
  obtain ⟨p, rfl⟩ := hz
  obtain ⟨q, hq⟩ := C.t_compresses p
  refine Subgroup.mem_map.mpr ⟨C.core q, MonoidHom.mem_range.mpr ⟨q, rfl⟩, ?_⟩
  rw [← hq]
  simp

/-- `J_L = ρ(J)` centralizes `Γ_L = ρ(Γ)`: the second sentence of the printed
proof. -/
theorem map_centralizes_core (x : C.Simple) :
    ∀ δ ∈ C.core.range.map rho,
      Commute ((rho C.t)⁻¹ * rho (C.simple x) * rho C.t) δ := by
  intro δ hδ
  rw [Subgroup.mem_map] at hδ
  obtain ⟨z, hz, rfl⟩ := hδ
  rw [MonoidHom.mem_range] at hz
  obtain ⟨p, rfl⟩ := hz
  have h := (centralizes_core C x p).map rho
  simpa using h

/-- The printed defect generator, computed: for `c = t_L⁻¹ρ(π(x))t_L ∈ J_L` and
`ℓ = ρ(π(y)) ∈ ρ(π(S)) ≤ Γ_L`, the generator `[t_L c t_L⁻¹, ℓ]` is the
commutator `[ρ(π(x)), ρ(π(y))]`. -/
theorem commutator_mem_printedDefect (x y : C.Simple) :
    ⁅rho (C.simple x), rho (C.simple y)⁆ ∈
      OneSidedMFRadical.printedDefect (C.core.range.map rho) := by
  have hy : rho (C.simple y) ∈ C.core.range.map rho := by
    obtain ⟨p, hp⟩ := C.core_mem_of_simple y
    refine Subgroup.mem_map.mpr ⟨C.core p, MonoidHom.mem_range.mpr ⟨p, rfl⟩, ?_⟩
    rw [← hp]
  have hkey := OneSidedMFRadical.printedDefect_generator_mem
    (C.core.range.map rho) (u := rho C.t)
    (c := (rho C.t)⁻¹ * rho (C.simple x) * rho C.t)
    (ℓ := rho (C.simple y))
    (map_t_mem_compressionSet C rho) (map_centralizes_core C rho x) hy
  have hrw : rho C.t * ((rho C.t)⁻¹ * rho (C.simple x) * rho C.t) *
      (rho C.t)⁻¹ = rho (C.simple x) := by group
  rwa [hrw] at hkey

/-- **The containment of `lem:simple-in-defect`.**  `S` is perfect, so the
commutator subgroup of `ρ(π(S))` is all of it, and the previous theorem puts
every commutator in the defect.

Neither surjectivity of `ρ` nor nontriviality of `ρ(π(S))` is used; both are
retained in `PrintedSimpleInDefect` below so that the printed statement is
formalized with its printed hypotheses. -/
theorem map_simpleRange_le_printedDefect :
    C.simple.range.map rho ≤
      OneSidedMFRadical.printedDefect (C.core.range.map rho) := by
  have hperf : commutator C.Simple = ⊤ :=
    commutator_eq_top_of_infinite_simple C.Simple
  have hsub : commutator C.Simple ≤
      (OneSidedMFRadical.printedDefect (C.core.range.map rho)).comap
        (rho.comp C.simple) := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro w ⟨a, b, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.coe_comp,
      Function.comp_apply, map_commutatorElement]
    exact commutator_mem_printedDefect C rho a b
  intro g hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨z, hz, rfl⟩ := hg
  rw [MonoidHom.mem_range] at hz
  obtain ⟨x, rfl⟩ := hz
  exact hsub (by rw [hperf]; exact Subgroup.mem_top x)

end SimpleInDefect

/-- **`lem:simple-in-defect`, with its printed hypotheses.**

> Let `ρ : G₀ → L` be a surjective homomorphism with `ρ(π(S)) ≠ 1`.  Then
> `ρ(π(S)) ≤ 𝔇_L(ρ(Γ))`. -/
def PrintedSimpleInDefect : Prop :=
  ∀ (cfg : Configuration) (L : Type) (_ : Group L) (rho : cfg.Ambient →* L),
    Function.Surjective rho → cfg.simple.range.map rho ≠ ⊥ →
      cfg.simple.range.map rho ≤
        OneSidedMFRadical.printedDefect (cfg.core.range.map rho)

/-- `lem:simple-in-defect`, proved. -/
theorem manuscriptSimpleInDefect : PrintedSimpleInDefect := by
  intro cfg L _ rho _ _
  exact map_simpleRange_le_printedDefect cfg rho

/-! ## 3.  The proof of `thm:torsion-free` -/

/-- **"the normal closure of `ρ(π(S))` in `L` is `ρ(N) = L`; as `L ≠ 1`, this
forces `ρ(π(S)) ≠ 1`."** -/
theorem map_simpleRange_ne_bot {L : Type} [Group L] [Nontrivial L]
    (rho : C.Ambient →* L)
    (hgen : (Subgroup.normalClosure (↑C.simple.range : Set C.Ambient)).map rho
      = ⊤) : C.simple.range.map rho ≠ ⊥ := by
  intro hbot
  have hle : Subgroup.normalClosure (↑C.simple.range : Set C.Ambient) ≤
      rho.ker := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    have hy' : y ∈ C.simple.range := hy
    have hmem : rho y ∈ C.simple.range.map rho :=
      Subgroup.mem_map_of_mem rho hy'
    rw [hbot, Subgroup.mem_bot] at hmem
    exact MonoidHom.mem_ker.mpr hmem
  have hmapbot :
      (Subgroup.normalClosure (↑C.simple.range : Set C.Ambient)).map rho = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_map] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact MonoidHom.mem_ker.mp (hle hw)
  rw [hgen] at hmapbot
  obtain ⟨x, hx⟩ := exists_ne (1 : L)
  apply hx
  have hmem : x ∈ (⊤ : Subgroup L) := Subgroup.mem_top x
  rw [hmapbot, Subgroup.mem_bot] at hmem
  exact hmem

/-- **The body of the printed proof of `thm:torsion-free`.**

For a surjection `ρ : G₀ → L` onto a nontrivial group under which the normal
closure of `π(S)` maps onto `L`:

* `ρ(π(S)) ≠ 1`;
* `lem:simple-in-defect` puts `ρ(π(S))` in `𝔇_L(ρ(Γ))`;
* `𝔇_L(ρ(Γ))` is normal and contains a normal generating set of `L`, so it
  equals `L`;
* `L` has property (T) as a quotient of `G₀`, and `ρ(Γ)` has property (T) as a
  quotient of `Γ`;
* `thm:compression-criterion` with the subgroup `ρ(Γ)` and `K = L` gives
  `Rad_MF(L) = L`. -/
theorem coronaMFResidual_eq_top_of_normallyGenerating
    {L : Type} [Group L] [Countable L] [Nontrivial L]
    (rho : C.Ambient →* L) (hrho : Function.Surjective rho)
    (hgen : (Subgroup.normalClosure (↑C.simple.range : Set C.Ambient)).map rho
      = ⊤) : manuscriptCoronaMFResidual L = ⊤ := by
  have hSne : C.simple.range.map rho ≠ ⊥ := map_simpleRange_ne_bot C rho hgen
  have hcontain : C.simple.range.map rho ≤
      OneSidedMFRadical.printedDefect (C.core.range.map rho) :=
    manuscriptSimpleInDefect C L inferInstance rho hrho hSne
  have hNle : Subgroup.normalClosure (↑C.simple.range : Set C.Ambient) ≤
      (OneSidedMFRadical.printedDefect (C.core.range.map rho)).comap rho := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    have hy' : y ∈ C.simple.range := hy
    exact hcontain (Subgroup.mem_map_of_mem rho hy')
  have hTtop : OneSidedMFRadical.printedDefect (C.core.range.map rho) = ⊤ := by
    refine top_unique ?_
    rw [← hgen]
    exact Subgroup.map_le_iff_le_comap.mpr hNle
  have hGammaT : HasKazhdanPropertyT.{0, 0} ↥(C.core.range.map rho) := by
    rw [← MonoidHom.range_comp]
    exact HasKazhdanPropertyT.of_surjective (rho.comp C.core).rangeRestrict
      (rho.comp C.core).rangeRestrict_surjective C.kazhdanCore
  have hLT : HasKazhdanPropertyT.{0, 0} L :=
    HasKazhdanPropertyT.of_surjective rho hrho C.kazhdanAmbient
  obtain ⟨-, -, hsat⟩ :=
    OneSidedMFRadical.manuscriptOneSidedCompressionCriterion L
      (C.core.range.map rho) hGammaT
  exact hsat hLT hTtop

/-- **`thm:torsion-free` (Theorem C), exactly as printed.**

There is a two-generated, finitely presented, torsion-free, acylindrically
hyperbolic group `Q` with property (T) and `Rad_MF(Q) = Q`; every nontrivial
quotient of `Q` also equals its own MF radical; in particular no nontrivial
quotient of `Q` is MF.

Countability is a binder in the last clause because `IsCDEOperatorMF` consumes
it as an instance.  It is not a restriction: every quotient of `Q` is countable,
`Q` being finitely presented. -/
def PrintedTorsionFreeFullMFRadical : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      TorsionFree.IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
      manuscriptCoronaMFResidual Q = ⊤ ∧
      (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
        Nontrivial L → manuscriptCoronaMFResidual L = ⊤) ∧
      (∀ (L : Type) (_ : Group L) (_ : Countable L) (r : Q →* L),
        Function.Surjective r → Nontrivial L → ¬ IsCDEOperatorMF L)

/-- **Theorem C, proved along the printed proof.** -/
theorem manuscriptTorsionFreeFullMFRadical : PrintedTorsionFreeFullMFRadical := by
  obtain ⟨cfg⟩ := exists_configuration
  haveI : Countable cfg.Ambient := cfg.countableAmbient
  obtain ⟨s, hs⟩ := exists_ne (1 : cfg.Simple)
  have hsne : cfg.simple s ≠ 1 := by
    intro h
    apply hs
    apply cfg.simple_injective
    rw [h, map_one]
  -- `N`, the normal closure of `π(S)` in `G₀`, is nontrivial.
  have hNne : Subgroup.normalClosure (↑cfg.simple.range : Set cfg.Ambient) ≠ ⊥ := by
    intro hbot
    apply hsne
    have hin : cfg.simple s ∈ (↑cfg.simple.range : Set cfg.Ambient) :=
      SetLike.mem_coe.mpr (MonoidHom.mem_range.mpr ⟨s, rfl⟩)
    have hmem := Subgroup.subset_normalClosure hin
    rw [hbot] at hmem
    simpa using hmem
  -- `lem:saturation` applied to `G₀`, `N` and `F = {1, π(s)}`.
  have hFin : ({1, cfg.simple s} : Set cfg.Ambient).Finite :=
    (Set.finite_singleton (cfg.simple s)).insert 1
  obtain ⟨SQ⟩ := TorsionFree.saturation cfg.torsionFreeAmbient
    (Subgroup.normalClosure (↑cfg.simple.range : Set cfg.Ambient)) hNne hFin
  haveI : Countable SQ.Q := SQ.surjective.countable
  -- "The group `Q` has property (T) as a quotient of `G₀`."
  have hQT : HasKazhdanPropertyT.{0, 0} SQ.Q :=
    HasKazhdanPropertyT.of_surjective SQ.q SQ.surjective cfg.kazhdanAmbient
  have hmem1 : (1 : cfg.Ambient) ∈ ({1, cfg.simple s} : Set cfg.Ambient) :=
    Set.mem_insert _ _
  have hmems : cfg.simple s ∈ ({1, cfg.simple s} : Set cfg.Ambient) :=
    Set.mem_insert_of_mem _ rfl
  have hqs : SQ.q (cfg.simple s) ≠ 1 := by
    intro hz
    apply hsne
    have h1 : SQ.q (cfg.simple s) = SQ.q 1 := by rw [hz, map_one]
    exact SQ.injOn hmems hmem1 h1
  haveI : Nontrivial SQ.Q := ⟨⟨SQ.q (cfg.simple s), 1, hqs⟩⟩
  -- The printed main step, for every nontrivial quotient `L` of `Q`.
  have hmain : ∀ (L : Type) (_ : Group L) (r : SQ.Q →* L),
      Function.Surjective r → Nontrivial L →
        manuscriptCoronaMFResidual L = ⊤ := by
    intro L instL r hr hLne
    letI := instL
    haveI := hLne
    haveI : Countable L := hr.countable
    refine coronaMFResidual_eq_top_of_normallyGenerating cfg (r.comp SQ.q)
      (hr.comp SQ.surjective) ?_
    rw [← Subgroup.map_map, SQ.map_eq_top]
    exact Subgroup.map_top_of_surjective r hr
  refine ⟨SQ.Q, inferInstance,
    ⟨SQ.generatorOne, SQ.generatorTwo, SQ.twoGenerated⟩, inferInstance,
    SQ.torsionFree, inferInstance, hQT, ?_, hmain, ?_⟩
  · -- "Taking `r` the identity gives `Rad_MF(Q) = Q`."
    exact hmain SQ.Q inferInstance (MonoidHom.id SQ.Q) Function.surjective_id
      inferInstance
  · -- "a nontrivial group equal to its own MF radical is not MF"
    intro L instL instCount r hr hLne hMF
    letI := instL
    haveI := instCount
    haveI := hLne
    have htop := hmain L instL r hr hLne
    have hbot : manuscriptCoronaMFResidual L = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp hMF
    obtain ⟨x, hx⟩ := exists_ne (1 : L)
    apply hx
    have hmem : x ∈ manuscriptCoronaMFResidual L := by
      rw [htop]
      exact Subgroup.mem_top x
    rw [hbot] at hmem
    simpa using hmem

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
