import GroupApproximation.Manuscript.NonMF.FournierFacioInput
import GroupApproximation.Manuscript.NonMF.HullFillCorrectedInputs
import GroupApproximation.Manuscript.NonMF.Saturation
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# The commutator-defect lemma and Theorem C (`thm:torsion-free`)

`non_mf_groups_exist.tex`, Section "A torsion-free group with full MF radical".

This module carries three items and nothing else: the printed configuration
paragraph, an auxiliary variant of `lem:commutator-in-defect` that needs less
input than the printed lemma (§2), and the printed Theorem C.

The printed `lem:commutator-in-defect` itself is formalized, by the printed
proof, in `Manuscript.NonMF.SimpleInDefect`
(`manuscriptLemmaCommutatorInDefect`).  That is the manuscript's route and it
is what the sentence census cites for tex 845-862.

## 1.  The compressed core and the free witness

The third factor `F₂` commutes with `P₁ = u₁Pu₁⁻¹`.  Hence its conjugate by
`t⁻¹` centralizes `Γ`, while `tΓt⁻¹ = π(P₁) ≤ Γ`.  Its image also lies in
`Γ`, which has property (T) as a quotient of `P`.

The corresponding theorems are `centralizes_core`, `t_mem_compressionSet`,
`conj_conj_witness`, `witnessRange_le_coreRange`, and `kazhdan_coreRange`.

## 2.  An auxiliary variant of `lem:commutator-in-defect`

The manuscript's lemma is the **`S`-version**:

> For every homomorphism `ρ : G₀ → Ḡ`, `ρ(S) ≤ 𝔇_Ḡ(ρ(Γ))`,

with `S = tJt⁻¹` and `J ≤ G₀` a finitely presented infinite simple group, and
its proof runs through perfectness: `[S̄,S̄] ≤ 𝔇` by the defect generators, and
`S̄` is perfect as a quotient of the perfect `S`, so `S̄ = [S̄,S̄] ≤ 𝔇`.  That
lemma, by that proof, is `SimpleInDefect.manuscriptLemmaCommutatorInDefect`,
over the printed configuration `PrintedFournierFacioData`; the perfectness step
is `commutator_simpleFactor_eq` (simple and nonabelian gives `⁅J,J⁆ = J`) and
`commutator_map_conjFactor_eq` (the image of a perfect subgroup is perfect).

What *this* module proves is a variant of the same shape, the **`F`-version**:

> For every homomorphism `ρ : G₀ → L`, `ρ(π([F,F])) ≤ 𝔇_L(ρ(Γ))`.

`manuscriptWitnessCommutatorInDefect`, with `ρ` an arbitrary homomorphism,
neither surjective nor assumed nontrivial on the witness.  For
`c = t_L⁻¹ρ(π(x))t_L` and `ℓ = ρ(π(y))`, the defect generator `[t_Lct_L⁻¹,ℓ]`
equals `[ρ(π(x)),ρ(π(y))]` (`map_defect_generator_mem`,
`commutator_mem_printedDefect`), so the image of `[F,F]` lies in the defect
(`map_map_witnessCommutator_le_printedDefect`, in the nested-image spelling).

The variant is kept because it costs less.  It needs no simple group: only the
free group `F₂` and one explicit nonidentity commutator to protect, so
`Configuration` carries a `Witness` group with a `distinguished` element and no
simplicity field at all, and the protected element is kernel-checkable in a way
a cited simple group is not (`freeWitnessCommutator_ne_one` is a computation in
`FreeGroup (Fin 2)`).  It is a strengthening of the printed lemma's role in the
argument, not a replacement for the printed lemma: §3's assembly happens to run
on it, and both feed `thm:torsion-free` identically, through a normal
generating set inside `𝔇_Ḡ(ρ(Γ))` giving `𝔇_Ḡ(ρ(Γ)) = Ḡ`.

Nothing here supersedes the manuscript.  Where a sentence of tex 845-862 is
graded, it is graded against the printed-route theorems in `SimpleInDefect`.

## 3.  `thm:torsion-free` (Theorem C)

> There is a two-generated, finitely presented, torsion-free, acylindrically
> hyperbolic group `Q` with property (T) and `Rad_MF(Q) = Q`.  Every nontrivial
> quotient of `Q` also equals its own MF radical; in particular, no nontrivial
> quotient of `Q` is MF.

`manuscriptTorsionFreeFullMFRadical`, with `TheoremC.LiteratureInputs` as a
leading binder and the printed statement as its conclusion, proved along the
proof with `N` the normal closure of the image of `[F₂,F₂]`, protecting one
explicit nonidentity commutator.  Normality of the defect and saturation give
the whole quotient; property (T) for `L` and for `ρ(Γ)` then feed
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

/-- Every conjugated witness element commutes with the compressed core. -/
theorem centralizes_core (x : C.Witness) (p : C.Core) :
    Commute (C.t⁻¹ * C.witness x * C.t) (C.core p) := by
  show (C.t⁻¹ * C.witness x * C.t) * C.core p
    = C.core p * (C.t⁻¹ * C.witness x * C.t)
  have h := (C.witness_commute_conj x p).eq
  calc (C.t⁻¹ * C.witness x * C.t) * C.core p
      = C.t⁻¹ * (C.witness x * (C.t * C.core p * C.t⁻¹)) * C.t := by group
    _ = C.t⁻¹ * ((C.t * C.core p * C.t⁻¹) * C.witness x) * C.t := by rw [h]
    _ = C.core p * (C.t⁻¹ * C.witness x * C.t) := by group

/-- Conjugating the witness element back recovers its image. -/
theorem conj_conj_witness (x : C.Witness) :
    C.t * (C.t⁻¹ * C.witness x * C.t) * C.t⁻¹ = C.witness x := by
  group

/-- The witness image lies in the core image. -/
theorem witnessRange_le_coreRange : C.witness.range ≤ C.core.range := by
  rintro y hy
  rw [MonoidHom.mem_range] at hy
  obtain ⟨x, rfl⟩ := hy
  obtain ⟨p, hp⟩ := C.core_mem_of_witness x
  exact MonoidHom.mem_range.mpr ⟨p, hp.symm⟩

/-- **"`Γ` has property (T) as a quotient of `P`."** -/
theorem kazhdan_coreRange : HasKazhdanPropertyT.{0, 0} ↥C.core.range :=
  HasKazhdanPropertyT.of_surjective C.core.rangeRestrict
    C.core.rangeRestrict_surjective C.kazhdanCore

/-! ## 2.  The witness commutator subgroup lies in the defect -/

section WitnessInDefect

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
theorem map_centralizes_core (x : C.Witness) :
    ∀ δ ∈ C.core.range.map rho,
      Commute ((rho C.t)⁻¹ * rho (C.witness x) * rho C.t) δ := by
  intro δ hδ
  rw [Subgroup.mem_map] at hδ
  obtain ⟨z, hz, rfl⟩ := hδ
  rw [MonoidHom.mem_range] at hz
  obtain ⟨p, rfl⟩ := hz
  have h := (centralizes_core C x p).map rho
  simpa using h

/-- Conjugating the mapped witness element back recovers its image. -/
theorem map_conj_conj_witness (x : C.Witness) :
    rho C.t * ((rho C.t)⁻¹ * rho (C.witness x) * rho C.t) * (rho C.t)⁻¹
      = rho (C.witness x) := by
  group

/-- The mapped witness image lies in the mapped core. -/
theorem map_witnessRange_le_coreRange :
    C.witness.range.map rho ≤ C.core.range.map rho :=
  Subgroup.map_mono (witnessRange_le_coreRange C)

/-- **"For `c ∈ J_L` and `ℓ ∈ Γ_L`, the commutator `[t_L c t_L⁻¹, ℓ]` lies in
`𝔇_L(Γ_L)` by `eq:intrinsic-defect`."**  The three inputs are exactly the three
clauses of the previous sentence. -/
theorem map_defect_generator_mem (x : C.Witness) {ℓ : L}
    (hℓ : ℓ ∈ C.core.range.map rho) :
    ⁅rho C.t * ((rho C.t)⁻¹ * rho (C.witness x) * rho C.t) * (rho C.t)⁻¹, ℓ⁆ ∈
      OneSidedMFRadical.printedDefect (C.core.range.map rho) :=
  OneSidedMFRadical.printedDefect_generator_mem (C.core.range.map rho)
    (map_t_mem_compressionSet C rho) (map_centralizes_core C rho x) hℓ

/-- The printed defect generator, computed: for `c = t_L⁻¹ρ(π(x))t_L ∈ J_L` and
`ℓ = ρ(π(y))` in the mapped witness image, the generator `[t_L c t_L⁻¹, ℓ]` is the
commutator `[ρ(π(x)), ρ(π(y))]`. -/
theorem commutator_mem_printedDefect (x y : C.Witness) :
    ⁅rho (C.witness x), rho (C.witness y)⁆ ∈
      OneSidedMFRadical.printedDefect (C.core.range.map rho) := by
  have hy : rho (C.witness y) ∈ C.core.range.map rho := by
    obtain ⟨p, hp⟩ := C.core_mem_of_witness y
    refine Subgroup.mem_map.mpr ⟨C.core p, MonoidHom.mem_range.mpr ⟨p, rfl⟩, ?_⟩
    rw [← hp]
  have hkey := OneSidedMFRadical.printedDefect_generator_mem
    (C.core.range.map rho) (u := rho C.t)
    (c := (rho C.t)⁻¹ * rho (C.witness x) * rho C.t)
    (ℓ := rho (C.witness y))
    (map_t_mem_compressionSet C rho) (map_centralizes_core C rho x) hy
  have hrw : rho C.t * ((rho C.t)⁻¹ * rho (C.witness x) * rho C.t) *
      (rho C.t)⁻¹ = rho (C.witness x) := by group
  rwa [hrw] at hkey

/-- The commutator subgroup of the mapped witness image lies in the defect.  It
is generated by the
commutators just placed in the defect. -/
theorem commutator_le_printedDefect :
    ⁅C.witness.range.map rho, C.witness.range.map rho⁆ ≤
      OneSidedMFRadical.printedDefect (C.core.range.map rho) := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  rw [Subgroup.mem_map] at hg hh
  obtain ⟨u, hu, rfl⟩ := hg
  obtain ⟨v, hv, rfl⟩ := hh
  rw [MonoidHom.mem_range] at hu hv
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨y, rfl⟩ := hv
  exact commutator_mem_printedDefect C rho x y

/-- **`lem:commutator-in-defect`**, with the two maps composed:
`ρ(π([F,F]))` written as the image of `[F,F]` under `ρ ∘ π`. -/
theorem map_witnessCommutator_le_printedDefect :
    (commutator C.Witness).map (rho.comp C.witness) ≤
      OneSidedMFRadical.printedDefect (C.core.range.map rho) := by
  have hsub : commutator C.Witness ≤
      (OneSidedMFRadical.printedDefect (C.core.range.map rho)).comap
        (rho.comp C.witness) := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro w ⟨a, b, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MonoidHom.coe_comp,
      Function.comp_apply, map_commutatorElement]
    exact commutator_mem_printedDefect C rho a b
  exact Subgroup.map_le_iff_le_comap.mpr hsub

/-- **`lem:commutator-in-defect`, in the printed spelling.**

> For every homomorphism `ρ : G₀ → L`, `ρ(π([F,F])) ≤ 𝔇_L(ρ(Γ))`.

`π([F,F])` is `(commutator W).map C.witness` and `ρ(-)` is a second
`Subgroup.map`, so the printed left-hand side is a nested image; the composed
form above is the same subgroup by `Subgroup.map_map`. -/
theorem map_map_witnessCommutator_le_printedDefect :
    ((commutator C.Witness).map C.witness).map rho ≤
      OneSidedMFRadical.printedDefect (C.core.range.map rho) := by
  rw [Subgroup.map_map]
  exact map_witnessCommutator_le_printedDefect C rho

end WitnessInDefect

/-- **The `F`-version of `lem:commutator-in-defect`, as one closed
proposition.**

> For every homomorphism `ρ : G₀ → L`, `ρ(π([F,F])) ≤ 𝔇_L(ρ(Γ))`.

The printed lemma is the `S`-version and is carried by
`SimpleInDefect.manuscriptLemmaCommutatorInDefect`; this is the free-witness
variant §2 describes.  Like the printed lemma it puts no hypothesis on `ρ`
beyond being a homomorphism, where an earlier draft's `lem:simple-in-defect`
needed surjectivity and a nontrivial image. -/
def PrintedWitnessCommutatorInDefect : Prop :=
  ∀ (cfg : Configuration) (L : Type) (_ : Group L) (rho : cfg.Ambient →* L),
    (commutator cfg.Witness).map (rho.comp cfg.witness) ≤
        OneSidedMFRadical.printedDefect (cfg.core.range.map rho)

/-- `lem:commutator-in-defect`, proved. -/
theorem manuscriptWitnessCommutatorInDefect :
    PrintedWitnessCommutatorInDefect := by
  intro cfg L _ rho
  exact map_witnessCommutator_le_printedDefect cfg rho

/-! ## 3.  The proof of `thm:torsion-free` -/

/-- **"The group `Q` has property (T) as a quotient of `G₀`"** — and, applied
again, **"the group `L` has property (T) as a quotient of `Q`"**: property (T)
passes to every quotient of the ambient group. -/
theorem kazhdan_of_ambient_quotient {Q : Type} [Group Q] (q : C.Ambient →* Q)
    (hq : Function.Surjective q) : HasKazhdanPropertyT.{0, 0} Q :=
  HasKazhdanPropertyT.of_surjective q hq C.kazhdanAmbient

/-- **"`ρ(Γ)` has property (T) as a quotient of `Γ`."** -/
theorem kazhdan_map_coreRange {L : Type} [Group L] (rho : C.Ambient →* L) :
    HasKazhdanPropertyT.{0, 0} ↥(C.core.range.map rho) := by
  rw [← MonoidHom.range_comp]
  exact HasKazhdanPropertyT.of_surjective (rho.comp C.core).rangeRestrict
    (rho.comp C.core).rangeRestrict_surjective C.kazhdanCore

/-- **"since `𝔇_L(ρ(Γ))` is normal in `L` and contains a normal generating set
of `L`, it equals `L`."**  The normal generating subgroup is the image of the
source commutator subgroup, which the preceding lemma places in the defect. -/
theorem printedDefect_eq_top_of_normallyGenerating {L : Type} [Group L]
    (rho : C.Ambient →* L)
    (hgen : (Subgroup.normalClosure
      (↑((commutator C.Witness).map C.witness) : Set C.Ambient)).map rho
      = ⊤) :
    OneSidedMFRadical.printedDefect (C.core.range.map rho) = ⊤ := by
  have hcontain := map_map_witnessCommutator_le_printedDefect C rho
  have hNle : Subgroup.normalClosure
      (↑((commutator C.Witness).map C.witness) : Set C.Ambient) ≤
      (OneSidedMFRadical.printedDefect (C.core.range.map rho)).comap rho := by
    apply Subgroup.normalClosure_le_normal
    intro y hy
    exact hcontain (Subgroup.mem_map_of_mem rho hy)
  refine top_unique ?_
  rw [← hgen]
  exact Subgroup.map_le_iff_le_comap.mpr hNle

/-- **The body of the printed proof of `thm:torsion-free`.**

For a surjection `ρ : G₀ → L` under which the saturated normal closure maps
onto `L`:

* the image of the source commutator subgroup lies in `𝔇_L(ρ(Γ))`;
* `𝔇_L(ρ(Γ))` is normal and contains a normal generating set of `L`, so it
  equals `L`;
* `L` has property (T) as a quotient of `G₀`, and `ρ(Γ)` has property (T) as a
  quotient of `Γ`;
* `thm:compression-criterion` with the subgroup `ρ(Γ)` and `K = L` gives
  `Rad_MF(L) = L`. -/
theorem coronaMFResidual_eq_top_of_normallyGenerating
    {L : Type} [Group L] [Countable L] [Nontrivial L]
    (rho : C.Ambient →* L) (hrho : Function.Surjective rho)
    (hgen : (Subgroup.normalClosure
      (↑((commutator C.Witness).map C.witness) : Set C.Ambient)).map rho
      = ⊤) : manuscriptCoronaMFResidual L = ⊤ := by
  have hTtop := printedDefect_eq_top_of_normallyGenerating C rho hgen
  have hGammaT := kazhdan_map_coreRange C rho
  have hLT : HasKazhdanPropertyT.{0, 0} L :=
    kazhdan_of_ambient_quotient C rho hrho
  obtain ⟨-, -, hsat⟩ :=
    OneSidedMFRadical.manuscriptOneSidedCompressionCriterion L
      (C.core.range.map rho) hGammaT
  exact hsat hLT hTtop

/-- The normal closure of the image of the witness commutator subgroup is
nontrivial because it contains the protected commutator. -/
theorem witnessCommutatorNormalClosure_ne_bot :
    Subgroup.normalClosure
      (↑((commutator C.Witness).map C.witness) : Set C.Ambient) ≠ ⊥ := by
  intro hbot
  apply C.distinguished_image_ne_one
  have hin : C.witness C.distinguished ∈
      (↑((commutator C.Witness).map C.witness) : Set C.Ambient) :=
    SetLike.mem_coe.mpr
      (Subgroup.mem_map_of_mem C.witness C.distinguished_mem_commutator)
  have hmem := Subgroup.subset_normalClosure hin
  rw [hbot] at hmem
  simpa using hmem

/-- **`thm:torsion-free` (Theorem C), exactly as printed.**

There is a two-generated, finitely presented, torsion-free, acylindrically
hyperbolic group `Q` with property (T) and `Rad_MF(Q) = Q`; every nontrivial
quotient of `Q` also equals its own MF radical; in particular no nontrivial
quotient of `Q` is MF.

The last clause uses the countability-free operator-MF predicate.  Every
nontrivial quotient is obstructed without adding a countability binder to the
statement. -/
def PrintedTorsionFreeFullMFRadical : Prop :=
  ∃ (Q : Type) (_ : Group Q),
    IsTwoGenerated Q ∧ Group.IsFinitelyPresented Q ∧ IsPowerTorsionFree Q ∧
      TorsionFree.IsAcylindricallyHyperbolic Q ∧ HasKazhdanPropertyT.{0, 0} Q ∧
      manuscriptCoronaMFResidual Q = ⊤ ∧
      (∀ (L : Type) (_ : Group L) (r : Q →* L), Function.Surjective r →
        Nontrivial L → manuscriptCoronaMFResidual L = ⊤) ∧
      (∀ (L : Type) (_ : Group L) (r : Q →* L),
        Function.Surjective r → Nontrivial L → ¬ IsOperatorMF L)

/-- **Theorem C, proved along the printed proof, from the paragraph's cited
inputs.**

The leading binders are exactly the cited inputs of the construction: the five
statements Fournier-Facio's paragraph cites and does not prove
(`TheoremC.LiteratureInputs`), and the two Hull cites
(`HullCorrectedInputs.HullInputsCorrected`).  The conclusion is the printed
statement of `thm:torsion-free` unchanged. -/
theorem manuscriptTorsionFreeFullMFRadical (I : LiteratureInputs)
    (hHull : HullCorrectedInputs.HullInputsCorrected.{0}) :
    PrintedTorsionFreeFullMFRadical := by
  obtain ⟨cfg⟩ := exists_configuration I
  haveI : Countable cfg.Ambient := cfg.countableAmbient
  let W : Subgroup cfg.Ambient := (commutator cfg.Witness).map cfg.witness
  -- `N`, the normal closure of the witness commutator image, is nontrivial.
  have hNne := witnessCommutatorNormalClosure_ne_bot cfg
  -- Protect the explicit nonidentity commutator during saturation.
  have hFin : ({1, cfg.witness cfg.distinguished} : Set cfg.Ambient).Finite :=
    (Set.finite_singleton (cfg.witness cfg.distinguished)).insert 1
  -- SINGLE CALL SITE for `TorsionFree.saturation`, which carries Hull's cited
  -- inputs as its leading hypothesis `hHull`.
  obtain ⟨SQ⟩ := TorsionFree.saturation hHull cfg.torsionFreeAmbient
    (Subgroup.normalClosure (↑W : Set cfg.Ambient)) hNne hFin
  haveI : Countable SQ.Q := SQ.surjective.countable
  -- "The group `Q` has property (T) as a quotient of `G₀`."
  have hQT : HasKazhdanPropertyT.{0, 0} SQ.Q :=
    HasKazhdanPropertyT.of_surjective SQ.q SQ.surjective cfg.kazhdanAmbient
  have hmem1 : (1 : cfg.Ambient) ∈
      ({1, cfg.witness cfg.distinguished} : Set cfg.Ambient) :=
    Set.mem_insert _ _
  have hmems : cfg.witness cfg.distinguished ∈
      ({1, cfg.witness cfg.distinguished} : Set cfg.Ambient) :=
    Set.mem_insert_of_mem _ rfl
  have hqs : SQ.q (cfg.witness cfg.distinguished) ≠ 1 := by
    intro hz
    apply cfg.distinguished_image_ne_one
    have h1 : SQ.q (cfg.witness cfg.distinguished) = SQ.q 1 := by
      rw [hz, map_one]
    exact SQ.injOn hmems hmem1 h1
  haveI : Nontrivial SQ.Q :=
    ⟨⟨SQ.q (cfg.witness cfg.distinguished), 1, hqs⟩⟩
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
    intro L instL r hr hLne hMF
    letI := instL
    haveI := hLne
    haveI : Countable L := hr.countable
    have htop := hmain L instL r hr hLne
    have hbot : manuscriptCoronaMFResidual L = ⊥ :=
      isCDEOperatorMF_iff_manuscriptCoronaMFResidual_eq_bot.mp
        ((isCDEOperatorMF_iff_isOperatorMF L).mpr hMF)
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
