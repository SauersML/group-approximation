import GroupApproximation.Manuscript.SimpleKazhdanSofic.MarkedLimitLEF
import GroupApproximation.Higman.Program
import GroupApproximation.Sofic.ContinuumMultiplicityCore
import GroupApproximation.Sofic.LEF
import GroupApproximation.Kazhdan.Kazhdan
import GroupApproximation.Meta.AxiomGuard
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# `cor:lef` and `cor:host` of `simple_kazhdan_sofic_group.tex`: statements and assemblies

`simple_kazhdan_sofic_group.tex` at origin/main 37551fd93, section "LEF groups" (tex l.312–409):

> **Corollary (`cor:lef`).** A finitely generated group is LEF if and only if it is a subgroup of
> an infinite, finitely generated, simple group with property (T) that is a limit of finite simple
> groups `SL_N(F₂)` in the space of marked groups, whose Cayley graphs form a family of expanders.
>
> **Corollary (`cor:host`).** Every countable LEF group is a subgroup of such a group. A set of
> finitely generated groups lies in one such group if and only if its members are LEF and represent
> countably many isomorphism classes. So one such group contains every recursively presented
> finitely generated LEF group, for instance every finitely presented residually finite group and
> every `G_Y` whose language is recursive.

## Spelling

* `IsLEFHost E` is "such a group". The marked limit and the expanders are MainAssembly's
  `IsMarkedLimit` and `IsExpanderFamily`. `SL_N(F₂)` is read up to reindexing by a finite type
  `κ ℓ`, so `thm:general`'s `SL_{3N}` enters as `κ ℓ = Fin 3 × Fin N`.
* "Subgroup of" means an injective homomorphism into the host.
* "Represent countably many isomorphism classes" means some countable family of groups contains
  an isomorphic copy of every member.
* "Recursively presented finitely generated" means `Group.FG` together with a
  `Higman.RecursivePresentation` (countable generators, r.e. word problem). Its docstring explains
  why this equals the textbook form.

## The proof

* l.329–330, "Limits of finite groups in the space of marked groups are LEF, and so are their
  subgroups": `printedMarkedLimitSubgroupsLEF`, through ct-two-ended's
  `printedMarkedLimitLEFStatement` and `isLEF_of_injective`.
* l.330–354, Part (i): a countable LEF group embeds in `[Δ,Δ]` for an infinite finitely generated
  LEF group `Δ`. This is the piece `LEFUltraproductEmbeddingStatement`.
* l.356–402, Parts (ii)–(iv): the lamplighter ring `R_Δ`, `thm:general`, and
  `[Δ,Δ] ≤ [Λ,Λ] ↪ G_Δ`. This is the piece `LEFLamplighterStatement`.
* l.404–407, the restricted direct sum: the piece `RestrictedSumLEFStatement`.
* l.407–408, "a countable group has countably many finitely generated subgroups":
  `lefFamily_countableClasses_of_host`, through `countable_fg_subgroups`.
* l.408–409, "There are countably many recursive presentations": the piece
  `RecursivePresentationClassesStatement`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

universe u

/-! ## Statements -/

/-- **The hosts of `cor:lef` and `cor:host`** (tex l.313–316): an infinite, finitely generated,
simple group with property (T) that is a limit, in the space of marked groups, of finite simple
groups `SL_N(F₂)` whose Cayley graphs form a family of expanders. -/
def IsLEFHost (E : Type) [Group E] : Prop :=
  Infinite E ∧ Group.FG E ∧ IsSimpleGroup E ∧ HasKazhdanPropertyT.{0, 0} E ∧
    ∃ (ι : Type) (s : ι → E) (κ : ℕ → Type) (_ : ∀ ℓ, Fintype (κ ℓ))
      (_ : ∀ ℓ, DecidableEq (κ ℓ)) (σ : ∀ ℓ, ι → Matrix.SpecialLinearGroup (κ ℓ) (ZMod 2)),
      (∀ ℓ, IsSimpleGroup (Matrix.SpecialLinearGroup (κ ℓ) (ZMod 2))) ∧ IsMarkedLimit s σ ∧
        IsExpanderFamily σ

/-- **`cor:lef`** (tex l.313–316). -/
def PrintedLEFSubgroupCharacterization : Prop :=
  ∀ (Γ : Type) [Group Γ], Group.FG Γ →
    (IsLEF Γ ↔ ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∃ f : Γ →* E, Function.Injective f)

/-- **`cor:host`, first statement** (tex l.320): every countable LEF group is a subgroup of such
a group. -/
def PrintedCountableLEFHost : Prop :=
  ∀ (Γ : Type) [Group Γ], Countable Γ → IsLEF Γ →
    ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∃ f : Γ →* E, Function.Injective f

/-- **`cor:host`, second statement** (tex l.320–322): a set of finitely generated groups lies in
one such group if and only if its members are LEF and represent countably many isomorphism
classes. -/
def PrintedLEFFamilyHost : Prop :=
  ∀ (ι : Type u) (G : ι → Type) [∀ i, Group (G i)], (∀ i, Group.FG (G i)) →
    ((∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∀ i, ∃ f : G i →* E, Function.Injective f) ↔
      (∀ i, IsLEF (G i)) ∧
        ∃ (J : Type) (_ : Countable J) (H : J → Type) (_ : ∀ j, Group (H j)),
          ∀ i, ∃ j, Nonempty (G i ≃* H j))

/-- **`cor:host`, last statement** (tex l.322–325): one such group contains every recursively
presented finitely generated LEF group. -/
def PrintedRecursivelyPresentedLEFHost : Prop :=
  ∃ (E : Type) (_ : Group E), IsLEFHost E ∧
    ∀ (Γ : Type) [Group Γ], Group.FG Γ → Nonempty (Higman.RecursivePresentation Γ) →
      IsLEF Γ → ∃ f : Γ →* E, Function.Injective f

/-- **Limits of finite groups in the space of marked groups are LEF, and so are their
subgroups** (tex l.329–330). -/
def PrintedMarkedLimitSubgroupsLEF : Prop :=
  ∀ (ι G : Type) [Group G] (s : ι → G) (H : ℕ → Type) [∀ ℓ, Group (H ℓ)] (σ : ∀ ℓ, ι → H ℓ),
    (∀ ℓ, Finite (H ℓ)) → IsMarkedLimit s σ → IsLEF G ∧ ∀ K : Subgroup G, IsLEF ↥K

/-! ## Pieces -/

/-- **Part (i)** (tex l.330–354): a countable LEF group `Γ` embeds in the commutator subgroup of an
infinite finitely generated LEF group `Δ`. Printed: `Δ = ⟨a, b⟩` inside an algebraic
ultraproduct of finite symmetric groups, with `γ_j ↦ w_j(a, b)`. -/
def LEFUltraproductEmbeddingStatement : Prop :=
  ∀ (Γ : Type) [Group Γ], Countable Γ → IsLEF Γ →
    ∃ (Δ : Type) (_ : Group Δ), Infinite Δ ∧ Group.FG Δ ∧ IsLEF Δ ∧
      ∃ f : Γ →* Δ, Function.Injective f ∧ ∀ γ, f γ ∈ commutator Δ

/-- **Parts (ii)–(iv)** (tex l.356–402): for an infinite finitely generated LEF group `Δ`, the
group `G_Δ = EL₃(LC(Ω,F₂) ⋊ Λ)` of the lamplighter action on `Ω = F₂^Δ` is such a group
(`thm:general`), and `[Δ,Δ] ≤ [Λ,Λ]` embeds in it. -/
def LEFLamplighterStatement : Prop :=
  ∀ (Δ : Type) [Group Δ], Infinite Δ → Group.FG Δ → IsLEF Δ →
    ∃ (E : Type) (_ : Group E), IsLEFHost E ∧ ∃ f : ↥(commutator Δ) →* E, Function.Injective f

/-- **The restricted direct sum** (tex l.404–407): countably many countable LEF groups embed in
one countable LEF group, "as finite subsets lie in finite products". -/
def RestrictedSumLEFStatement : Prop :=
  ∀ (J : Type) [Countable J] (H : J → Type) [∀ j, Group (H j)], (∀ j, Countable (H j)) →
    (∀ j, IsLEF (H j)) →
      ∃ (P : Type) (_ : Group P), Countable P ∧ IsLEF P ∧
        ∀ j, ∃ f : H j →* P, Function.Injective f

/-- **There are countably many recursive presentations** (tex l.408–409): the recursively
presented finitely generated groups represent countably many isomorphism classes. -/
def RecursivePresentationClassesStatement : Prop :=
  ∃ (J : Type) (_ : Countable J) (H : J → Type) (_ : ∀ j, Group (H j)),
    ∀ (Γ : Type) [Group Γ], Group.FG Γ → Nonempty (Higman.RecursivePresentation Γ) →
      ∃ j, Nonempty (Γ ≃* H j)

/-! ## Closed pieces -/

/-- **Limits of finite groups in the space of marked groups are LEF, and so are their
subgroups** (tex l.329–330). -/
theorem printedMarkedLimitSubgroupsLEF : PrintedMarkedLimitSubgroupsLEF := by
  intro ι G _ s H _ σ hfin hlim
  have hG : IsLEF G := printedMarkedLimitLEFStatement ι G s H σ hfin hlim
  exact ⟨hG, fun K => isLEF_of_injective K.subtype Subtype.val_injective hG⟩

/-- Such a group is LEF, being a limit of finite groups in the space of marked groups. -/
theorem isLEF_of_isLEFHost {E : Type} [Group E] (h : IsLEFHost E) : IsLEF E := by
  obtain ⟨-, -, -, -, ι, s, κ, _, _, σ, -, hlim, hexp⟩ := h
  exact printedMarkedLimitLEFStatement ι E s (fun ℓ => Matrix.SpecialLinearGroup (κ ℓ) (ZMod 2))
    σ hexp.2.1 hlim

/-- **The "if" half of `cor:lef`**: a subgroup of such a group is LEF. -/
theorem isLEF_of_embeds_isLEFHost {Γ E : Type} [Group Γ] [Group E] (hE : IsLEFHost E)
    (f : Γ →* E) (hf : Function.Injective f) : IsLEF Γ :=
  isLEF_of_injective f hf (isLEF_of_isLEFHost hE)

/-- **The "only if" half of the second statement of `cor:host`** (tex l.407–408): the members of a
set of finitely generated groups lying in one such group are LEF, and they represent countably many
isomorphism classes, as a countable group has countably many finitely generated subgroups. -/
theorem lefFamily_countableClasses_of_host {ι : Type u} {G : ι → Type} [∀ i, Group (G i)]
    (hfg : ∀ i, Group.FG (G i)) {E : Type} [Group E] (hE : IsLEFHost E)
    (hemb : ∀ i, ∃ f : G i →* E, Function.Injective f) :
    (∀ i, IsLEF (G i)) ∧
      ∃ (J : Type) (_ : Countable J) (H : J → Type) (_ : ∀ j, Group (H j)),
        ∀ i, ∃ j, Nonempty (G i ≃* H j) := by
  have hlefE : IsLEF E := isLEF_of_isLEFHost hE
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨f, hf⟩ := hemb i
    exact isLEF_of_injective f hf hlefE
  · haveI : Group.FG E := hE.2.1
    haveI : Countable E := ContinuumMultiplicity.countable_of_fg E
    refine ⟨↥{K : Subgroup E | K.FG}, (ContinuumMultiplicity.countable_fg_subgroups E).to_subtype,
      fun j => ↥(j : Subgroup E), fun j => inferInstance, fun i => ?_⟩
    obtain ⟨f, hf⟩ := hemb i
    haveI : Group.FG (G i) := hfg i
    have hrange : f.range.FG := (Group.fg_iff_subgroup_fg f.range).mp (Group.fg_range f)
    exact ⟨⟨f.range, hrange⟩, ⟨MonoidHom.ofInjective hf⟩⟩

/-! ## Assemblies -/

/-- **The first statement of `cor:host` from its pieces** (tex l.330–402): Part (i) gives
`Γ ↪ [Δ,Δ]`, and Parts (ii)–(iv) give `[Δ,Δ] ↪ G_Δ`. -/
theorem printedCountableLEFHost_of_pieces (hultra : LEFUltraproductEmbeddingStatement)
    (hlamp : LEFLamplighterStatement) : PrintedCountableLEFHost := by
  intro Γ _ hcount hΓ
  obtain ⟨Δ, _, hinf, hfgΔ, hlefΔ, φ, hφ, hmem⟩ := hultra Γ hcount hΓ
  obtain ⟨E, _, hE, ψ, hψ⟩ := hlamp Δ hinf hfgΔ hlefΔ
  refine ⟨E, inferInstance, hE, ψ.comp (φ.codRestrict (commutator Δ) hmem), ?_⟩
  intro x y hxy
  have h1 : ψ (φ.codRestrict (commutator Δ) hmem x) = ψ (φ.codRestrict (commutator Δ) hmem y) :=
    hxy
  exact hφ (congrArg Subtype.val (hψ h1))

/-- **`cor:lef` from its pieces** (tex l.329–404): the "if" half is closed, and a finitely
generated LEF group is countable, so the first statement of `cor:host` applies. -/
theorem printedLEFSubgroupCharacterization_of_pieces (hultra : LEFUltraproductEmbeddingStatement)
    (hlamp : LEFLamplighterStatement) : PrintedLEFSubgroupCharacterization := by
  intro Γ _ hfg
  refine ⟨fun hΓ => ?_, ?_⟩
  · haveI : Group.FG Γ := hfg
    exact printedCountableLEFHost_of_pieces hultra hlamp Γ
      (ContinuumMultiplicity.countable_of_fg Γ) hΓ
  · rintro ⟨E, _, hE, f, hf⟩
    exact isLEF_of_embeds_isLEFHost hE f hf

/-- **The second statement of `cor:host` from its pieces** (tex l.404–408). -/
theorem printedLEFFamilyHost_of_pieces (hultra : LEFUltraproductEmbeddingStatement)
    (hlamp : LEFLamplighterStatement) (hsum : RestrictedSumLEFStatement) :
    PrintedLEFFamilyHost.{u} := by
  intro ι G _ hfg
  refine ⟨?_, ?_⟩
  · rintro ⟨E, _, hE, hemb⟩
    exact lefFamily_countableClasses_of_host hfg hE hemb
  · rintro ⟨hlef, J, _, H, _, hrep⟩
    have hcountH : ∀ j : {j : J // ∃ i, Nonempty (G i ≃* H j)}, Countable (H j.1) := by
      intro j
      obtain ⟨i, ⟨e⟩⟩ := j.2
      haveI : Group.FG (G i) := hfg i
      haveI : Countable (G i) := ContinuumMultiplicity.countable_of_fg (G i)
      exact e.symm.injective.countable
    have hlefH : ∀ j : {j : J // ∃ i, Nonempty (G i ≃* H j)}, IsLEF (H j.1) := by
      intro j
      obtain ⟨i, ⟨e⟩⟩ := j.2
      exact isLEF_of_injective e.symm.toMonoidHom e.symm.injective (hlef i)
    obtain ⟨P, _, hPc, hPlef, hPemb⟩ :=
      hsum {j : J // ∃ i, Nonempty (G i ≃* H j)} (fun j => H j.1) hcountH hlefH
    obtain ⟨E, _, hE, ψ, hψ⟩ := printedCountableLEFHost_of_pieces hultra hlamp P hPc hPlef
    refine ⟨E, inferInstance, hE, fun i => ?_⟩
    obtain ⟨j, ⟨e⟩⟩ := hrep i
    obtain ⟨φ, hφ⟩ := hPemb ⟨j, i, ⟨e⟩⟩
    exact ⟨ψ.comp (φ.comp e.toMonoidHom), hψ.comp (hφ.comp e.injective)⟩

/-- **The last statement of `cor:host` from its pieces** (tex l.322–325, l.404–409): apply the
first statement to the restricted direct sum of representatives of the countably many isomorphism
classes of recursively presented finitely generated LEF groups. -/
theorem printedRecursivelyPresentedLEFHost_of_pieces (hultra : LEFUltraproductEmbeddingStatement)
    (hlamp : LEFLamplighterStatement) (hsum : RestrictedSumLEFStatement)
    (hrec : RecursivePresentationClassesStatement) : PrintedRecursivelyPresentedLEFHost := by
  obtain ⟨J, _, H, _, hrep⟩ := hrec
  have hcountH : ∀ j : {j : J // ∃ (Γ : Type) (_ : Group Γ), Group.FG Γ ∧ IsLEF Γ ∧
      Nonempty (Γ ≃* H j)}, Countable (H j.1) := by
    intro j
    obtain ⟨Γ, _, hfg, -, ⟨e⟩⟩ := j.2
    haveI : Group.FG Γ := hfg
    haveI : Countable Γ := ContinuumMultiplicity.countable_of_fg Γ
    exact e.symm.injective.countable
  have hlefH : ∀ j : {j : J // ∃ (Γ : Type) (_ : Group Γ), Group.FG Γ ∧ IsLEF Γ ∧
      Nonempty (Γ ≃* H j)}, IsLEF (H j.1) := by
    intro j
    obtain ⟨Γ, _, -, hlef, ⟨e⟩⟩ := j.2
    exact isLEF_of_injective e.symm.toMonoidHom e.symm.injective hlef
  obtain ⟨P, _, hPc, hPlef, hPemb⟩ :=
    hsum {j : J // ∃ (Γ : Type) (_ : Group Γ), Group.FG Γ ∧ IsLEF Γ ∧ Nonempty (Γ ≃* H j)}
      (fun j => H j.1) hcountH hlefH
  obtain ⟨E, _, hE, ψ, hψ⟩ := printedCountableLEFHost_of_pieces hultra hlamp P hPc hPlef
  refine ⟨E, inferInstance, hE, fun Γ _ hfg hpres hlef => ?_⟩
  obtain ⟨j, ⟨e⟩⟩ := hrep Γ hfg hpres
  obtain ⟨φ, hφ⟩ := hPemb ⟨j, Γ, inferInstance, hfg, hlef, ⟨e⟩⟩
  exact ⟨ψ.comp (φ.comp e.toMonoidHom), hψ.comp (hφ.comp e.injective)⟩

#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.printedMarkedLimitSubgroupsLEF
#audit_axioms GroupApproximation.SimpleKazhdanSofic.isLEF_of_isLEFHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.isLEF_of_embeds_isLEFHost
#audit_axioms GroupApproximation.SimpleKazhdanSofic.lefFamily_countableClasses_of_host
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedCountableLEFHost_of_pieces
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFSubgroupCharacterization_of_pieces
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedLEFFamilyHost_of_pieces
#audit_axioms GroupApproximation.SimpleKazhdanSofic.printedRecursivelyPresentedLEFHost_of_pieces

end SimpleKazhdanSofic
end GroupApproximation
