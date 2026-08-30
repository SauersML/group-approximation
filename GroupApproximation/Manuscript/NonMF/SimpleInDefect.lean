import GroupApproximation.Meta.AxiomGuard
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedDefect
import GroupApproximation.Sofic.IntrinsicCompressionDefect
import GroupApproximation.Sofic.KazhdanCompressionFunctorial
import GroupApproximation.Sofic.TorsionFreeFullMFRadical

/-!
# The simple factor in every mapped compression defect

`non_mf_groups_exist.tex`, `lem:commutator-in-defect` (tex 845-862) and the
paragraph it rests on (tex 835-843).

The manuscript's lemma is

> For every homomorphism `ρ : G₀ → Ḡ`, `ρ(S) ≤ 𝔇_Ḡ(ρ(Γ))`,

with `S = tJt⁻¹` and `J ≤ G₀` a finitely presented infinite simple group, and
its proof goes through perfectness of `S̄`.  This module carries that lemma,
by that proof, in the section "`lem:commutator-in-defect`, by the printed
proof": `manuscriptLemmaCommutatorInDefect`, over the printed configuration
`PrintedFournierFacioData`.  That is the manuscript's route and it is the one
the sentence census cites.

The first half of the module carries a **second, auxiliary proof of a
containment of the same shape**, over `FournierFacioDefectData`, which reaches
`ρ(S) ≤ 𝔇` from simplicity of `S` plus one protected nonidentity commutator
instead of from perfectness.  It is a strengthening, not a replacement: it
needs less input, so it is worth keeping, and `Manuscript.NonMF.TheoremC` uses
a variant of it internally with the free group `F₂` in place of `J`.  Nothing
here supersedes the printed lemma, and no sentence of the manuscript is graded
against the auxiliary route.

For a datum `D`, the manuscript's subgroups `π(S)` and `Γ` are respectively
`D.simpleSubgroup` and `D.iota.range`.  Thus their images under `ρ` are
`D.simpleSubgroup.map ρ` and `D.iota.range.map ρ`.  The first theorem below is
the marked-core statement: the image of the simple factor lies in the defect
normal subgroup of the mapped core for every homomorphism.  The theorems after
it identify that marked defect with a subgroup of the exact one-sided defect
printed in the manuscript.

Neither surjectivity nor nontriviality of the mapped simple factor is needed
for the auxiliary containment.  They are retained in its final wrapper solely
so that its hypotheses keep the shape an earlier draft of the paper printed
under the label `lem:simple-in-defect`.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF

open scoped commutatorElement

universe u v

variable {P : Type} {E : Type u} {L : Type v}
  [Group P] [Group E] [Group L]

/-- The image of the Fournier--Facio simple factor lies in the defect normal
subgroup of the mapped compression core, for every homomorphism. -/
theorem map_simpleSubgroup_le_defectNormal
    (D : FournierFacioDefectData P E) (rho : E →* L) :
    D.simpleSubgroup.map rho ≤ (D.core.map rho).defectNormal :=
  D.core.map_subgroup_le_defectNormal rho D.simpleSubgroup
    D.simpleSubgroup_le_defectNormal

/-- A marked core's defect normal subgroup is contained in the exact
one-sided compression--centralizer defect printed in the manuscript. -/
theorem defectNormal_le_printedDefect (C : KazhdanCompressionCore P L) :
    C.defectNormal ≤ OneSidedMFRadical.printedDefect C.iota.range := by
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨p, rfl⟩
  exact OneSidedMFRadical.printedDefect_generator_mem C.iota.range
    C.t_mem_compressionSet C.c_commutes_range ⟨p, rfl⟩

/-- The exact containment asserted by the printed lemma, without its
unnecessary surjectivity and nontrivial-image hypotheses. -/
theorem map_simpleSubgroup_le_printedDefect
    (D : FournierFacioDefectData P E) (rho : E →* L) :
    D.simpleSubgroup.map rho ≤
      OneSidedMFRadical.printedDefect (D.iota.range.map rho) := by
  rw [← MonoidHom.range_comp]
  exact (map_simpleSubgroup_le_defectNormal D rho).trans
    (defectNormal_le_printedDefect (D.core.map rho))

/-- The printed hypothesis shape, packaged as one proposition so the endpoint
has no declaration inputs.  The datum itself remains a genuine mathematical
hypothesis; a separate construction must produce the manuscript's concrete
Fournier--Facio datum. -/
def PrintedSimpleInDefect : Prop :=
  ∀ {P : Type} {E L : Type} [Group P] [Group E] [Group L]
    (D : FournierFacioDefectData P E) (rho : E →* L),
    Function.Surjective rho → D.simpleSubgroup.map rho ≠ ⊥ →
      D.simpleSubgroup.map rho ≤
        OneSidedMFRadical.printedDefect (D.iota.range.map rho)

/-- **`lem:simple-in-defect`, in its printed hypothesis shape.**

Here `D.simpleSubgroup.map rho` is `ρ(π(S))` and
`D.iota.range.map rho` is `ρ(Γ)`.  The proof above shows that the two printed
hypotheses are stronger than necessary for this containment. -/
theorem manuscriptLemmaSimpleInDefect : PrintedSimpleInDefect := by
  intro P E L _ _ _ D rho _ _
  exact map_simpleSubgroup_le_printedDefect D rho

/-! ## `lem:commutator-in-defect`, by the printed proof

Everything above reaches the containment by simplicity of `S` together with one
protected nonidentity commutator.  That is not the manuscript's proof.  The
manuscript's proof, at `non_mf_groups_exist.tex` 845-862, runs through
perfectness, and this section follows it sentence by sentence.

The printed configuration is the paragraph at tex 835-843: `Γ ≤ G₀`, an element
`t` with `tΓt⁻¹ ≤ Γ`, and a subgroup `J ≤ G₀` isomorphic to a finitely
presented infinite simple group with `[Γ,J] = 1` and `tJt⁻¹ ≤ Γ`.  It is a
citation of Fournier-Facio, so it enters as a datum; that conditionality is the
literature input and nothing more. -/

section PrintedRoute

/-- **The Fournier-Facio package, as `non_mf_groups_exist.tex` 835-843 prints
it.**

`core` is `Γ`, `t` is `t`, and `simpleFactor` is `J`.  The manuscript's `S` is
`tJt⁻¹`, defined below as `conjFactor` rather than carried as a field, so that
`S = tJt⁻¹` is a definition and not an assumption.

`nonabelian` renders "nonabelian" the way the printed proof uses it: two
elements of `J` that do not commute.  Simplicity and nonabelianness are both
clauses of the citation; they are what the printed middle step consumes. -/
structure PrintedFournierFacioData (Ambient : Type u) [Group Ambient] where
  /-- `Γ ≤ G₀`, the compressed core. -/
  core : Subgroup Ambient
  /-- The compressor `t ∈ G₀`. -/
  t : Ambient
  /-- `J ≤ G₀`, the simple factor. -/
  simpleFactor : Subgroup Ambient
  /-- `tΓt⁻¹ ≤ Γ`. -/
  conj_core_mem : ∀ γ ∈ core, t * γ * t⁻¹ ∈ core
  /-- `[Γ, J] = 1`. -/
  simpleFactor_centralizes : ∀ c ∈ simpleFactor, ∀ γ ∈ core, Commute c γ
  /-- `tJt⁻¹ ≤ Γ`. -/
  conj_simpleFactor_mem : ∀ c ∈ simpleFactor, t * c * t⁻¹ ∈ core
  /-- `J` is simple. -/
  simple : IsSimpleGroup ↥simpleFactor
  /-- `J` is nonabelian. -/
  nonabelian : ∃ x y : ↥simpleFactor, ¬ Commute x y

namespace PrintedFournierFacioData

variable (F : PrintedFournierFacioData E)

/-- **"Put `S = tJt⁻¹`."**

`Subgroup.map` along `MulAut.conj t` is `tJt⁻¹`, which is the spelling the
development already uses for the printed `tΓt⁻¹` (see
`Analysis/StrictCompressionFromPrinted.lean`). -/
def conjFactor : Subgroup E := F.simpleFactor.map (MulAut.conj F.t).toMonoidHom

theorem conjFactor_def :
    F.conjFactor = F.simpleFactor.map (MulAut.conj F.t).toMonoidHom := rfl

/-- **"Since `J` is simple and nonabelian, `J` ... is perfect."**

A normal subgroup of `J` is `⊥` or `⊤`; the commutator subgroup is normal, and
it is not `⊥` because it contains the commutator of the two elements that do
not commute.  So it is `⊤`, which for the subgroup `J ≤ G₀` is `⁅J, J⁆ = J`. -/
theorem commutator_simpleFactor_eq : ⁅F.simpleFactor, F.simpleFactor⁆ = F.simpleFactor := by
  haveI : IsSimpleGroup ↥F.simpleFactor := F.simple
  have hcomm : _root_.commutator ↥F.simpleFactor = ⊤ := by
    obtain ⟨x, y, hxy⟩ := F.nonabelian
    have hmem : ⁅x, y⁆ ∈ _root_.commutator ↥F.simpleFactor := by
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    have hnorm : (_root_.commutator ↥F.simpleFactor).Normal := inferInstance
    rcases hnorm.eq_bot_or_eq_top with h | h
    · exact absurd
        (commutatorElement_eq_one_iff_commute.mp (Subgroup.mem_bot.mp (h ▸ hmem))) hxy
    · exact h
  rw [← F.simpleFactor.map_subtype_commutator, hcomm, ← MonoidHom.range_eq_map,
    F.simpleFactor.range_subtype]

/-- **"... and `S` [is perfect]."**  `S` is an isomorphic image of `J`. -/
theorem commutator_conjFactor_eq : ⁅F.conjFactor, F.conjFactor⁆ = F.conjFactor := by
  rw [conjFactor_def, ← Subgroup.map_commutator, F.commutator_simpleFactor_eq]

/-- **"The group `S̄` is perfect as a quotient of `S`."**

The image of a perfect subgroup under any homomorphism is perfect; the printed
sentence is the special case where the homomorphism is `ρ`. -/
theorem commutator_map_conjFactor_eq (rho : E →* L) :
    ⁅F.conjFactor.map rho, F.conjFactor.map rho⁆ = F.conjFactor.map rho := by
  rw [← Subgroup.map_commutator, F.commutator_conjFactor_eq]

/-- **"`S ≤ Γ`"**, from the printed `tJt⁻¹ ≤ Γ`. -/
theorem conjFactor_le_core : F.conjFactor ≤ F.core := by
  intro x hx
  rw [conjFactor_def, Subgroup.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  simpa using F.conj_simpleFactor_mem c hc

/-- **"`S̄ ≤ Γ̄`."** -/
theorem map_conjFactor_le_map_core (rho : E →* L) :
    F.conjFactor.map rho ≤ F.core.map rho :=
  Subgroup.map_mono F.conjFactor_le_core

/-- **"`t̄Γ̄t̄⁻¹ ≤ Γ̄`."** -/
theorem map_conj_core_mem (rho : E →* L) :
    ∀ δ ∈ F.core.map rho, rho F.t * δ * (rho F.t)⁻¹ ∈ F.core.map rho := by
  intro δ hδ
  rw [Subgroup.mem_map] at hδ
  obtain ⟨γ, hγ, rfl⟩ := hδ
  refine Subgroup.mem_map.mpr ⟨F.t * γ * F.t⁻¹, F.conj_core_mem γ hγ, ?_⟩
  simp

/-- **"`J̄` centralizes `Γ̄`."** -/
theorem map_simpleFactor_centralizes (rho : E →* L) {c : E} (hc : c ∈ F.simpleFactor) :
    ∀ δ ∈ F.core.map rho, Commute (rho c) δ := by
  intro δ hδ
  rw [Subgroup.mem_map] at hδ
  obtain ⟨γ, hγ, rfl⟩ := hδ
  exact (F.simpleFactor_centralizes c hc γ hγ).map rho

/-- **"For `c ∈ J̄` and `ℓ ∈ S̄`, the commutator `[t̄ct̄⁻¹, ℓ]` lies in
`𝔇_Ḡ(Γ̄)` by `eq:intrinsic-defect`."**

`ℓ` is taken in `Γ̄`, which is where `eq:intrinsic-defect` needs it and where
`S̄ ≤ Γ̄` puts it. -/
theorem defect_generator_mem (rho : E →* L) {c : E} (hc : c ∈ F.simpleFactor)
    {ℓ : L} (hℓ : ℓ ∈ F.core.map rho) :
    ⁅rho F.t * rho c * (rho F.t)⁻¹, ℓ⁆ ∈
      OneSidedMFRadical.printedDefect (F.core.map rho) :=
  OneSidedMFRadical.printedDefect_generator_mem _ (F.map_conj_core_mem rho)
    (F.map_simpleFactor_centralizes rho hc) hℓ

/-- **"As `c` ranges over `J̄`, the element `t̄ct̄⁻¹` ranges over `S̄`, so
`[S̄, S̄] ≤ 𝔇_Ḡ(Γ̄)`."** -/
theorem commutator_map_conjFactor_le_printedDefect (rho : E →* L) :
    ⁅F.conjFactor.map rho, F.conjFactor.map rho⁆ ≤
      OneSidedMFRadical.printedDefect (F.core.map rho) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_map] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  rw [conjFactor_def, Subgroup.mem_map] at hs
  obtain ⟨c, hc, rfl⟩ := hs
  have hxeq : rho ((MulAut.conj F.t).toMonoidHom c)
      = rho F.t * rho c * (rho F.t)⁻¹ := by simp
  rw [hxeq]
  exact F.defect_generator_mem rho hc (F.map_conjFactor_le_map_core rho hy)

/-- **`lem:commutator-in-defect`.**

> For every homomorphism `ρ : G₀ → Ḡ`, `ρ(S) ≤ 𝔇_Ḡ(ρ(Γ))`.

The printed proof, in order: the three clauses about `Γ̄`, `J̄` and `S̄`; the
defect generators; `[S̄, S̄] ≤ 𝔇`; and then perfectness of `S̄`, which turns the
commutator subgroup back into `S̄` itself. -/
theorem map_conjFactor_le_printedDefect (rho : E →* L) :
    F.conjFactor.map rho ≤ OneSidedMFRadical.printedDefect (F.core.map rho) := by
  calc F.conjFactor.map rho
      = ⁅F.conjFactor.map rho, F.conjFactor.map rho⁆ :=
        (F.commutator_map_conjFactor_eq rho).symm
    _ ≤ OneSidedMFRadical.printedDefect (F.core.map rho) :=
        F.commutator_map_conjFactor_le_printedDefect rho

end PrintedFournierFacioData

/-- The printed lemma with no declaration inputs: the Fournier-Facio datum is
universally quantified inside the proposition, and the quantifier over `ρ` is
the printed one -- arbitrary, neither surjective nor nontrivial on `S`. -/
def PrintedCommutatorInDefect : Prop :=
  ∀ {E L : Type} [Group E] [Group L] (F : PrintedFournierFacioData E) (rho : E →* L),
    F.conjFactor.map rho ≤ OneSidedMFRadical.printedDefect (F.core.map rho)

/-- **`lem:commutator-in-defect`, proved by the printed argument.** -/
theorem manuscriptLemmaCommutatorInDefect : PrintedCommutatorInDefect := by
  intro E L _ _ F rho
  exact F.map_conjFactor_le_printedDefect rho

end PrintedRoute

end NonMF
end Manuscript
end GroupApproximation

#audit_closed_axioms GroupApproximation.Manuscript.NonMF.manuscriptLemmaSimpleInDefect
#audit_closed_axioms GroupApproximation.Manuscript.NonMF.manuscriptLemmaCommutatorInDefect
