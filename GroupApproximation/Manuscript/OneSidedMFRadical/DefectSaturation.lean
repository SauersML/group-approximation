import GroupApproximation.Algebra.FiniteResidual
import GroupApproximation.Manuscript.OneSidedMFRadical.PrintedCriterion
import GroupApproximation.Sofic.SimpleLampNormalGeneration

/-!
# `prop:defect-saturation`, for the defect printed in the manuscript

This file formalizes Proposition~`prop:defect-saturation` of
`non_mf_groups_exist.tex`.  In particular, every statement below uses
`printedDefect`, whose generators range over the *set* of individual
one-sided compressors.  It does not silently replace that subgroup by the
larger `compressionCentralizerDefect` generated using `compressionGroup`.

For a homomorphism `f : G →* Q`, the manuscript writes the target ambient
group as `f(G)`.  The theorem `map_printedDefect_to_range_le` represents that
literally by using the subtype `f.range`.  The ambient-target variant
`map_printedDefect_le` is useful for the proposition's surjective clause.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

open scoped commutatorElement

section Functoriality

variable {G Q : Type*} [Group G] [Group Q]

/-- Compressor transport at arbitrary universes.  The existing analogous
lemma in `IntrinsicCompressionFiniteStage` is universe-zero because that
analytic module is finite-stage; this algebraic statement has no such
restriction. -/
theorem map_mem_printedCompressionSet (f : G →* Q) (L : Subgroup G)
    {u : G} (hu : u ∈ compressionSet L) :
    f u ∈ compressionSet (L.map f) := by
  intro delta hdelta
  rcases hdelta with ⟨d, hd, rfl⟩
  rw [← map_mul, ← map_inv, ← map_mul]
  exact ⟨u * d * u⁻¹, hu d hd, rfl⟩

/-- Homomorphisms carry the printed defect into the printed defect of the
mapped subgroup.  This ambient-target form specializes to the manuscript's
literal `f(G)` statement by taking `f.rangeRestrict`. -/
theorem map_printedDefect_le (f : G →* Q) (L : Subgroup G) :
    (printedDefect L).map f ≤ printedDefect (L.map f) := by
  rintro _ ⟨x, hx, rfl⟩
  apply (show printedDefect L ≤ (printedDefect (L.map f)).comap f from ?_) hx
  apply Subgroup.normalClosure_le_normal
  rintro _ ⟨u, hu, c, hc, ell, hell, rfl⟩
  change f ⁅u * c * u⁻¹, ell⁆ ∈ printedDefect (L.map f)
  rw [map_commutatorElement, map_mul, map_mul, map_inv]
  apply printedDefect_generator_mem (L.map f)
  · exact map_mem_printedCompressionSet f L hu
  · intro delta hdelta
    rcases hdelta with ⟨d, hd, rfl⟩
    exact (hc d hd).map f
  · exact ⟨ell, hell, rfl⟩

/-- Equation~`eq:defect-functoriality` with the manuscript's target ambient
group `f(G)` represented exactly by the range subtype of `f`. -/
theorem map_printedDefect_to_range_le (f : G →* Q) (L : Subgroup G) :
    (printedDefect L).map f.rangeRestrict ≤
      printedDefect (L.map f.rangeRestrict) :=
  map_printedDefect_le f.rangeRestrict L

end Functoriality

section Saturation

variable {G Q : Type*} [Group G] [Group Q]

/-- A normal printed defect which meets a simple subgroup nontrivially
contains that subgroup. -/
theorem simple_le_printedDefect_of_inf_ne_bot (L S : Subgroup G)
    (hS : IsSimpleGroup S) (hne : printedDefect L ⊓ S ≠ ⊥) :
    S ≤ printedDefect L :=
  le_of_normal_of_inf_ne_bot (printedDefect_normal L) hS hne

/-- If that simple subgroup normally generates the ambient group, the printed
defect is the whole group. -/
theorem printedDefect_eq_top_of_simple_normalClosure_eq_top
    (L S : Subgroup G) (hS : IsSimpleGroup S)
    (hne : printedDefect L ⊓ S ≠ ⊥)
    (hgen : Subgroup.normalClosure (S : Set G) = ⊤) :
    printedDefect L = ⊤ := by
  apply top_unique
  rw [← hgen]
  exact Subgroup.normalClosure_le_normal
    (simple_le_printedDefect_of_inf_ne_bot L S hS hne)

/-- The proposition's more general image statement.  The simplicity and
nontrivial-image hypotheses are retained exactly as printed; once `S ≤ D`
and normal generation of `f(S)` are supplied, normality is the step that
forces the conclusion. -/
theorem printedDefect_map_eq_top_of_simple_image_normalClosure_eq_top
    (f : G →* Q) (_hf : Function.Surjective f) (L S : Subgroup G)
    (_hS : IsSimpleGroup S) (hSD : S ≤ printedDefect L)
    (_hne : S.map f ≠ ⊥)
    (hgen : Subgroup.normalClosure (S.map f : Set Q) = ⊤) :
    printedDefect (L.map f) = ⊤ := by
  have hmap : S.map f ≤ printedDefect (L.map f) :=
    (Subgroup.map_mono hSD).trans (map_printedDefect_le f L)
  apply top_unique
  rw [← hgen]
  exact Subgroup.normalClosure_le_normal hmap

end Saturation

section TypeZeroConsequence

variable {G : Type} [Group G]

/-- The final consequence of `prop:defect-saturation`: when `L` and `G` have
property `(T)`, the simple-subgroup saturation hypotheses make the manuscript
MF radical equal to the whole group.  This endpoint is at `Type 0`, exactly
the universe in which the manuscript's property-`(T)` compression criterion
is currently formalized. -/
theorem manuscriptCoronaMFResidual_eq_top_of_printedDefect_saturation
    [Countable G] (L S : Subgroup G)
    (hL : HasKazhdanPropertyT.{0, 0} ↥L)
    (hG : HasKazhdanPropertyT.{0, 0} G)
    (hS : IsSimpleGroup S) (hne : printedDefect L ⊓ S ≠ ⊥)
    (hgen : Subgroup.normalClosure (S : Set G) = ⊤) :
    manuscriptCoronaMFResidual G = ⊤ :=
  (manuscriptOneSidedCompressionCriterion G L hL).2.2 hG
    (printedDefect_eq_top_of_simple_normalClosure_eq_top L S hS hne hgen)

end TypeZeroConsequence

/-! ## The Introduction's sterility consequences

`non_mf_groups_exist.tex`, Introduction, the paragraph beginning "If
`ρ : G → GL(V)` is a homomorphism and `V` is finite-dimensional": the printed
configuration cannot occur when `G` has a faithful finite-dimensional linear
representation, when `G` is residually finite, or — the group-theoretic half
of the amenable case — when `L` is finite.  The amenable case's analytic
input, that an amenable group's property-`(T)` subgroup is finite, is *not*
proved in this module; it is proved in
`Kazhdan.AmenableKazhdanFinite.finite_subgroup_of_isAmenable_of_kazhdan`, so
the manuscript's citation to `BHV` for it is discharged in the development.
What this module supplies is only the finite-`L` conclusion. -/

section Sterility

variable {G : Type*} [Group G]

/-- **A faithful finite-dimensional representation kills the printed
defect.**  The printed defect lies in the kernel of every finite-dimensional
representation over every field, and a faithful representation has trivial
kernel. -/
theorem printedDefect_eq_bot_of_faithful_finiteDimensional
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (rho : G →* (V ≃ₗ[k] V))
    (hrho : Function.Injective rho) (L : Subgroup G) :
    printedDefect L = ⊥ := by
  have hker : rho.ker = ⊥ := (MonoidHom.ker_eq_bot_iff rho).mpr hrho
  refine le_bot_iff.mp ?_
  rw [← hker]
  exact (printedDefect_le_compressionCentralizerDefect L).trans
    (compressionCentralizerDefect_le_ker rho L)

/-- For a **finite** `L`, conjugation by a one-sided compressor is onto `L`:
it is an injective self-map of a finite set, hence surjective. -/
theorem exists_conj_eq_of_mem_compressionSet_of_finite {L : Subgroup G}
    [Finite ↥L] {u : G} (hu : u ∈ compressionSet L) {ell : G} (hell : ell ∈ L) :
    ∃ m ∈ L, u * m * u⁻¹ = ell := by
  have hinj : Function.Injective
      (fun m : ↥L ↦ (⟨u * (m : G) * u⁻¹, hu (m : G) m.2⟩ : ↥L)) := by
    intro a b hab
    have hval : u * (a : G) * u⁻¹ = u * (b : G) * u⁻¹ :=
      congrArg Subtype.val hab
    exact Subtype.ext (mul_left_cancel (mul_right_cancel hval))
  obtain ⟨m, hm⟩ := Finite.injective_iff_surjective.mp hinj ⟨ell, hell⟩
  exact ⟨(m : G), m.2, congrArg Subtype.val hm⟩

/-- The printed sentence `uLu⁻¹ = L` in the finite case: one-sided
compression by `u` is already two-sided. -/
theorem conj_image_eq_of_mem_compressionSet_of_finite {L : Subgroup G}
    [Finite ↥L] {u : G} (hu : u ∈ compressionSet L) :
    (fun x ↦ u * x * u⁻¹) '' (L : Set G) = (L : Set G) := by
  ext y
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact hu m hm
  · intro hy
    obtain ⟨m, hm, hmeq⟩ :=
      exists_conj_eq_of_mem_compressionSet_of_finite hu hy
    exact ⟨m, hm, hmeq⟩

/-- The printed sentence "`ucu⁻¹` centralizes `L`": for a finite `L`, every
compressor conjugate of a centralizer element is again a centralizer
element. -/
theorem commute_conj_of_mem_compressionSet_of_finite {L : Subgroup G}
    [Finite ↥L] {u c : G} (hu : u ∈ compressionSet L)
    (hc : ∀ delta ∈ L, Commute c delta) {ell : G} (hell : ell ∈ L) :
    Commute (u * c * u⁻¹) ell := by
  obtain ⟨m, hm, rfl⟩ := exists_conj_eq_of_mem_compressionSet_of_finite hu hell
  have hcm : c * m = m * c := (hc m hm).eq
  show u * c * u⁻¹ * (u * m * u⁻¹) = u * m * u⁻¹ * (u * c * u⁻¹)
  calc u * c * u⁻¹ * (u * m * u⁻¹) = u * (c * m) * u⁻¹ := by simp [mul_assoc]
    _ = u * (m * c) * u⁻¹ := by rw [hcm]
    _ = u * m * u⁻¹ * (u * c * u⁻¹) := by simp [mul_assoc]

/-- **The group-theoretic half of the amenable case.**  A finite `L` has
trivial printed defect: every printed generator `[ucu⁻¹, ℓ]` is already
trivial. -/
theorem printedDefect_eq_bot_of_finite (L : Subgroup G) [Finite ↥L] :
    printedDefect L = ⊥ := by
  refine le_bot_iff.mp (Subgroup.normalClosure_le_normal ?_)
  rintro _ ⟨u, hu, c, hc, ell, hell, rfl⟩
  exact SetLike.mem_coe.mpr (Subgroup.mem_bot.mpr
    (commutatorElement_eq_one_iff_commute.mpr
      (commute_conj_of_mem_compressionSet_of_finite hu hc hell)))

/-- **Residual finiteness kills the printed defect.**  Functoriality carries
the defect into each finite quotient, where the image of `L` is finite and
the previous theorem applies; residual finiteness then separates every
nontrivial element from all of those quotients.  No representation theory is
used: the finite quotient is killed by the finiteness argument itself. -/
theorem printedDefect_eq_bot_of_isResiduallyFinite (hG : IsResiduallyFinite G)
    (L : Subgroup G) : printedDefect L = ⊥ := by
  refine le_bot_iff.mp ?_
  rw [SetLike.le_def]
  intro x hx
  rw [Subgroup.mem_bot]
  have hres : x ∈ finiteResidual G := by
    rw [finiteResidual_eq_normalFiniteResidual, mem_normalFiniteResidual_iff]
    intro N hN hfi
    haveI := hN
    haveI := hfi
    haveI : Finite (G ⧸ N) := N.finite_quotient_of_finiteIndex
    haveI : Finite ↥(L.map (QuotientGroup.mk' N)) := Subtype.finite
    have hmem : (QuotientGroup.mk' N) x ∈
        printedDefect (L.map (QuotientGroup.mk' N)) :=
      map_printedDefect_le (QuotientGroup.mk' N) L
        (Subgroup.mem_map_of_mem _ hx)
    have hbot : printedDefect (L.map (QuotientGroup.mk' N)) = ⊥ :=
      printedDefect_eq_bot_of_finite _
    rw [hbot, Subgroup.mem_bot] at hmem
    have hker : x ∈ (QuotientGroup.mk' N).ker := MonoidHom.mem_ker.mpr hmem
    rwa [QuotientGroup.ker_mk'] at hker
  rw [hG, Subgroup.mem_bot] at hres
  exact hres

end Sterility

/-- **The Introduction's sterility consequences**, packaged as one closed
proposition: a faithful finite-dimensional linear representation over any
field, residual finiteness, and finiteness of `L` each force `𝔇_G(L) = 1`.
The third clause is the group-theoretic half of the printed amenable case;
the passage from amenability and property `(T)` to finiteness of `L` is the
cited `BHV` input and is not formalized here. -/
def PrintedDefectSterility : Prop :=
  (∀ (G : Type*) [Group G] (k V : Type*) [Field k] [AddCommGroup V]
      [Module k V] [FiniteDimensional k V] (rho : G →* (V ≃ₗ[k] V)),
      Function.Injective rho → ∀ L : Subgroup G, printedDefect L = ⊥) ∧
  (∀ (G : Type*) [Group G], IsResiduallyFinite G →
      ∀ L : Subgroup G, printedDefect L = ⊥) ∧
  (∀ (G : Type*) [Group G] (L : Subgroup G), Finite ↥L →
      printedDefect L = ⊥)

theorem manuscriptPrintedDefectSterility : PrintedDefectSterility := by
  refine ⟨?_, ?_, ?_⟩
  · intro G _ k V _ _ _ _ rho hrho L
    exact printedDefect_eq_bot_of_faithful_finiteDimensional rho hrho L
  · intro G _ hG L
    exact printedDefect_eq_bot_of_isResiduallyFinite hG L
  · intro G _ L hL
    haveI := hL
    exact printedDefect_eq_bot_of_finite L

/-! ## The complete printed proposition as one closed endpoint -/

/-- Proposition~`prop:defect-saturation`, including its final MF-radical
consequence, packaged as a single proposition for the closed-axiom audit. -/
def DefectSaturation : Prop :=
  (∀ (G Q : Type) [Group G] [Group Q] (f : G →* Q) (L : Subgroup G),
      (printedDefect L).map f.rangeRestrict ≤
        printedDefect (L.map f.rangeRestrict)) ∧
  (∀ (G : Type) [Group G] (L S : Subgroup G), IsSimpleGroup S →
      printedDefect L ⊓ S ≠ ⊥ → S ≤ printedDefect L) ∧
  (∀ (G : Type) [Group G] (L S : Subgroup G), IsSimpleGroup S →
      printedDefect L ⊓ S ≠ ⊥ →
      Subgroup.normalClosure (S : Set G) = ⊤ → printedDefect L = ⊤) ∧
  (∀ (G Q : Type) [Group G] [Group Q] (f : G →* Q),
      Function.Surjective f → ∀ (L S : Subgroup G), IsSimpleGroup S →
      S ≤ printedDefect L → S.map f ≠ ⊥ →
      Subgroup.normalClosure (S.map f : Set Q) = ⊤ →
        printedDefect (L.map f) = ⊤) ∧
  (∀ (G : Type) [Group G] [Countable G] (L S : Subgroup G),
      HasKazhdanPropertyT.{0, 0} ↥L → HasKazhdanPropertyT.{0, 0} G →
      IsSimpleGroup S → printedDefect L ⊓ S ≠ ⊥ →
      Subgroup.normalClosure (S : Set G) = ⊤ →
        manuscriptCoronaMFResidual G = ⊤)

theorem manuscriptDefectSaturation : DefectSaturation := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ _ _ f L ↦ map_printedDefect_to_range_le f L
  · exact fun _ _ L S hS hne ↦
      simple_le_printedDefect_of_inf_ne_bot L S hS hne
  · exact fun _ _ L S hS hne hgen ↦
      printedDefect_eq_top_of_simple_normalClosure_eq_top L S hS hne hgen
  · exact fun _ _ _ _ f hf L S hS hSD hne hgen ↦
      printedDefect_map_eq_top_of_simple_image_normalClosure_eq_top
        f hf L S hS hSD hne hgen
  · exact fun _ _ _ L S hL hG hS hne hgen ↦
      manuscriptCoronaMFResidual_eq_top_of_printedDefect_saturation
        L S hL hG hS hne hgen

end OneSidedMFRadical
end Manuscript
end GroupApproximation
