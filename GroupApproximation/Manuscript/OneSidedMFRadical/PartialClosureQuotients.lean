import GroupApproximation.Sofic.MFCamouflage
import GroupApproximation.Criterion.CommutantRigidity

/-!
# Four printed sentences that the library proved only inside other proofs

`non_mf_groups_exist.tex` contains four sentences whose content is used by the
development but is not the statement of any declaration:

* `\section{MF-visible quotients}`, the closing paragraph of the proof of
  `prop:universal-factorization`: *"Conversely, quotienting `W_Q` by
  `⟪d⟫_{W_Q}` kills `B`, since
  `⟪d⟫_B = B`, and kills the second factor `A` in `Q × A`."*  In the library
  this is the anonymous local hypothesis `hkill` inside the proof of
  `MFCamouflage.projection_ker_eq_normalClosure`; the second half is
  `MFCamouflage.product_edge_eq_blackHole`, which is stated, but never
  combined with the first half.
* the next sentence, *"The resulting quotient is `Q`, with quotient map
  induced by `π_Q`."*  `MFCamouflage.projection_surjective` and
  `MFCamouflage.projection_ker_eq_normalClosure` are both stated, and the
  first isomorphism theorem is immediate, but no declaration exhibits the
  isomorphism or records that it is induced by `π_Q`.
* `thm:commutant`, the displayed three-line computation *"If `x ∈ C`, `h ∈ L`,
  and `h' = u h u⁻¹ ∈ L`, then ..."*.  The library reaches the same inclusion
  through `adjointRep_conj_fixed_iff`, which is a different route: the printed
  chain of three equalities is nowhere stated.
* `thm:commutant`, *"Thus `ρ(u)⁻¹ C ρ(u) ⊆ C`."*  In the library this
  inclusion occurs only as one direction of the `iff`
  `commutant_no_growth`/`inv_compressor_mem_commutantStabilizer`, both of
  which carry a `FiniteDimensional` hypothesis.  The printed inclusion does
  not need finite dimension -- it is a two-line computation -- and finite
  dimension enters the printed proof only at the *next* sentence, to upgrade
  the inclusion to an equality.  The statement below therefore has no
  `FiniteDimensional` hypothesis.

Each printed sentence is restated here as a named `Prop` with every quantifier
and hypothesis inside the statement, so that `#audit_closed_axioms`, which
throws on any leading binder, applies to the accompanying theorem.  The
auxiliary lemmas above each pair carry their binders in front and are not
manuscript-facing.

The commutant statements represent `C = ρ(L)'` as
`fixedSubmodule (adjointRep rho) L`, which is the library's definition of the
commutant (`adjointRep_fixed_iff_commute` turns membership into commutation
with every `ρ(ℓ)`), and this is the rendering the sentence census already
records for the printed sentence "Put `C = ρ(L)'`".

Instantiability of the camouflage hypothesis `⟪d⟫_B = B` is not vacuous: it is
discharged for the manuscript's own group by
`RankTwelveEndpoint.normalClosure_defect_eq_top`, together with
`RankTwelveEndpoint.defect_ne_one`.  That module is not imported here, to keep
this file next to the two constructions it talks about.

No theorem from the literature is an input.
-/

namespace GroupApproximation
namespace Manuscript
namespace OneSidedMFRadical

universe u v w

/-! ## The camouflage amalgam: quotienting by the printed defect -/

/-- **Auxiliary (not manuscript-facing).**  "Quotienting `W_Q` by `⟪d⟫_{W_Q}`
kills `B`, since `⟪d⟫_B = B`."  This is the anonymous `hkill` of
`MFCamouflage.projection_ker_eq_normalClosure`, extracted as a statement. -/
theorem quotientByDefect_comp_blackHole {B : Type} [Group B] (d : B)
    (Q : Type) [Group Q]
    (hgen : Subgroup.normalClosure ({d} : Set B) = ⊤) :
    (QuotientGroup.mk' (Subgroup.normalClosure
        ({MFCamouflage.defect d Q} : Set (MFCamouflage.Camouflage d Q)))).comp
      (MFCamouflage.blackHole d Q) = 1 := by
  ext b
  have hb : b ∈ Subgroup.normalClosure ({d} : Set B) := by
    rw [hgen]
    exact Subgroup.mem_top b
  have hle : Subgroup.normalClosure ({d} : Set B) ≤
      ((QuotientGroup.mk' (Subgroup.normalClosure
        ({MFCamouflage.defect d Q} :
          Set (MFCamouflage.Camouflage d Q)))).comp
        (MFCamouflage.blackHole d Q)).ker := by
    refine Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr ?_)
    apply MonoidHom.mem_ker.mpr
    exact (QuotientGroup.eq_one_iff (MFCamouflage.defect d Q)).mpr
      (Subgroup.subset_normalClosure (Set.mem_singleton _))
  exact MonoidHom.mem_ker.mp (hle hb)

/-- **Auxiliary (not manuscript-facing).**  The same quotient "kills the
second factor `A` in `Q × A`": the composite of the second-factor inclusion
`A → Q × A` with the product vertex dies in the quotient.  The edge relation
`MFCamouflage.product_edge_eq_blackHole` identifies that composite with the
black-hole inclusion of `A ≤ B`. -/
theorem quotientByDefect_comp_edgeFactor {B : Type} [Group B] (d : B)
    (Q : Type) [Group Q]
    (hgen : Subgroup.normalClosure ({d} : Set B) = ⊤) :
    (QuotientGroup.mk' (Subgroup.normalClosure
        ({MFCamouflage.defect d Q} : Set (MFCamouflage.Camouflage d Q)))).comp
      ((MFCamouflage.productVertex d Q).comp
        (MonoidHom.inr Q ↥(MFCamouflage.Edge d))) = 1 := by
  have hkill := quotientByDefect_comp_blackHole d Q hgen
  ext z
  have hedge : ((MFCamouflage.productVertex d Q).comp
      (MonoidHom.inr Q ↥(MFCamouflage.Edge d))) z =
      MFCamouflage.blackHole d Q z.1 :=
    MFCamouflage.product_edge_eq_blackHole d Q z
  rw [MonoidHom.comp_apply, hedge]
  exact DFunLike.congr_fun hkill z.1

/-- **"Conversely, quotienting `W_Q` by `⟪d⟫_{W_Q}` kills `B`, since
`⟪d⟫_B = B`, and kills the second factor `A` in `Q × A`."**  Both halves of
the printed sentence, under the printed hypothesis that `d` normally generates
`B`: the quotient map of `W_Q` by the normal closure of the defect annihilates
the black-hole vertex `B`, and annihilates the second factor `A` of the
product vertex `Q × A`. -/
def PrintedCamouflageQuotientKillsBothVertices : Prop :=
  ∀ (B : Type) [Group B] (d : B) (Q : Type) [Group Q],
    Subgroup.normalClosure ({d} : Set B) = ⊤ →
      (QuotientGroup.mk' (Subgroup.normalClosure
          ({MFCamouflage.defect d Q} :
            Set (MFCamouflage.Camouflage d Q)))).comp
          (MFCamouflage.blackHole d Q) = 1 ∧
        (QuotientGroup.mk' (Subgroup.normalClosure
          ({MFCamouflage.defect d Q} :
            Set (MFCamouflage.Camouflage d Q)))).comp
          ((MFCamouflage.productVertex d Q).comp
            (MonoidHom.inr Q ↥(MFCamouflage.Edge d))) = 1

/-- Closed proof of the printed "kills `B` ... and kills the second factor
`A`" sentence. -/
theorem manuscriptPrintedCamouflageQuotientKillsBothVertices :
    PrintedCamouflageQuotientKillsBothVertices := by
  intro B _ d Q _ hgen
  exact ⟨quotientByDefect_comp_blackHole d Q hgen,
    quotientByDefect_comp_edgeFactor d Q hgen⟩

/-- **"The resulting quotient is `Q`, with quotient map induced by `π_Q`."**
The quotient of `W_Q` by the normal closure of the defect is isomorphic to
`Q`, and the isomorphism carries the canonical quotient map of `W_Q` to
`π_Q`: both pointwise and as an identity of homomorphisms.  Stated as an
existential because the isomorphism is data, and a `Prop` is what the closed
audit consumes. -/
def PrintedCamouflageQuotientIsVisibleGroup : Prop :=
  ∀ (B : Type) [Group B] (d : B) (Q : Type) [Group Q],
    Subgroup.normalClosure ({d} : Set B) = ⊤ →
      ∃ e : (MFCamouflage.Camouflage d Q ⧸
          Subgroup.normalClosure
            ({MFCamouflage.defect d Q} :
              Set (MFCamouflage.Camouflage d Q))) ≃* Q,
        (∀ x : MFCamouflage.Camouflage d Q,
            e (QuotientGroup.mk' (Subgroup.normalClosure
                ({MFCamouflage.defect d Q} :
                  Set (MFCamouflage.Camouflage d Q))) x) =
              MFCamouflage.projection d Q x) ∧
          e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.normalClosure
              ({MFCamouflage.defect d Q} :
                Set (MFCamouflage.Camouflage d Q)))) =
            MFCamouflage.projection d Q

/-- Closed proof of "the resulting quotient is `Q`, with quotient map induced
by `π_Q`".  The isomorphism is the first isomorphism theorem for `π_Q`,
transported along `MFCamouflage.projection_ker_eq_normalClosure`. -/
theorem manuscriptPrintedCamouflageQuotientIsVisibleGroup :
    PrintedCamouflageQuotientIsVisibleGroup := by
  intro B _ d Q _ hgen
  have hker : (MFCamouflage.projection d Q).ker =
      Subgroup.normalClosure
        ({MFCamouflage.defect d Q} : Set (MFCamouflage.Camouflage d Q)) :=
    MFCamouflage.projection_ker_eq_normalClosure d Q hgen
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (MFCamouflage.projection d Q)
        (MFCamouflage.projection_surjective d Q)),
    fun _x => rfl, MonoidHom.ext fun _x => rfl⟩

/-! ## `thm:commutant`: the printed conjugation computation -/

/-- **Auxiliary (not manuscript-facing).**  `ρ(u)⁻¹ρ(u h u⁻¹) = ρ(h)ρ(u)⁻¹`,
evaluated at a vector.  This is the first equality of the printed display. -/
theorem repInvConj_apply {G : Type u} {k : Type v} {V : Type w} [Group G]
    [Field k] [AddCommGroup V] [Module k V] (rho : G →* (V ≃ₗ[k] V))
    (u h : G) (y : V) :
    ((rho u)⁻¹ : V ≃ₗ[k] V) (rho (u * h * u⁻¹) y) =
      rho h (((rho u)⁻¹ : V ≃ₗ[k] V) y) := by
  have hgrp : u⁻¹ * (u * h * u⁻¹) = h * u⁻¹ := by group
  have hmul : ((rho u)⁻¹ * rho (u * h * u⁻¹) : V ≃ₗ[k] V) =
      rho h * (rho u)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hgrp]
  exact DFunLike.congr_fun hmul y

/-- **Auxiliary (not manuscript-facing).**  `ρ(u h u⁻¹)ρ(u) = ρ(u)ρ(h)`,
evaluated at a vector.  This is the third equality of the printed display. -/
theorem repConjMul_apply {G : Type u} {k : Type v} {V : Type w} [Group G]
    [Field k] [AddCommGroup V] [Module k V] (rho : G →* (V ≃ₗ[k] V))
    (u h : G) (y : V) :
    rho (u * h * u⁻¹) (rho u y) = rho u (rho h y) := by
  have hgrp : u * h * u⁻¹ * u = u * h := by group
  have hmul : (rho (u * h * u⁻¹) * rho u : V ≃ₗ[k] V) = rho u * rho h := by
    rw [← map_mul, ← map_mul, hgrp]
  exact DFunLike.congr_fun hmul y

/-- **`thm:commutant`, the displayed three-line computation.**  "If `x ∈ C`,
`h ∈ L`, and `h' = u h u⁻¹ ∈ L`, then
`ρ(h)ρ(u)⁻¹xρ(u) = ρ(u)⁻¹ρ(h')xρ(u) = ρ(u)⁻¹xρ(h')ρ(u) = ρ(u)⁻¹xρ(u)ρ(h)`."
The three printed equalities are the first three conjuncts, in printed order;
the fourth is the chain they compose to, which is what the next printed
sentence uses.  `C` is `ρ(L)'`, i.e. the fixed submodule of the adjoint
representation.  No finite-dimensionality is assumed: the display is an
identity of operators. -/
def PrintedCommutantConjugationDisplay : Prop :=
  ∀ (G : Type u) (k : Type v) (V : Type w) [Group G] [Field k] [AddCommGroup V]
    [Module k V] (rho : G →* (V ≃ₗ[k] V)) (L : Subgroup G) (u : G)
    (x : V →ₗ[k] V) (_hx : x ∈ fixedSubmodule (adjointRep rho) L)
    (h : G) (_hh : h ∈ L) (h' : G) (_hconj : h' = u * h * u⁻¹) (_hh' : h' ∈ L),
      (rho h : V →ₗ[k] V) ∘ₗ (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ
            (rho u : V →ₗ[k] V) =
          (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ (rho h' : V →ₗ[k] V) ∘ₗ x ∘ₗ
            (rho u : V →ₗ[k] V) ∧
        (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ (rho h' : V →ₗ[k] V) ∘ₗ x ∘ₗ
              (rho u : V →ₗ[k] V) =
            (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ
              (rho h' : V →ₗ[k] V) ∘ₗ (rho u : V →ₗ[k] V) ∧
          (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ
                (rho h' : V →ₗ[k] V) ∘ₗ (rho u : V →ₗ[k] V) =
              (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ
                (rho u : V →ₗ[k] V) ∘ₗ (rho h : V →ₗ[k] V) ∧
            (rho h : V →ₗ[k] V) ∘ₗ (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ
                x ∘ₗ (rho u : V →ₗ[k] V) =
              (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ
                (rho u : V →ₗ[k] V) ∘ₗ (rho h : V →ₗ[k] V)

/-- Closed proof of the printed three-line commutant computation. -/
theorem manuscriptPrintedCommutantConjugationDisplay :
    PrintedCommutantConjugationDisplay := by
  intro G k V _ _ _ _ rho L u x hx h _hh h' hconj hh'
  subst hconj
  have hcomm : (rho (u * h * u⁻¹) : V →ₗ[k] V) ∘ₗ x =
      x ∘ₗ (rho (u * h * u⁻¹) : V →ₗ[k] V) :=
    (adjointRep_fixed_iff_commute rho (u * h * u⁻¹) x).mp
      (mem_fixedSubmodule.mp hx _ hh')
  have h1 : (rho h : V →ₗ[k] V) ∘ₗ (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ
        x ∘ₗ (rho u : V →ₗ[k] V) =
      (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ
        (rho (u * h * u⁻¹) : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho u : V →ₗ[k] V) :=
    LinearMap.ext fun y => (repInvConj_apply rho u h (x (rho u y))).symm
  have h2 : (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ
        (rho (u * h * u⁻¹) : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho u : V →ₗ[k] V) =
      (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ
        (rho (u * h * u⁻¹) : V →ₗ[k] V) ∘ₗ (rho u : V →ₗ[k] V) :=
    LinearMap.ext fun y =>
      congrArg (fun z : V => ((rho u)⁻¹ : V ≃ₗ[k] V) z)
        (DFunLike.congr_fun hcomm (rho u y))
  have h3 : (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ
        (rho (u * h * u⁻¹) : V →ₗ[k] V) ∘ₗ (rho u : V →ₗ[k] V) =
      (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho u : V →ₗ[k] V) ∘ₗ
        (rho h : V →ₗ[k] V) :=
    LinearMap.ext fun y =>
      congrArg (fun z : V => ((rho u)⁻¹ : V ≃ₗ[k] V) (x z))
        (repConjMul_apply rho u h y)
  exact ⟨h1, h2, h3, h1.trans (h2.trans h3)⟩

/-- **"Thus `ρ(u)⁻¹ C ρ(u) ⊆ C`."**  Under the printed standing hypothesis
`u L u⁻¹ ≤ L`, conjugating the commutant `C = ρ(L)'` by `ρ(u)⁻¹` lands inside
`C` again: elementwise, and as an inclusion of the conjugated set.  There is
no finite-dimensionality hypothesis; the printed proof spends finite dimension
only on the *next* sentence, which upgrades this inclusion to an equality. -/
def PrintedCommutantConjugationInclusion : Prop :=
  ∀ (G : Type u) (k : Type v) (V : Type w) [Group G] [Field k] [AddCommGroup V]
    [Module k V] (rho : G →* (V ≃ₗ[k] V)) (L : Subgroup G) (u : G),
    (∀ h ∈ L, u * h * u⁻¹ ∈ L) →
      (∀ x ∈ fixedSubmodule (adjointRep rho) L,
          (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ
              (rho u : V →ₗ[k] V) ∈ fixedSubmodule (adjointRep rho) L) ∧
        (fun y : V →ₗ[k] V =>
              (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ y ∘ₗ
                (rho u : V →ₗ[k] V)) ''
            (fixedSubmodule (adjointRep rho) L : Set (V →ₗ[k] V)) ⊆
          (fixedSubmodule (adjointRep rho) L : Set (V →ₗ[k] V))

/-- Closed proof of "Thus `ρ(u)⁻¹ C ρ(u) ⊆ C`", by the printed computation and
nothing else. -/
theorem manuscriptPrintedCommutantConjugationInclusion :
    PrintedCommutantConjugationInclusion := by
  intro G k V _ _ _ _ rho L u hu
  have hmem : ∀ x ∈ fixedSubmodule (adjointRep rho) L,
      (((rho u)⁻¹ : V ≃ₗ[k] V) : V →ₗ[k] V) ∘ₗ x ∘ₗ (rho u : V →ₗ[k] V) ∈
        fixedSubmodule (adjointRep rho) L := by
    intro x hx
    refine mem_fixedSubmodule.mpr fun g hg => ?_
    refine (adjointRep_fixed_iff_commute rho g _).mpr ?_
    have hcomm : (rho (u * g * u⁻¹) : V →ₗ[k] V) ∘ₗ x =
        x ∘ₗ (rho (u * g * u⁻¹) : V →ₗ[k] V) :=
      (adjointRep_fixed_iff_commute rho (u * g * u⁻¹) x).mp
        (mem_fixedSubmodule.mp hx _ (hu g hg))
    refine LinearMap.ext fun y => ?_
    calc
      rho g (((rho u)⁻¹ : V ≃ₗ[k] V) (x (rho u y))) =
          ((rho u)⁻¹ : V ≃ₗ[k] V) (rho (u * g * u⁻¹) (x (rho u y))) :=
        (repInvConj_apply rho u g (x (rho u y))).symm
      _ = ((rho u)⁻¹ : V ≃ₗ[k] V) (x (rho (u * g * u⁻¹) (rho u y))) :=
        congrArg (fun z : V => ((rho u)⁻¹ : V ≃ₗ[k] V) z)
          (DFunLike.congr_fun hcomm (rho u y))
      _ = ((rho u)⁻¹ : V ≃ₗ[k] V) (x (rho u (rho g y))) :=
        congrArg (fun z : V => ((rho u)⁻¹ : V ≃ₗ[k] V) (x z))
          (repConjMul_apply rho u g y)
  refine ⟨hmem, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact hmem z hz

end OneSidedMFRadical
end Manuscript
end GroupApproximation
