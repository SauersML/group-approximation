import GroupApproximation.Computability.SecondLevelIndexSets
import GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
import GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationCore
import GroupApproximation.Sofic.ChiodoBelegradekTheorem
import Mathlib.GroupTheory.HNNExtension

/-!
# `mf_recognition_complexity.tex`: the data consumed by the two branch lemmas

This module fixes, in Lean, the objects of Table~1 of the manuscript that
`lem:negative-branch` and `lem:positive-branch` actually consume, and nothing
else.  The two displayed HNN extensions are written out literally:

```
  Γ_e = ⟨K_e, v | [v, ℓ] = 1 (ℓ ∈ L_e)⟩            (eq:central-rope)
  R_e = ⟨Γ_e × Q_e, u | u(s,1)u⁻¹ = (s,α_e(s)) (s ∈ S_e)⟩   (eq:twisted-rope)
```

`CentralRope` is the first and `TwistedHNN` the second.  Both are Mathlib
`HNNExtension`s: the first has both edge groups equal to `L_e` and the
identity edge isomorphism, which is exactly what `[v,ℓ]=1 (ℓ∈L_e)` says; the
second has edge groups `{(s,1)}` and `{(s,α_e(s))}` and the edge isomorphism
`(s,1) ↦ (s,α_e(s))`.

The structure `RecognitionInputs` bundles the printed facts about these
objects that the two branches use.  Every field names the printed lemma it
comes from.  Nothing in this file is a new mathematical claim: the fields are
hypotheses, and the theorems are the two transport steps (a regular
realization moves along a group isomorphism, and every coded finite
presentation is countable) that the branch lemmas need in order to speak about
`R̂_e` rather than about `R_e`.

## The stable letter

The manuscript's stable letter of `Γ_e` is called `v`, and it conjugates as
`v i(f) v⁻¹`.  Mathlib's `HNNExtension.t` conjugates the same way
(`HNNExtension.equiv_eq_conj`), so `ropeStable` is `HNNExtension.t`.  The
displayed presentation is unchanged by replacing `v` by `v⁻¹`, so a
formalization that realizes the manuscript's `v` as `t⁻¹` describes the same
group; see `PositiveBranchFiniteQuotients.ropeLambda_stable_inv`, which shows
that the finite quotient of the positive branch does not see the difference.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace Recognition

open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open GroupApproximation.SecondLevelIndexSets

/-! ## 1.  The first HNN extension: `K_e`, `L_e`, `i`, `Γ_e`, `v`, `S_e` -/

/-- `L^{\mathrm g} = \{(f, jq_+(f)) : f \in F\}`, the graph of `j q_+` inside
`K^{\mathrm g} = F × P`. -/
def ropeGraph {F P : Type} [Group F] [Group P] (psi : F →* P) :
    Subgroup (F × P) :=
  ((MonoidHom.id F).prod psi).range

theorem mem_ropeGraph_iff {F P : Type} [Group F] [Group P] (psi : F →* P)
    (z : F × P) : z ∈ ropeGraph psi ↔ ∃ f : F, (f, psi f) = z :=
  Iff.rfl

/-- `K_e = K^0_e × K^{\mathrm g} = K^0_e × (F × P)`. -/
abbrev RopeBase (K0 F P : Type) : Type := K0 × (F × P)

/-- `L_e = L^0_e × L^{\mathrm g}`. -/
def ropeEdge {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) : Subgroup (RopeBase K0 F P) :=
  L0.prod (ropeGraph psi)

/-- **`eq:central-rope`.**  `Γ_e = ⟨K_e, v | [v,ℓ] = 1 (ℓ ∈ L_e)⟩`: the HNN
extension of `K_e` with both edge groups equal to `L_e` and the identity as
edge isomorphism. -/
abbrev CentralRope {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) : Type :=
  HNNExtension (RopeBase K0 F P) (ropeEdge L0 psi) (ropeEdge L0 psi)
    (MulEquiv.refl (ropeEdge L0 psi))

/-- The printed stable letter `v` of `eq:central-rope`. -/
def ropeStable {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) : CentralRope L0 psi :=
  (HNNExtension.t)⁻¹

/-- `i(f) = (i^0_e(f), (f,1))`, read in `K_e`. -/
def ropeEmbedding {K0 F P : Type} [Group K0] [Group F] [Group P]
    (i0 : F →* K0) : F →* RopeBase K0 F P :=
  i0.prod (MonoidHom.inl F P)

theorem ropeEmbedding_apply {K0 F : Type} (P : Type) [Group K0] [Group F]
    [Group P] (i0 : F →* K0) (f : F) :
    ropeEmbedding (P := P) i0 f = (i0 f, (f, 1)) := rfl

/-- "Injectivity of `i` is clear from the first coordinate."
(`lem:central-rope`(1)) -/
theorem ropeEmbedding_injective {K0 F P : Type} [Group K0] [Group F] [Group P]
    (i0 : F →* K0) (hi0 : Function.Injective i0) :
    Function.Injective (ropeEmbedding (P := P) i0) := by
  intro a b hab
  exact hi0 (congrArg Prod.fst hab)

/-- `i(f)`, read in `Γ_e`. -/
def ropeGen {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) :
    F →* CentralRope L0 psi :=
  (HNNExtension.of : RopeBase K0 F P →* CentralRope L0 psi).comp
    (ropeEmbedding i0)

/-- `v i(f) v⁻¹`, read in `Γ_e`. -/
def ropeGenConj {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) :
    F →* CentralRope L0 psi :=
  (MulAut.conj (ropeStable L0 psi)).toMonoidHom.comp (ropeGen L0 psi i0)

theorem ropeGenConj_apply {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) (f : F) :
    ropeGenConj L0 psi i0 f =
      ropeStable L0 psi * ropeGen L0 psi i0 f * (ropeStable L0 psi)⁻¹ :=
  rfl

/-- **`eq:central-rope`.**  `S_e = ⟨i(F), v i(F) v⁻¹⟩ ≤ Γ_e`. -/
def ropeSubgroup {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) :
    Subgroup (CentralRope L0 psi) :=
  Subgroup.closure
    (Set.range (ropeGen L0 psi i0) ∪ Set.range (ropeGenConj L0 psi i0))

theorem ropeGen_mem_ropeSubgroup {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) (f : F) :
    ropeGen L0 psi i0 f ∈ ropeSubgroup L0 psi i0 :=
  Subgroup.subset_closure (Or.inl ⟨f, rfl⟩)

theorem ropeGenConj_mem_ropeSubgroup {K0 F P : Type} [Group K0] [Group F]
    [Group P] (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) (f : F) :
    ropeGenConj L0 psi i0 f ∈ ropeSubgroup L0 psi i0 :=
  Subgroup.subset_closure (Or.inr ⟨f, rfl⟩)

/-- `i(f)`, read as an element of `S_e`. -/
def ropeGenS {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) :
    F →* ↥(ropeSubgroup L0 psi i0) :=
  (ropeGen L0 psi i0).codRestrict _ (ropeGen_mem_ropeSubgroup L0 psi i0)

/-- `v i(f) v⁻¹`, read as an element of `S_e`. -/
def ropeGenConjS {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) :
    F →* ↥(ropeSubgroup L0 psi i0) :=
  (ropeGenConj L0 psi i0).codRestrict _
    (ropeGenConj_mem_ropeSubgroup L0 psi i0)

@[simp] theorem coe_ropeGenS {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) (f : F) :
    ((ropeGenS L0 psi i0 f : ↥(ropeSubgroup L0 psi i0)) :
      CentralRope L0 psi) = ropeGen L0 psi i0 f := rfl

@[simp] theorem coe_ropeGenConjS {K0 F P : Type} [Group K0] [Group F] [Group P]
    (L0 : Subgroup K0) (psi : F →* P) (i0 : F →* K0) (f : F) :
    ((ropeGenConjS L0 psi i0 f : ↥(ropeSubgroup L0 psi i0)) :
      CentralRope L0 psi) = ropeGenConj L0 psi i0 f := rfl

/-! ## 2.  The second HNN extension: `R_e` -/

/-- The left edge map `s ↦ (s,1)` of `eq:twisted-rope`. -/
def edgeSource {Gamma : Type} [Group Gamma] (S : Subgroup Gamma) (Q : Type)
    [Group Q] : ↥S →* Gamma × Q :=
  S.subtype.prod (1 : ↥S →* Q)

/-- The right edge map `s ↦ (s,τ(s))` of `eq:twisted-rope`. -/
def edgeTarget {Gamma Q : Type} [Group Gamma] [Group Q] (S : Subgroup Gamma)
    (tau : ↥S →* Q) : ↥S →* Gamma × Q :=
  S.subtype.prod tau

theorem edgeSource_injective {Gamma : Type} [Group Gamma] (S : Subgroup Gamma)
    (Q : Type) [Group Q] : Function.Injective (edgeSource S Q) := by
  intro a b hab
  have h : (a : Gamma) = (b : Gamma) := congrArg Prod.fst hab
  exact Subtype.ext h

theorem edgeTarget_injective {Gamma Q : Type} [Group Gamma] [Group Q]
    (S : Subgroup Gamma) (tau : ↥S →* Q) :
    Function.Injective (edgeTarget S tau) := by
  intro a b hab
  have h : (a : Gamma) = (b : Gamma) := congrArg Prod.fst hab
  exact Subtype.ext h

/-- The subgroup `{(s,1) : s ∈ S}` of `Γ × Q`. -/
def edgeSubgroupSource {Gamma : Type} [Group Gamma] (S : Subgroup Gamma)
    (Q : Type) [Group Q] : Subgroup (Gamma × Q) :=
  (edgeSource S Q).range

/-- The subgroup `{(s,τ(s)) : s ∈ S}` of `Γ × Q`. -/
def edgeSubgroupTarget {Gamma Q : Type} [Group Gamma] [Group Q]
    (S : Subgroup Gamma) (tau : ↥S →* Q) : Subgroup (Gamma × Q) :=
  (edgeTarget S tau).range

/-- Both edge maps are injective because their first coordinate is the
inclusion of `S`, so both kernels are trivial. -/
theorem edgeSource_ker_eq_edgeTarget_ker {Gamma Q : Type} [Group Gamma]
    [Group Q] (S : Subgroup Gamma) (tau : ↥S →* Q) :
    (edgeSource S Q).ker = (edgeTarget S tau).ker :=
  ((MonoidHom.ker_eq_bot_iff (edgeSource S Q)).mpr
      (edgeSource_injective S Q)).trans
    ((MonoidHom.ker_eq_bot_iff (edgeTarget S tau)).mpr
      (edgeTarget_injective S tau)).symm

/-- The printed edge isomorphism `(s,1) ↦ (s,τ(s))` of `eq:twisted-rope`:
each edge group is a copy of `S`, so the two images are canonically
isomorphic.

This is built by the same construction, from the same two edge maps, as
`TensorSynchronization.edgeMulEquiv`, so `TwistedHNN` below is definitionally
the HNN extension that `lem:tensor-sync` concludes about and no transport is
needed between the two readings. -/
noncomputable def edgeMulEquiv {Gamma Q : Type} [Group Gamma] [Group Q]
    (S : Subgroup Gamma) (tau : ↥S →* Q) :
    ↥(edgeSubgroupSource S Q) ≃* ↥(edgeSubgroupTarget S tau) :=
  OneSidedMFRadical.TensorSynchronizationCore.rangeMulEquivOfKerEq
    (edgeSource S Q) (edgeTarget S tau)
    (edgeSource_ker_eq_edgeTarget_ker S tau)

/-- **`eq:twisted-rope`.**  The group
`⟨Γ × Q, u | u(s,1)u⁻¹ = (s,τ(s)) (s ∈ S)⟩`.  This is also the group named in
the last sentence of `lem:tensor-sync`. -/
@[reducible] noncomputable def TwistedHNN {Gamma Q : Type} [Group Gamma]
    [Group Q] (S : Subgroup Gamma) (tau : ↥S →* Q) : Type :=
  HNNExtension (Gamma × Q) (edgeSubgroupSource S Q) (edgeSubgroupTarget S tau)
    (edgeMulEquiv S tau)

/-- "whose edge maps `s ↦ (s,1)` and `s ↦ (s,α_e(s))` are injective
homomorphisms of `S_e` into `Γ_e × Q_e`; so `Γ_e × Q_e` embeds in `R_e` by
Britton's lemma." -/
theorem twistedHNN_of_injective {Gamma Q : Type} [Group Gamma] [Group Q]
    (S : Subgroup Gamma) (tau : ↥S →* Q) :
    Function.Injective
      (HNNExtension.of : Gamma × Q →* TwistedHNN S tau) :=
  HNNExtension.of_injective _

/-! ## 3.  Two transport steps -/

/-- A tracial MF realization moves along a group isomorphism: compose the
unitary representation with the isomorphism and keep the same algebra and the
same tracial state. -/
theorem isRegularlyRealized_of_mulEquiv {G G' : Type} [Group G] [Group G']
    (e : G' ≃* G) (h : IsRegularlyRealized G) : IsRegularlyRealized G' := by
  obtain ⟨A, instA, hA⟩ := h
  letI : CStarAlgebra A := instA
  obtain ⟨R⟩ := hA
  refine ⟨A, instA, ⟨?_⟩⟩
  exact
    { mf := R.mf
      rho := R.rho.comp e.toMonoidHom
      tau := R.tau
      regular := fun g hg =>
        R.regular (e g) ((MulEquiv.map_ne_one_iff e).mpr hg) }

/-- Every finite presentation names a countable group.  This is the clause
that lets the branch lemmas be read on presentation codes. -/
theorem countable_carrier (c : PresentationCodes.PresentationCode) :
    Countable (PresentationCodes.Carrier c) :=
  ChiodoBelegradek.countable_of_isFinitelyPresented
    (PresentationCodes.Carrier c)

/-! ## 4.  The inputs of the two branch lemmas -/

/-- **The objects of Table~1 attached to a program index `e`, and the printed
facts about them that `lem:negative-branch` and `lem:positive-branch`
consume.**

| field | printed source |
| --- | --- |
| `not_isOperatorMF_H` | `H` is not MF, `[NonMF, Theorem B]` |
| `embed_H_C` | `lem:switch`: `H` embeds in `C_e` for `e ∈ FIN` |
| `embed_C_Q` | `lem:bridge`(1): `C` embeds in `B(C) = Q_e` |
| `j`, `j_injective`, `residuallyFinite_P` | `lem:bridge`(3) |
| `L0`, `i0` | `lem:mikhailova` |
| `residuallyFinite_K` | `lem:central-rope`(1) |
| `alpha`, `alpha_gen`, `alpha_genConj` | `lem:central-rope`(3) |
| `pi1`, `pi1_gen`, `pi1_genConj` | the maps `π_0,π_1` of `lem:positive-branch` |
| `equiv_Q_Qplus`, `qe_eq_qplus` | "`Q_e = Q_+`, `N_e = N_+`, `q_e = q_+`" |
| `equiv_Rhat` | `lem:finite-rope` |

`Γ_e` and `S_e` are not fields: they are the displayed presentations
`CentralRope L0 (j ∘ q_+)` and `ropeSubgroup L0 (j ∘ q_+) i0`. -/
structure RecognitionInputs (e : Nat.Partrec.Code)
    (H C F P Qplus Q K0 Rhat : Type)
    [Group H] [Group C] [Group F] [Group P] [Group Qplus] [Group Q]
    [Group K0] [Group Rhat] where
  /-- `H` is finitely generated (`lem:seed`), so countable. -/
  countable_H : Countable H
  /-- `H` is not MF, by `[NonMF, Theorem B]`. -/
  not_isOperatorMF_H : ¬ IsOperatorMF H
  /-- **`lem:switch`.**  "`H` embeds in `C_e` if `e ∈ FIN`." -/
  embed_H_C : FiniteDomain e → ∃ f : H →* C, Function.Injective f
  /-- **`lem:bridge`(1).**  "`B(C)` is an HNN extension of `C * F(x,y)`, so
  `C` embeds in `B(C)`", at `C = C_e`, `B(C_e) = Q_e`. -/
  embed_C_Q : ∃ f : C →* Q, Function.Injective f
  /-- The printed quotient map `q_e : F → Q_e`. -/
  qe : F →* Q
  /-- The printed quotient map `q_+ : F → Q_+`. -/
  qplus : F →* Qplus
  /-- **`lem:bridge`(3).**  `j : Q_+ → P = F(x_1,y) × F(x_2,t)`. -/
  j : Qplus →* P
  /-- ... which is injective. -/
  j_injective : Function.Injective j
  /-- "Free groups are residually finite and residual finiteness passes to
  direct products and subgroups", so `P` is residually finite. -/
  residuallyFinite_P : Group.ResiduallyFinite P
  /-- `P` is a product of two finitely generated free groups, so countable. -/
  countable_P : Countable P
  /-- `Q_e` is a quotient of `F`, so countable. -/
  countable_Q : Countable Q
  /-- `Q_+` is a quotient of `F`, so countable. -/
  countable_Qplus : Countable Qplus
  /-- **`lem:mikhailova`.**  The subgroup `L^0_e = F × M_e` of
  `K^0_e = F × F(X_e) × F(X_e)`. -/
  L0 : Subgroup K0
  /-- **`lem:mikhailova`.**  The injection `i_e : F → K^0_e`. -/
  i0 : F →* K0
  /-- **`lem:central-rope`(1).**  `K_e` is "a direct product of free groups of
  finite rank, so finitely presented and residually finite". -/
  residuallyFinite_K : Group.ResiduallyFinite (RopeBase K0 F P)
  /-- ... and countable. -/
  countable_K : Countable (RopeBase K0 F P)
  /-- **`lem:central-rope`(2).**  `Γ_e` is finitely presented, so countable. -/
  countable_Gamma : Countable (CentralRope L0 (j.comp qplus))
  /-- **`lem:central-rope`(3).**  `α_e : S_e → Q_e`. -/
  alpha : ↥(ropeSubgroup L0 (j.comp qplus) i0) →* Q
  /-- ... with `α_e(i(f)) = q_e(f)`. -/
  alpha_gen : ∀ f : F,
    alpha (ropeGenS L0 (j.comp qplus) i0 f) = qe f
  /-- ... and `α_e(v i(f) v⁻¹) = 1`. -/
  alpha_genConj : ∀ f : F,
    alpha (ropeGenConjS L0 (j.comp qplus) i0 f) = 1
  /-- The second coordinate map `π_1 : S_e → Q_+` of `lem:positive-branch`,
  "trivial on one copy of `F` in `S_e ≅ F *_{N_+} F` and `q_+` on the
  other". -/
  pi1 : ↥(ropeSubgroup L0 (j.comp qplus) i0) →* Qplus
  /-- ... `π_1(i(f)) = 1`. -/
  pi1_gen : ∀ f : F, pi1 (ropeGenS L0 (j.comp qplus) i0 f) = 1
  /-- ... and `π_1(v i(f) v⁻¹) = q_+(f)`. -/
  pi1_genConj : ∀ f : F,
    pi1 (ropeGenConjS L0 (j.comp qplus) i0 f) = qplus f
  /-- "if `e ∈ INF` then `Q_e = Q_+`". -/
  equiv_Q_Qplus : InfiniteDomain e → (Q ≃* Qplus)
  /-- "... `N_e = N_+` and `q_e = q_+`". -/
  qe_eq_qplus : ∀ (h : InfiniteDomain e) (f : F),
    equiv_Q_Qplus h (qe f) = qplus f
  /-- **`lem:finite-rope`.**  "The groups `R̂_e` and `R_e` are isomorphic by
  the map that is the identity on `Γ_e` and on `u` and sends `F` onto `Q_e`
  by `q_e`." -/
  equiv_Rhat :
    TwistedHNN (ropeSubgroup L0 (j.comp qplus) i0) alpha ≃* Rhat
  /-- `R̂_e` is finitely presented, so countable. -/
  countable_Rhat : Countable Rhat

end Recognition
end MFRecognition
end Manuscript
end GroupApproximation
