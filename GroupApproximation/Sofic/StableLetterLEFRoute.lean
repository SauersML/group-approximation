import GroupApproximation.Sofic.LiteralSoficAssembly
import GroupApproximation.Sofic.SoficByAmenablePermanence

/-!
# `thm:Esofic` along the route it prints: `E₀` is LEF, and `E = E₀ ⋊ ℤ`

`non_mf_groups_exist.tex`, `\begin{mainthm}[a finitely presented sofic non-MF
group]` (`\label{thm:Esofic}`) and its proof in
`\subsection{Soficity of the literal group}` (`\label{sec:Esofic}`).  Grep the
phrase "the kernel of the exponent sum", never a line number.  The printed
argument is four sentences:

> Let `E₀` be the kernel of the exponent sum in `t`.  For every finite subset
> of `E₀`, the `T`-coordinates lie in a single level of the ascending chain and
> the lamp coordinates involve finitely many conjugates of `c`; the subgroup
> they generate embeds in a residually finite group.  Hence `E₀` is LEF.  Since
> `E` is a split extension of `E₀` by `ℤ`, it is sofic by the Elek--Szabó
> amenable-extension theorem.  This extension does not preserve LEF: LEF groups
> are MF, so `E₀` is LEF whereas `E` is not.

This is proof-ledger row `ES.06`, graded `UNDER-SPECIFIED` because the
formalized proof ran the block-Clifford window tower and never named `E₀`, its
local embeddability, or the split extension: `isSofic_blockClifford_tower`
performs all three steps inside one proof and exposes only the endpoint.  This
module names them.

## The four sentences, one declaration each

* `exists_residuallyFinite_subgroup_telescope` (in
  `Sofic/BlockCliffordTowerSofic.lean`, added with this module) — the window
  statement: every finite subset of `E₀` lies in a residually finite subgroup.
* `telescopeKernel_isLEF` — hence `E₀` is LEF.  Local embeddability, not
  soficity: the printed sentence asserts LEF of `E₀` and *derives* soficity,
  and the distinction is the point of the paragraph's last sentence.
* `markedGroupEquivKernelByInt` with `mem_stableExponent_ker_iff` and
  `stableExponent_surjective` — `E` is a split extension of `E₀` by `ℤ`, and
  `E₀` is the kernel of the exponent sum in `t`, which is what the printed `E₀`
  is defined to be.  The isomorphism is the re-association of the tower already
  built in `Sofic/LiteralSoficAssembly.lean`; nothing new is constructed.
* `markedGroup_isSofic_printedRoute` — soficity of `E`, by
  `SoficByAmenablePermanence.isSofic_semidirectProduct` at the amenable group
  `ℤ`, which is this repository's Elek--Szabó amenable-extension theorem.

`manuscriptEsoficPrintedRoute` collects them together with the printed
contrast `¬ IsLEF E`, so that the whole paragraph is one proposition.

## What this is not

It is not a second proof of soficity: every ingredient is already in the tree,
and `markedGroup_isSofic_printedRoute` is propositionally the same statement as
`LiteralSoficAssembly.markedGroup_isSofic`, reached through the same lemmas in
the printed order rather than through `isSofic_blockClifford_tower`'s packaging.
The badge on `thm:Esofic` should stay where it is; what this module buys is that
the row can be graded against declarations that say what the sentences say.
-/

namespace GroupApproximation
namespace StableLetterLEFRoute

open LiteralNonMFPresentation LiteralBlockNormalForm LiteralSoficAssembly
open MarkedCompression MappingTelescope

noncomputable section

/-! ## `E₀`, and the two actions -/

/-- The action of the telescope on the block-Clifford lamp kernel: the tower
action of `Sofic/LiteralSoficAssembly.lean` restricted along `inl`. -/
abbrev kernelAction :
    Telescope alpha halpha →* MulAut LiteralBlockClifford :=
  SemidirectAssoc.baseAction (shiftHom alpha halpha) towerAction

/-- **`E₀`.**  The printed `C(𝒢) ⋊ T`: the block-Clifford lamps by the
telescope, with no shift.  `mem_stableExponent_ker_iff` below identifies it
with the kernel of the exponent sum in `t`, which is how the manuscript
defines it. -/
abbrev TelescopeKernel : Type :=
  LiteralBlockClifford ⋊[kernelAction] Telescope alpha halpha

/-- The action of the stable letter on `E₀`, by which `E` is the split
extension. -/
abbrev shiftAction : Multiplicative ℤ →* MulAut TelescopeKernel :=
  SemidirectAssoc.outerAction (shiftHom alpha halpha) towerAction

/-! ## Sentence 2: `E₀` is LEF -/

/-- **`E₀` is LEF.**  A finite subset of `E₀` has its telescope coordinates in
one level and its lamp coordinates in finitely many blocks; the invariant
window they generate is residually finite, and a group exhausted by residually
finite subgroups is locally embeddable into finite groups.

This is the printed "the subgroup they generate embeds in a residually finite
group.  Hence `E₀` is LEF", at the group the printed `E₀` is isomorphic to. -/
theorem telescopeKernel_isLEF : IsLEF TelescopeKernel :=
  BlockCliffordTowerSofic.isLEF_blockClifford_telescope Block BlockSites
    ExplicitIntegralLinearModel.gammaBar_residuallyFinite alpha halpha
    kernelAction teleSitePerm
    (fun t ↦ towerAction_sign (SemidirectProduct.inl t))
    towerAction_lamp finite_level_site_orbit

/-- `E₀` is sofic, being LEF.  The manuscript does not state this separately —
it is the input the Elek--Szabó step consumes. -/
theorem telescopeKernel_isSofic : IsSofic TelescopeKernel :=
  isSofic_of_isLEF telescopeKernel_isLEF

/-! ## Sentence 3: the split extension and the exponent sum -/

/-- **`E ≅ E₀ ⋊ ℤ`.**  The block-Clifford tower of `Sofic/LiteralSoficAssembly`
re-associated: `C(𝒢) ⋊ (T ⋊ ℤ)` is `(C(𝒢) ⋊ T) ⋊ ℤ`. -/
def markedGroupEquivKernelByInt :
    MarkedGroup ≃* (TelescopeKernel ⋊[shiftAction] Multiplicative ℤ) :=
  markedGroupEquivTelescopeTower.trans
    (SemidirectAssoc.assocEquiv (shiftHom alpha halpha) towerAction).symm

/-- **The exponent sum in `t`**, as a homomorphism `E → ℤ`: the projection of
the split extension onto its `ℤ` factor. -/
def stableExponent : MarkedGroup →* Multiplicative ℤ :=
  (SemidirectProduct.rightHom (φ := shiftAction)).comp
    markedGroupEquivKernelByInt.toMonoidHom

/-- The exponent sum is onto, which is the manuscript's "`E` surjects onto
`ℤ`". -/
theorem stableExponent_surjective : Function.Surjective stableExponent := by
  intro k
  refine ⟨markedGroupEquivKernelByInt.symm (SemidirectProduct.inr k), ?_⟩
  show SemidirectProduct.rightHom (markedGroupEquivKernelByInt
    (markedGroupEquivKernelByInt.symm (SemidirectProduct.inr k))) = k
  rw [MulEquiv.apply_symm_apply]
  exact SemidirectProduct.rightHom_inr k

/-- In the split extension the kernel of the projection is the copy of `E₀`. -/
theorem ker_rightHom_eq_range_inl :
    (SemidirectProduct.rightHom (φ := shiftAction)).ker
      = (SemidirectProduct.inl (φ := shiftAction)).range :=
  SemidirectProduct.range_inl_eq_ker_rightHom.symm

/-- **`E₀` is the kernel of the exponent sum in `t`.**  An element of `E` has
exponent sum zero exactly when the printed isomorphism sends it into the copy
of `E₀`.  This is the sentence "Let `E₀` be the kernel of the exponent sum in
`t`", read against `E₀ ≅ C(𝒢) ⋊ T`. -/
theorem mem_stableExponent_ker_iff (g : MarkedGroup) :
    g ∈ stableExponent.ker ↔
      markedGroupEquivKernelByInt g ∈
        (SemidirectProduct.inl (φ := shiftAction)).range := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
    MonoidHom.mem_ker]
  rfl

/-! ## Sentence 4: Elek--Szabó, and the endpoint -/

/-- **`E` is sofic, along the printed route.**  `E₀` is LEF hence sofic, `ℤ` is
amenable, and a sofic group extended by an amenable one is sofic.

`SoficByAmenablePermanence.isSofic_semidirectProduct` is this repository's form
of the Elek--Szabó amenable-extension theorem, and `isAmenable_int` supplies
its amenability hypothesis; neither is a literature input. -/
theorem markedGroup_isSofic_printedRoute : IsSofic MarkedGroup :=
  (isSofic_mulEquiv_iff markedGroupEquivKernelByInt).mpr
    (SoficByAmenablePermanence.isSofic_semidirectProduct shiftAction
      telescopeKernel_isSofic SoficByAmenablePermanence.isAmenable_int)

/-- **The paragraph, in one proposition.**  `E₀` is LEF and sofic; the exponent
sum is onto `ℤ` and its kernel is the copy of `E₀`; `E` is sofic; and the
extension does not preserve LEF, since `E` is not LEF.

The last clause is the printed "This extension does not preserve LEF: LEF
groups are MF, so `E₀` is LEF whereas `E` is not", and both halves of that
contrast are now theorems rather than one theorem and one citation. -/
theorem manuscriptEsoficPrintedRoute :
    IsLEF TelescopeKernel ∧
      IsSofic TelescopeKernel ∧
      Function.Surjective stableExponent ∧
      (∀ g : MarkedGroup, g ∈ stableExponent.ker ↔
        markedGroupEquivKernelByInt g ∈
          (SemidirectProduct.inl (φ := shiftAction)).range) ∧
      IsSofic MarkedGroup ∧ ¬ IsLEF MarkedGroup :=
  ⟨telescopeKernel_isLEF, telescopeKernel_isSofic, stableExponent_surjective,
    mem_stableExponent_ker_iff, markedGroup_isSofic_printedRoute,
    (markedGroup_sofic_not_isLEF_unconditional).2.1⟩

end

end StableLetterLEFRoute
end GroupApproximation
