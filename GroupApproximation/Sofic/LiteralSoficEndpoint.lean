import GroupApproximation.Algebra.SemidirectProductAssoc
import GroupApproximation.Sofic.Hyperlinear
import GroupApproximation.Sofic.LEFSofic
import GroupApproximation.Sofic.LiteralNonMFEndpoint
import GroupApproximation.Sofic.LocallyFiniteMF
import GroupApproximation.Sofic.SoficIntegerExtension
import GroupApproximation.Sofic.SoficTransfer
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The soficity endpoint for the literal finitely presented non-MF group

`Sofic/LiteralNonMFEndpoint.lean` proves, unconditionally, that the literal
eight-generator forty-one-relator group `E` of `LiteralNonMFPresentation` is
finitely presented and not MF.  This file supplies the other half of the
separation: given soficity of the telescope core, `E` itself is sofic, hence
hyperlinear, and the two halves combine into

> an explicit finitely presented **sofic** group that is not MF.

The mathematics is `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` §5 and §6a, and
the route statement `research/literal-sofic-via-block-tower.md`.  The final
step is one sentence: the stable-letter exponent gives

    1 → E_T → E → ℤ → 1 ,

split along `⟨τ⟩`, with `E_T = N_E ⋊ T` the telescope core; `ℤ` is amenable, so
`E` is sofic by the sofic-kernel / amenable-quotient permanence of Elek--Szabó.
The split integer case of that permanence is `Sofic/SoficIntegerExtension.lean`
(`isSofic_int_semidirectProduct`), proved in this repository from the local
definition by truncating the level set to `ZMod L`; it is used here as a black
box.  The *converse* direction -- amenable kernel with sofic quotient -- is not
a theorem and is used nowhere in this file; §1 of the source document records it
as a refuted route.

## What is conditional, and what is not

Everything about *non*-MF is unconditional and already in the repository.
This file isolates the conditional endpoint: soficity of the telescope core
`E_T` is the sole premise of every conditional declaration below.  The later
module `Sofic/LiteralSoficAssembly.lean` discharges that premise and proves
`markedGroup_isSofic : IsSofic MarkedGroup` unconditionally.

`notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` flags `B ≅ Γ̄` (completeness of the
eight-relator presentation of `SL₃(ℤ)`) as the one irreducible literature input,
entering at its (S1) and at its Lemma 3.1.  That caveat is now obsolete:
`Monsters/LiteralBaseCompleteness.lean` proves
`baseAffineEquiv : Base ≃* gammaBar` outright, so the split normal form
`E = N_E ⋊ V` is premise-free inside this repository.  Residual finiteness of
the finite block windows and telescope levels is proved in
`BlockCliffordLamp.lean` and assembled by `LiteralSoficAssembly.lean`; it is no
longer an open input.  No declaration in this file asserts soficity of `E`
outright by design, because this module is the reusable conditional interface.

## Interface

Two independent entry points produce `IsSofic MarkedGroup`, so that whichever
shape the splitting lane delivers can be consumed without further glue:

* `markedGroup_isSofic_of_soficCore` takes the *retraction* shape -- a
  homomorphism `π : E → ℤ` with a section and sofic kernel, packaged as the
  closed proposition `HasSoficTelescopeCore`;
* `markedGroup_isSofic_of_towerEquiv` takes the *tower* shape -- an isomorphism
  `E ≅ N ⋊ (T ⋊ ℤ)` together with soficity of the reassociated core `N ⋊ T`,
  exactly as `Sofic/SoficMarkedCompression.lean` consumes it for the finitely
  generated witness `W`.

Everything downstream of soficity is packaged separately, with `IsSofic
MarkedGroup` as its only premise, so the two entry points share one endpoint.
-/

namespace GroupApproximation
namespace LiteralSoficEndpoint

open LiteralNonMFPresentation

/-! ## Split extensions by the integers

A retraction `π : G → ℤ` with a section `s` exhibits `G` as the semidirect
product of `ker π` by `ℤ`.  This is the internal-to-external translation that
`SoficIntegerExtension.isSofic_int_semidirectProduct` needs, and it is stated
for an arbitrary group: nothing about the literal presentation enters. -/

section SplitData

variable {G : Type*} [Group G] (π : G →* Multiplicative ℤ)
  (s : Multiplicative ℤ →* G)

/-- The `ℤ`-action on `ker π` obtained by conjugating along the section.  The
kernel is normal, so conjugation lands in its automorphism group. -/
def splitAction : Multiplicative ℤ →* MulAut π.ker :=
  (MulAut.conjNormal (H := π.ker)).comp s

/-- The multiplication map `(k, n) ↦ k · s n` of the internal splitting, as a
homomorphism out of the external semidirect product. -/
def splitHom : (π.ker ⋊[splitAction π s] Multiplicative ℤ) →* G :=
  SemidirectProduct.lift π.ker.subtype s (by
    intro n
    apply MonoidHom.ext
    intro k
    exact MulAut.conjNormal_apply (s n) k)

/-- The splitting map is the multiplication map, by construction. -/
@[simp] theorem splitHom_apply (x : π.ker ⋊[splitAction π s] Multiplicative ℤ) :
    splitHom π s x = (x.left : G) * s x.right := rfl

/-- Injectivity of the splitting map: an element of the kernel has trivial
`π`-image, so the `ℤ`-coordinate of a relation is forced to vanish first. -/
theorem splitHom_injective (hπs : ∀ n, π (s n) = n) :
    Function.Injective (splitHom π s) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  rw [splitHom_apply] at hx
  have hleft : π (x.left : G) = 1 := MonoidHom.mem_ker.mp x.left.2
  have hright : x.right = 1 := by
    have hπ : π ((x.left : G) * s x.right) = 1 := by rw [hx, map_one]
    rw [map_mul, hleft, one_mul, hπs] at hπ
    exact hπ
  refine SemidirectProduct.ext (Subtype.ext ?_) hright
  rw [hright, map_one, mul_one] at hx
  exact hx

/-- Surjectivity of the splitting map: correcting `g` by the section of its own
`π`-image lands in the kernel. -/
theorem splitHom_surjective (hπs : ∀ n, π (s n) = n) :
    Function.Surjective (splitHom π s) := by
  intro g
  have hmem : g * (s (π g))⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπs, mul_inv_cancel]
  refine ⟨⟨⟨g * (s (π g))⁻¹, hmem⟩, π g⟩, ?_⟩
  rw [splitHom_apply]
  exact inv_mul_cancel_right g (s (π g))

/-- **A retraction onto `ℤ` with a section splits the group.**  This is the
internal-to-external translation of `1 → ker π → G → ℤ → 1`. -/
noncomputable def splitEquiv (hπs : ∀ n, π (s n) = n) :
    (π.ker ⋊[splitAction π s] Multiplicative ℤ) ≃* G :=
  MulEquiv.ofBijective (splitHom π s)
    ⟨splitHom_injective π s hπs, splitHom_surjective π s hπs⟩

end SplitData

/-! ## The three soficity transfers -/

section Transfers

variable {G : Type*} [Group G]

/-- **Elek--Szabó, split integer case, transported along an isomorphism.**  If
`G` is isomorphic to a semidirect product of a sofic group by `ℤ`, it is sofic.
The content is `SoficIntegerExtension.isSofic_int_semidirectProduct`;
`isSofic_mulEquiv_iff` moves it across the isomorphism. -/
theorem isSofic_of_intSemidirectEquiv {C : Type*} [Group C]
    {φ : Multiplicative ℤ →* MulAut C}
    (e : G ≃* (C ⋊[φ] Multiplicative ℤ)) (hC : IsSofic C) :
    IsSofic G :=
  (isSofic_mulEquiv_iff e).mpr
    (SoficIntegerExtension.isSofic_int_semidirectProduct φ hC)

/-- **Retraction form.**  A group carrying a homomorphism onto `ℤ` that admits
a section and has sofic kernel is sofic. -/
theorem isSofic_of_intRetraction (π : G →* Multiplicative ℤ)
    (s : Multiplicative ℤ →* G) (hπs : ∀ n, π (s n) = n)
    (hker : IsSofic π.ker) : IsSofic G :=
  isSofic_of_intSemidirectEquiv (splitEquiv π s hπs).symm hker

/-- **Tower form.**  A group isomorphic to `A ⋊ (B ⋊ ℤ)` is sofic as soon as
the reassociated core `A ⋊ B` is sofic.  This is the shape in which the
finitely generated witness `W` is handled by
`Sofic/SoficMarkedCompression.lean`, and the shape the literal group `E`
presents: `E ≅ N_E ⋊ (T ⋊ ℤ)` with core `E_T = N_E ⋊ T`. -/
theorem isSofic_of_towerEquiv {A B : Type*} [Group A] [Group B]
    (g : Multiplicative ℤ →* MulAut B)
    (f : (B ⋊[g] Multiplicative ℤ) →* MulAut A)
    (e : G ≃* (A ⋊[f] (B ⋊[g] Multiplicative ℤ)))
    (hcore : IsSofic (A ⋊[SemidirectAssoc.baseAction g f] B)) :
    IsSofic G :=
  (isSofic_mulEquiv_iff e).mpr
    (isSofic_of_intSemidirectEquiv (SemidirectAssoc.assocEquiv g f).symm hcore)

end Transfers

/-! ## The literal group

`MarkedGroup` is the literal eight-generator, forty-one-relator group `E` of
`def:E`.  The two declarations below are the only places where soficity of `E`
is produced, and each is conditional on a statement about the telescope core
that this file does not prove. -/

/-- **The closed premise of the soficity endpoint.**  The stable-letter
exponent retracts `E` onto `ℤ`, the retraction has a section (the stable letter
itself), and its kernel -- the telescope core `E_T = N_E ⋊ T` -- is sofic.

Only the last clause is open: the retraction and its section are elementary
consequences of the presentation, while soficity of `E_T` is the conclusion of
the block-tower argument of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` §§3--4,
which in turn carries the `B ≅ Γ̄` input recorded in that document's header. -/
def HasSoficTelescopeCore : Prop :=
  ∃ (π : MarkedGroup →* Multiplicative ℤ) (s : Multiplicative ℤ →* MarkedGroup),
    (∀ n, π (s n) = n) ∧ IsSofic π.ker

/-- **The literal group is sofic, given a sofic telescope core.**  This is
Theorem 5.1 of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md`, with its one open
input exposed as a hypothesis rather than assumed. -/
theorem markedGroup_isSofic_of_soficCore (h : HasSoficTelescopeCore) :
    IsSofic MarkedGroup := by
  obtain ⟨π, s, hπs, hcore⟩ := h
  exact isSofic_of_intRetraction π s hπs hcore

/-- **The literal group is sofic, given the tower splitting.**  The same
conclusion from the other presentation of the splitting: an isomorphism
`E ≅ N_E ⋊ (T ⋊ ℤ)` together with soficity of the reassociated core
`E_T = N_E ⋊ T`. -/
theorem markedGroup_isSofic_of_towerEquiv {A B : Type*} [Group A] [Group B]
    (g : Multiplicative ℤ →* MulAut B)
    (f : (B ⋊[g] Multiplicative ℤ) →* MulAut A)
    (e : MarkedGroup ≃* (A ⋊[f] (B ⋊[g] Multiplicative ℤ)))
    (hcore : IsSofic (A ⋊[SemidirectAssoc.baseAction g f] B)) :
    IsSofic MarkedGroup :=
  isSofic_of_towerEquiv g f e hcore

/-! ## Unconditional companions

These two need no soficity input at all: they follow from the unconditional
failure of operator MF, because LEF implies MF and residual finiteness implies
LEF.  Together with soficity they give the separations of Corollary 5.5 of the
source document. -/

/-- **The literal group is not LEF.**  A countable LEF group is operator MF
(`isOperatorMF_of_isLEF`), and `E` is not.  Premise-free. -/
theorem markedGroup_not_isLEF : ¬ IsLEF MarkedGroup := fun hLEF ↦
  LiteralNonMFEndpoint.literal_not_isOperatorMF (isOperatorMF_of_isLEF hLEF)

/-- **The literal group is not residually finite.**  Residually finite implies
LEF.  Premise-free. -/
theorem markedGroup_not_residuallyFinite :
    ¬ Group.ResiduallyFinite MarkedGroup := by
  intro h
  haveI := h
  exact markedGroup_not_isLEF isLEF_of_residuallyFinite

/-! ## Packaged endpoints

Each of the following takes soficity of `E` as its single premise, so that both
entry points above feed the same endpoint. -/

/-- **The separation, exactly as it would be printed.**  The literal
eight-generator group is finitely presented, sofic, and not MF in the
manuscript's genuine-corona convention. -/
theorem markedGroup_finitelyPresented_sofic_not_isCDEOperatorMF
    (hsofic : IsSofic MarkedGroup) :
    Group.IsFinitelyPresented MarkedGroup ∧ IsSofic MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup :=
  ⟨markedGroup_finitelyPresented, hsofic,
    LiteralNonMFEndpoint.literal_not_isCDEOperatorMF⟩

/-- **The hyperlinear form.**  Soficity implies hyperlinearity, so the same
group is an explicit finitely presented hyperlinear group that is not MF. -/
theorem markedGroup_finitelyPresented_hyperlinear_not_isCDEOperatorMF
    (hsofic : IsSofic MarkedGroup) :
    Group.IsFinitelyPresented MarkedGroup ∧ IsHyperlinear MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup :=
  ⟨markedGroup_finitelyPresented, isHyperlinear_of_isSofic hsofic,
    LiteralNonMFEndpoint.literal_not_isCDEOperatorMF⟩

/-- **Sofic but not LEF.**  Corollary 5.5 of the source document: an explicit
finitely presented group separating soficity from local embeddability into
finite groups.  The second and third clauses are premise-free. -/
theorem markedGroup_sofic_not_isLEF (hsofic : IsSofic MarkedGroup) :
    IsSofic MarkedGroup ∧ ¬ IsLEF MarkedGroup ∧
      ¬ Group.ResiduallyFinite MarkedGroup :=
  ⟨hsofic, markedGroup_not_isLEF, markedGroup_not_residuallyFinite⟩

/-- **The full endpoint package.**  Finitely presented, sofic, hyperlinear, not
LEF, not residually finite, and not MF in every convention the development
formalizes -- the group-level genuine-corona predicate, the operator-MF
predicate, and both group C-star algebras. -/
theorem markedGroup_soficNonMF_package (hsofic : IsSofic MarkedGroup) :
    Group.IsFinitelyPresented MarkedGroup ∧
      IsSofic MarkedGroup ∧
      IsHyperlinear MarkedGroup ∧
      ¬ IsLEF MarkedGroup ∧
      ¬ Group.ResiduallyFinite MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup ∧
      ¬ IsOperatorMF MarkedGroup ∧
      ¬ IsMFAlgebra (MaximalGroupCStar MarkedGroup) ∧
      ¬ IsMFAlgebra (ReducedGroupCStarTrace.ReducedGroupCStar MarkedGroup) :=
  ⟨markedGroup_finitelyPresented,
    hsofic,
    isHyperlinear_of_isSofic hsofic,
    markedGroup_not_isLEF,
    markedGroup_not_residuallyFinite,
    LiteralNonMFEndpoint.literal_not_isCDEOperatorMF,
    LiteralNonMFEndpoint.literal_not_isOperatorMF,
    LiteralNonMFEndpoint.literal_maximalGroupCStar_not_isMFAlgebra,
    LiteralNonMFEndpoint.literal_reducedGroupCStar_not_isMFAlgebra⟩

/-!
## Integration target

The splitting lane pre-composes the re-association itself, so the integration
uses the plainest entry point of the three.  `LiteralLampKernelSplit` supplies

```
abbrev Telescope      := MappingTelescope.Telescope alpha conjD_injective
abbrev telescopeAction := SemidirectAssoc.baseAction
                            (shiftHom alpha conjD_injective) lampKernelAction
abbrev TelescopeCore  := lampKernel ⋊[telescopeAction] Telescope
abbrev stableAction   := SemidirectAssoc.outerAction
                            (shiftHom alpha conjD_injective) lampKernelAction

markedGroupEquivCoreByInt :
  MarkedGroup ≃* (TelescopeCore ⋊[stableAction] Multiplicative ℤ)
```

which is literally `isSofic_of_intSemidirectEquiv`'s hypothesis, so:

```
theorem markedGroup_isSofic
    (hcore : IsSofic LiteralLampKernelSplit.TelescopeCore) :
    IsSofic MarkedGroup :=
  isSofic_of_intSemidirectEquiv
    LiteralLampKernelSplit.markedGroupEquivCoreByInt hcore
```

`markedGroup_isSofic_of_towerEquiv` remains available for a splitting that
does *not* pre-compose the re-association; it performs the same
`SemidirectAssoc.assocEquiv` step internally.

The remaining premise `hcore` is `LiteralTelescopeCoreLEF.telescopeCore_isSofic
D`, since `telescopeCore D` is the `abbrev` `Lamp ⋊[D.action] Tel`.  It
discharges as soon as a `TelescopeCoreData` is built with

```
Lamp := LiteralLampKernelSplit.lampKernel
Tel  := LiteralLampKernelSplit.Telescope
D.action := LiteralLampKernelSplit.telescopeAction
```

the last being a `rfl` identification with `SemidirectAssoc.baseAction` -- the
same one `Sofic/SoficMarkedCompression.lean` makes at
`level_action_eq_baseAction`, whose comment records that `rw` cannot see
through the `MulAut` coercion, so it must be closed by defeq.  Building that
datum is the block, amalgam and LEF lanes' business; its
`subAmalgam_residuallyFinite` and `level_residuallyFinite` fields are the whole
of the endpoint's trust surface.

Note the base: this chain runs over `ExplicitLinearModel.gammaBar` with
`alpha = conjD`.  A block-geometry result instantiated instead at
`Monsters/AffineSL3Doubling.Gamma` is stated over a *different* carrier, and no
`MulEquiv` intertwining `conjD` with `AffineSL3Doubling.alpha` exists in the
repository; such results must be re-instantiated over `gammaBar` before they
can feed this datum.  Nothing in the soficity chain needs the doubling index to
be exactly `8` -- `MappingTelescopeFiniteOrbits` needs only
`[conjD.range.FiniteIndex]`, which `LiteralBaseDoublingIndex` provides.

The printed separation is

```
theorem markedGroup_finitelyPresented_sofic_nonMF :
    Group.IsFinitelyPresented MarkedGroup ∧ IsSofic MarkedGroup ∧
      ¬ IsCDEOperatorMF MarkedGroup :=
  markedGroup_finitelyPresented_sofic_not_isCDEOperatorMF markedGroup_isSofic
```

and it now exists, premise-free, as
`LiteralSoficAssembly.markedGroup_finitelyPresented_sofic_nonMF`: that module
supplies `markedGroup_isSofic` with no hypothesis and no literature input, and
imports this one to discharge the premise.  It is the declaration a numbered
manuscript theorem cites.  Nothing *in this file* asserts soficity of `E`
without a premise, by design -- the premise is what keeps the two routes to
soficity feeding one endpoint.
-/

end LiteralSoficEndpoint
end GroupApproximation
