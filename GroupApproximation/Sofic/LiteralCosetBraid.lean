import GroupApproximation.Sofic.LiteralLampKernelSplit
import GroupApproximation.Sofic.LiteralBlockGeometry
import GroupApproximation.Sofic.LiteralAffineCosetTransitivity

/-!
# The coset lamps braid through the mark

`notes/LITERAL_ORBITAL_CLIQUE_ROUTE.md` reduces soficity of the literal group
to a single `IsBlockCliffordPresentation` over the coset carrier, and lists its
six fields: three already available, three outstanding.  This module supplies
one of the three, `braid`.

## The statement

For sites of the orbital graph,

```text
Adj ξ η  →  ⁅cosetLamp ξ, cosetLamp η⁆ = mark .
```

Composed with `LiteralBlockGeometry.adj_of_blockOf_eq`, whose transitivity
hypothesis is discharged by `LiteralAffineCosetTransitivity`, this is exactly
the `braid` field: distinct sites of one block anticommute through the mark.

## Why it is short

Because adjacency is *defined* as the orbit of the marked pair, and the lamps
are equivariant.  So there are only two things to do:

* compute the commutator at the marked pair, where it is the marked word
  itself — `mark = ⁅tct⁻¹, a(tct⁻¹)a⁻¹⁆` is `mark_eq_markedCompressionWord`,
  and the two marked sites carry exactly the lamps `tct⁻¹` and its
  `a`-conjugate once `sect_t` and `sect_iota` are unfolded;
* transport along the orbit, where `cosetLamp_smul` turns each lamp into a
  conjugate, the commutator of two conjugates is the conjugate of the
  commutator, and centrality of the mark absorbs the conjugation.

The reversed order of the pair costs one extra step: `⁅y, x⁆ = ⁅x, y⁆⁻¹`, and
the mark is an involution.

## What this does not do

It does not supply `generated` or `lift`.  `lift` is the substantial one — the
universal property of the lamp kernel on the coset carrier — and
`LiteralLampKernelAmalgam.isBlockCliffordPresentation_lampFactor` is the model
for it on the presented carrier.
-/

namespace GroupApproximation
namespace LiteralCosetBraid

open LiteralNonMFPresentation LiteralNonMFLinearWitness LiteralLampKernelSplit
open LiteralBlockGeometry MarkedCompression
open ExplicitLinearModel LiteralBaseDoublingIndex
open scoped commutatorElement

/-! ## The marked pair -/

/-- The affine class of the displacing letter, transported into `E`, is the
literal base letter `v₁`. -/
private theorem affineToMarked_v1G :
    affineToMarked v1G = baseMap (PresentedGroup.of v1Index) := by
  have h := affineToMarked_affineQuotient LiteralBaseRelations.v1
  rwa [affineQuotient_v1] at h

/-- **The commutator at the marked pair is the mark.**  Unfolding the two
marked sites through `sect` recovers the marked compression word verbatim. -/
theorem braid_marked :
    ⁅cosetLamp (markedSiteA alpha conjD_injective),
      cosetLamp (markedSiteB alpha conjD_injective v1G)⁆ = mark := by
  rw [markedSiteA_eq_mk, markedSiteB_eq_mk, cosetLamp_mk, cosetLamp_mk,
    mark_eq_markedCompressionWord]
  simp only [siteLamp, markedCompressionWord, map_mul, sect_iota, sect_t,
    affineToMarked_v1G, commutatorElement_def]
  group

/-! ## Transport along the orbit -/

/-- The commutator of two conjugates is the conjugate of the commutator. -/
private theorem commutator_conj (g x y : MarkedGroup) :
    ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

/-- Conjugation does not move the central mark. -/
private theorem conj_mark (g : MarkedGroup) : g * mark * g⁻¹ = mark := by
  rw [← (mark_central g).eq]
  group

/-- The mark is its own inverse. -/
private theorem mark_inv : mark⁻¹ = mark :=
  inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact mark_sq)

/-- The braid relation on a translate of the marked pair, in the order in
which `Adj` presents it. -/
private theorem braid_smul_marked (g : Vertical alpha conjD_injective) :
    ⁅cosetLamp (g • markedSiteA alpha conjD_injective),
      cosetLamp (g • markedSiteB alpha conjD_injective v1G)⁆ = mark := by
  rw [cosetLamp_smul, cosetLamp_smul, commutator_conj, braid_marked, conj_mark]

/-- **Adjacent lamps braid through the mark.**  This is the `braid` field of
the block Clifford presentation over the coset carrier. -/
theorem braid_of_adj {ξ η : Cosets alpha conjD_injective}
    (h : Adj alpha conjD_injective v1G ξ η) :
    ⁅cosetLamp ξ, cosetLamp η⁆ = mark := by
  obtain ⟨g, hg | hg⟩ := h
  · rw [← hg.1, ← hg.2]
    exact braid_smul_marked g
  · have hswap : ⁅cosetLamp (g • markedSiteA alpha conjD_injective),
        cosetLamp (g • markedSiteB alpha conjD_injective v1G)⁆⁻¹ =
        ⁅cosetLamp (g • markedSiteB alpha conjD_injective v1G),
          cosetLamp (g • markedSiteA alpha conjD_injective)⁆ :=
      commutatorElement_inv _ _
    rw [← hg.2, ← hg.1, ← hswap, braid_smul_marked g]
    exact mark_inv

/-- **The block form.**  Distinct sites of a common block braid through the
mark: `LiteralBlockGeometry.adj_of_blockOf_eq` supplies the adjacency, and its
transitivity hypothesis is discharged by
`LiteralAffineCosetTransitivity.conjD_cosetTransitive`. -/
theorem braid_of_blockOf_eq {ξ η : Cosets alpha conjD_injective}
    (hblock : blockOf alpha conjD_injective ξ = blockOf alpha conjD_injective η)
    (hne : ξ ≠ η) :
    ⁅cosetLamp ξ, cosetLamp η⁆ = mark := by
  have htr : AlphaCosetTransitive alpha v1G :=
    LiteralAffineCosetTransitivity.conjD_cosetTransitive
  exact braid_of_adj (adj_of_blockOf_eq alpha conjD_injective htr hne hblock)

end LiteralCosetBraid
end GroupApproximation
