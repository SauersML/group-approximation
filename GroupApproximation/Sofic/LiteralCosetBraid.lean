import GroupApproximation.Sofic.LiteralLampKernelSplit
import GroupApproximation.Sofic.LiteralBlockGeometry

/-!
# The coset lamps braid through the mark

`docs/LITERAL_ORBITAL_CLIQUE_ROUTE.md` reduces soficity of the literal group
to a single `IsBlockCliffordPresentation` over the coset carrier, and lists its
six fields: three already available, three outstanding.  This module supplies
one of the three, `braid`.

## The statement

For sites of the orbital graph,

```text
Adj ξ η  →  ⁅cosetLamp ξ, cosetLamp η⁆ = mark .
```

Composed with `LiteralBlockGeometry.adj_of_blockOf_eq`, whose transitivity
hypothesis is discharged by `alphaCosetTransitive`, this is exactly the
`braid` field: distinct sites of one block anticommute through the mark.

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

Never compiled.
-/

namespace GroupApproximation
namespace LiteralCosetBraid

open LiteralNonMFPresentation LiteralLampKernelSplit
open LiteralBlockGeometry MarkedCompression
open ExplicitLinearModel LiteralBaseDoublingIndex
open scoped commutatorElement

/-! ## The marked pair -/

/-- **The commutator at the marked pair is the mark.**  Unfolding the two
marked sites through `sect` recovers the marked compression word verbatim. -/
theorem braid_marked :
    ⁅cosetLamp (markedSiteA alpha conjD_injective),
      cosetLamp (markedSiteB alpha conjD_injective v1G)⁆ = mark := by
  rw [markedSiteA, markedSiteB, cosetLamp_smul, cosetLamp_smul,
    cosetLamp_rootCoset, map_mul, sect_iota, sect_t,
    ← affineQuotient_v1, affineToMarked_affineQuotient,
    mark_eq_markedCompressionWord, markedCompressionWord]

/-! ## Transport along the orbit -/

/-- The commutator of two conjugates is the conjugate of the commutator. -/
private theorem commutator_conj (g x y : MarkedGroup) :
    ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * ⁅x, y⁆ * g⁻¹ := by
  simp only [commutatorElement_def]
  group

/-- **Adjacent lamps braid through the mark.**  This is the `braid` field of
the block Clifford presentation over the coset carrier. -/
theorem braid_of_adj {ξ η : Cosets alpha conjD_injective}
    (h : Adj alpha conjD_injective v1G ξ η) :
    ⁅cosetLamp ξ, cosetLamp η⁆ = mark := by
  obtain ⟨g, hg | hg⟩ := h
  · obtain ⟨ha, hb⟩ := hg
    rw [← ha, ← hb, cosetLamp_smul, cosetLamp_smul, commutator_conj,
      braid_marked]
    exact (mark_central (sect g)).eq ▸ by group
  · obtain ⟨ha, hb⟩ := hg
    rw [← ha, ← hb] at *
    have hswap : ⁅cosetLamp (g • markedSiteB alpha conjD_injective v1G),
        cosetLamp (g • markedSiteA alpha conjD_injective)⁆ =
        ⁅cosetLamp (g • markedSiteA alpha conjD_injective),
          cosetLamp (g • markedSiteB alpha conjD_injective v1G)⁆⁻¹ :=
      (commutatorElement_inv _ _).symm
    rw [hswap, cosetLamp_smul, cosetLamp_smul, commutator_conj, braid_marked]
    have hinv : (sect g * mark * (sect g)⁻¹)⁻¹ = mark := by
      rw [← (mark_central (sect g)).eq]
      have : sect g * mark * (sect g)⁻¹ = mark := by
        rw [← (mark_central (sect g)).eq]; group
      rw [this]
      exact inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact mark_sq)
    exact hinv

/-- **The block form.**  Distinct sites of a common block braid through the
mark: `LiteralBlockGeometry.adj_of_blockOf_eq` supplies the adjacency, and its
transitivity hypothesis is discharged by `alphaCosetTransitive`. -/
theorem braid_of_blockOf_eq {ξ η : Cosets alpha conjD_injective}
    (hblock : blockOf alpha conjD_injective ξ = blockOf alpha conjD_injective η)
    (hne : ξ ≠ η) :
    ⁅cosetLamp ξ, cosetLamp η⁆ = mark :=
  braid_of_adj (adj_of_blockOf_eq alpha conjD_injective
    LiteralAffineCosetTransitivity.conjD_cosetTransitive hne hblock)

end LiteralCosetBraid
end GroupApproximation
