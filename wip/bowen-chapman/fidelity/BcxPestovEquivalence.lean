/-
`IsSoficGroup` is exactly the textbook definition of a sofic group.
Fidelity driver, unwired: no lake target builds files under wip/.  Compiled
green on MSI on 2026-09-12, 21:28-21:31 CDT, against the origin/main bytes of
d71ae9349.

Build:
  lake build PalomarBowenChapmanSolution
  lake env lean <path>/BcxPestovEquivalence.lean

Why this matters for the challenge.  The theorem concludes `¬ IsSoficGroup`.
If `IsSoficGroup` were STRONGER than soficity, `¬ IsSoficGroup` would be WEAKER
than nonsoficity and the challenge would claim less than it says.  The shared
block's `IsSoficGroup` differs on its face from the textbook conditions:

* it demands `d(σ(gh), σ(g)σ(h)) ≤ ε` for all `g, h ∈ F`, where the textbook
  (Pestov, *Hyperlinear and sofic groups: a brief guide*, arXiv:0804.3968,
  Theorem 3.5(1)) demands it only when `gh ∈ F` as well;
* it demands separation `1 - ε`, where the textbook (ibid. 3.5(3)) demands only
  the fixed constant `1/4`;
* it omits the textbook's `d(σ(1), Id) < ε` (ibid. 3.5(2)).

`isSoficGroup_iff_isPestovSofic` below settles all three at once, for an
arbitrary group in `Type`, with no countability premise: the two are equivalent.
-/
import Palomar.BowenChapmanSolution
import GroupApproximation.Sofic.SoficAmplification

namespace BowenChapman

open GroupApproximation
open scoped Pointwise

variable {G : Type} [Group G]

/-- Pestov, Theorem 3.5, conditions (1) and (3): multiplicativity is required
only where the tested product stays in the test set, and the separation is the
fixed constant `1/4`. -/
structure PestovModel (G : Type) [Group G] (F : Finset G) (ε : ℝ) where
  carrier : FiniteCarrier
  nonempty : 0 < Fintype.card carrier
  map : G → Equiv.Perm carrier
  multiplicative : ∀ g ∈ F, ∀ h ∈ F, g * h ∈ F →
    hammingDist carrier (map (g * h)) (map g * map h) ≤ ε
  separated : ∀ g ∈ F, ∀ h ∈ F, g ≠ h →
    1 / 4 ≤ hammingDist carrier (map g) (map h)

/-- Soficity in the textbook form. -/
def IsPestovSofic (G : Type) [Group G] : Prop :=
  ∀ (F : Finset G) (ε : ℝ), 0 < ε → Nonempty (PestovModel G F ε)

/-- The shared block's soficity gives the textbook form. -/
theorem isPestovSofic_of_isSoficGroup (h : IsSoficGroup G) : IsPestovSofic G := by
  intro F ε hε
  obtain ⟨Y, σ, hY, hmul, hsep⟩ := h F (min ε (1 / 2)) (lt_min hε (by norm_num))
  refine ⟨{ carrier := Y, nonempty := hY, map := σ,
            multiplicative := ?_, separated := ?_ }⟩
  · intro g hg h' hh' _
    exact (hmul g hg h' hh').trans (min_le_left _ _)
  · intro g hg h' hh' hne
    have hs := hsep g hg h' hh' hne
    have hm : min ε (1 / 2) ≤ 1 / 2 := min_le_right _ _
    linarith

/-- The textbook form gives the shared block's soficity.  Enlarging the test
set by `F * F` removes the product restriction; the development's tensor-power
amplification (`isSofic_of_isSoficWeak`) raises the separation from `1/4` to
`1 - ε`. -/
theorem isSoficGroup_of_isPestovSofic (h : IsPestovSofic G) : IsSoficGroup G := by
  classical
  rw [isSoficGroup_iff_isSofic]
  refine isSofic_of_isSoficWeak (δ := 1 / 4) (by norm_num) ?_
  intro F ε hε
  obtain ⟨P⟩ := h (F ∪ F * F) ε hε
  refine ⟨{ carrier := ⟨P.carrier.carrier, P.carrier.fintype, P.carrier.decidableEq⟩
            nonempty := P.nonempty
            map := P.map
            multiplicative := ?_
            separated := ?_ }⟩
  · intro g hg h' hh'
    exact P.multiplicative g (Finset.mem_union_left _ hg) h' (Finset.mem_union_left _ hh')
      (Finset.mem_union_right F (Finset.mul_mem_mul hg hh'))
  · intro g hg h' hh' hne
    exact P.separated g (Finset.mem_union_left _ hg) h' (Finset.mem_union_left _ hh') hne

/-- **The challenge's soficity is the textbook soficity**, for every group in
`Type`, countable or not. -/
theorem isSoficGroup_iff_isPestovSofic : IsSoficGroup G ↔ IsPestovSofic G :=
  ⟨isPestovSofic_of_isSoficGroup, isSoficGroup_of_isPestovSofic⟩

/-- The same conclusion routed through the development's two convention
lemmas, as a cross-check. -/
theorem isSoficGroup_iff_weak_quarter : IsSoficGroup G ↔ IsSoficWeak G (1 / 4) :=
  isSoficGroup_iff_isSofic.trans isSofic_iff_weak_quarter

theorem isSoficGroup_iff_productRestricted :
    IsSoficGroup G ↔ IsSoficProductRestricted G :=
  isSoficGroup_iff_isSofic.trans (isSofic_iff_productRestricted G)

end BowenChapman
