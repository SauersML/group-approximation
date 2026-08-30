import GroupApproximation.GGT.ElementaryClosure
import GroupApproximation.GGT.HullSCConeOffCyclicReduction
import GroupApproximation.GGT.HyperbolicFreeGroupAH

/-!
# A proper power is never hyperbolically embedded, and the clause that needs it

`GGT/HullSCConeOffCyclicReduction.lean` reduces Hull's Corollary 5.7 with Lemma
5.8, over a pair, to one geometric clause: that for **any** two independent
loxodromic elements of `Γ(G,A)` the cone-off of `A` along the cyclic subgroups
they generate is hyperbolically embedded.
`Manuscript/NonMF/TheoremCDebts.lean` records that clause as all that is left of
the row `hullHypEmbeddedConeOff`, and `ZpowersConeOffEmbedding` below is it,
named.

**It is false**, and this module proves it.  So that reduction is vacuous, and
the debt cannot be closed along it.

## The obstruction

`HullSC.not_isHyperbolicallyEmbedded_zpowers_pow`, of the cyclic-reduction
module itself, is the general fact: coning off `⟨a^n⟩` for `n ≥ 2` along an
alphabet containing `a` is never hyperbolically embedded, because `a` normalises
`⟨a^n⟩` and does not lie in it, so the three-letter word `a · (a⁻¹ k a) · a⁻¹`
puts every `k` of the subgroup into the relative ball of radius three.

That lemma is conditional: it wants a letter of infinite order inside an actual
`HullGeneratingSet`, and until now nothing in the tree exhibited one.  This
module supplies the missing half.

## The model

`HullSC.freeHullGeneratingSet` is Hull's data for a free group of rank two: the
basis alphabet, hyperbolic at `δ = 0` because the Cayley graph is a tree,
acylindrical because the alphabet is finite, non-elementary because two distinct
basis letters are independent loxodromics.  All three proofs are
`GGT/HyperbolicFreeGroupAH.lean`'s and are used rather than restated.  It is the
first inhabitant of `HullGeneratingSet` in the repository — every consumer of
Hull's Theorem 3.12 had until now run on a structure nothing was known to
satisfy.

Against it, `HullSC.not_zpowersConeOffEmbedding` refutes the clause with the
pair `(a², b)`, where `a = FreeGroup.of 0` and `b = FreeGroup.of 1`.  Both are
loxodromic — a positive power of a loxodromic is loxodromic — and independent,
since independence quantifies over all integer exponents and the exponents of
`a²` are a subfamily of those of `a`.  So the hypothesis applies and its
conclusion fails.

## Why this is not a transcription slip

It is Dahmani--Guirardel--Osin's Proposition 4.33 — a hyperbolically embedded
family is almost malnormal — biting at `g = a`: the conjugate `⟨a²⟩^a` is `⟨a²⟩`
itself, infinite, while `a ∉ ⟨a²⟩`.  `GGT/DGOProposition433Ball.lean` already
says as much in words for the `mu = lam`, `f ∈ H_lam` case.

## What survives

`HullSC.ExistsHypEmbeddedConeOff₂` itself is untouched: its family `K` is
existentially quantified, so `K b = E(g b)` is still available, and the four
cheap clauses of the reduction can be recovered at
`elementaryClosure (g b) ⊓ N`, where the containment in `N` is `inf_le_right`
and Hull's (W4) still follows from independence.  What the refutation removes is
the claim that the *cyclic* choice costs nothing: almost malnormality forces
`elementaryClosure (g b) = zpowers (g b)` for any pair the reduction could be
applied to, which is a real extra obligation on the choice of the two
loxodromics.

Clause (a) of the leaf is unaffected, and that is worth stating because it is
the check that the two results are consistent: the cone-off along `⟨a²⟩` really
is hyperbolic (`GGT/HullSCConeOffHeavyUnconditional.lean`), and what a proper
power fails is clause (b) alone.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Hull's data for a free group of rank two -/

/-- `Γ(F₂, A)` is `0`-hyperbolic: it is a tree. -/
theorem free_hyperbolic :
    IsHyperbolicSpace 0 (Cayley (GGT.freeGroupAlphabet (Fin 2))) :=
  GGT.isHyperbolicSpace_zero_cayley Hyperbolic.isTreeLike_freeAlphabet

/-- The translation action of `F₂` on `Γ(F₂, A)` is acylindrical: the alphabet
is finite, so the action is proper. -/
theorem free_acylindrical :
    IsAcylindrical (FreeGroup (Fin 2))
      (Cayley (GGT.freeGroupAlphabet (Fin 2))) := by
  have hfin : (Hyperbolic.freeAlphabet (Fin 2)).Finite := Set.finite_range _
  exact GGT.isAcylindrical_cayley_of_finite (GGT.freeGroupAlphabet (Fin 2)) hfin

/-- `F₂` acts non-elementarily on `Γ(F₂, A)`: the two basis letters are
independent loxodromics. -/
theorem free_nonElementary :
    ActsNonElementarily (⊤ : Subgroup (FreeGroup (Fin 2)))
      (Cayley.base (GGT.freeGroupAlphabet (Fin 2))) :=
  ⟨FreeGroup.of 0, Subgroup.mem_top _, FreeGroup.of 1, Subgroup.mem_top _,
    GGT.isLoxodromic_of_basis (a := (0 : Fin 2)) (b := (1 : Fin 2)) (by decide),
    GGT.isLoxodromic_of_basis (a := (1 : Fin 2)) (b := (0 : Fin 2)) (by decide),
    GGT.independent_of_basis (a := (0 : Fin 2)) (b := (1 : Fin 2)) (by decide)⟩

/-- **Hull's Theorem 3.12 data for a free group of rank two.**  Every field is a
theorem of `GGT/HyperbolicFreeGroupAH.lean`; nothing new is proved here.  This
is the model the refutation below runs on, and the first inhabitant of
`HullGeneratingSet` in the tree. -/
def freeHullGeneratingSet : HullGeneratingSet (FreeGroup (Fin 2)) where
  alphabet := GGT.freeGroupAlphabet (Fin 2)
  delta := 0
  hyperbolic := free_hyperbolic
  acylindrical := free_acylindrical
  nonElementary := free_nonElementary

/-! ## The refuted clause -/

/-- **The `∀`-form geometric clause of Hull's §5 for a pair, named.**

`GGT/HullSCConeOffCyclicReduction.lean` used to carry it as an inline binder,
whose docstring called it "the sharpest form of what Hull's §5 for a pair still
owes".  Naming it is what lets `not_zpowersConeOffEmbedding` refute it, and
`existsHypEmbeddedConeOff₂_of_zpowersConeOffEmbedding` records that it really
would have closed the row. -/
def ZpowersConeOffEmbedding : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (g : Bool → G),
    (∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet)) →
      Independent (g false) (g true) (Cayley.base A.alphabet) →
        (coneOffFamily A.alphabet
          (fun b => Subgroup.zpowers (g b))).IsHyperbolicallyEmbedded

/-- **The named clause would close the leaf.**  The suitable subgroup supplies
the two independent loxodromics (`exists_independent_lox_of_suitable`) and
`existsHypEmbeddedConeOff₂_of_zpowers` supplies the other four conditions, so
`ZpowersConeOffEmbedding` really is a reduction of the row and not a weakening
of it.  That is what makes the refutation below informative rather than a remark
about a statement nobody wanted. -/
theorem existsHypEmbeddedConeOff₂_of_zpowersConeOffEmbedding
    (h : ZpowersConeOffEmbedding.{u}) : ExistsHypEmbeddedConeOff₂.{u} := by
  refine existsHypEmbeddedConeOff₂_of_zpowers ?_
  intro G _ A N hN
  obtain ⟨g, hgN, hglox, hind⟩ := exists_independent_lox_of_suitable hN
  exact ⟨g, hgN, hglox, hind, h A g hglox hind⟩

/-- **The clause is false.**

At `G = F₂` with Hull's own alphabet, `a²` and `b` are independent loxodromics,
but the cone-off along `⟨a²⟩` and `⟨b⟩` is not hyperbolically embedded, by
`not_isHyperbolicallyEmbedded_zpowers_pow` at `n = 2`: `a` is a letter of the
alphabet, has infinite order because it is loxodromic, and lies outside `⟨a²⟩`.

So the row `Manuscript.NonMF.TorsionFree.hullHypEmbeddedConeOff` does not reduce
to this clause, and any reduction that produces it is vacuous. -/
theorem not_zpowersConeOffEmbedding : ¬ ZpowersConeOffEmbedding.{0} := by
  intro h
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  have hloxa : IsLoxodromic (FreeGroup.of (0 : Fin 2))
      (Cayley.base freeHullGeneratingSet.alphabet) :=
    GGT.isLoxodromic_of_basis (a := (0 : Fin 2)) (b := (1 : Fin 2)) h01
  have hzp : ∀ n : ℤ, (FreeGroup.of (0 : Fin 2) ^ (2 : ℕ)) ^ n
      = FreeGroup.of (0 : Fin 2) ^ (2 * n) := by
    intro n
    have h2 : FreeGroup.of (0 : Fin 2) ^ (2 : ℕ)
        = FreeGroup.of (0 : Fin 2) ^ (2 : ℤ) := by
      rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from by norm_num, zpow_natCast]
    rw [h2, ← zpow_mul]
  have hlox : ∀ b : Bool,
      IsLoxodromic
        (bif b then FreeGroup.of (1 : Fin 2)
          else FreeGroup.of (0 : Fin 2) ^ (2 : ℕ))
        (Cayley.base freeHullGeneratingSet.alphabet) := by
    intro b
    cases b
    · show IsLoxodromic (FreeGroup.of (0 : Fin 2) ^ (2 : ℕ))
        (Cayley.base freeHullGeneratingSet.alphabet)
      exact isLoxodromic_pow hloxa (by norm_num)
    · show IsLoxodromic (FreeGroup.of (1 : Fin 2))
        (Cayley.base freeHullGeneratingSet.alphabet)
      exact GGT.isLoxodromic_of_basis (a := (1 : Fin 2)) (b := (0 : Fin 2)) h10
  have hind : Independent (FreeGroup.of (0 : Fin 2) ^ (2 : ℕ))
      (FreeGroup.of (1 : Fin 2))
      (Cayley.base freeHullGeneratingSet.alphabet) := by
    obtain ⟨C, hC⟩ := GGT.independent_of_basis (a := (0 : Fin 2))
      (b := (1 : Fin 2)) h01
    refine ⟨C, ?_⟩
    intro n m
    have hstep := hC (2 * n) m
    rw [← hzp n] at hstep
    exact hstep
  have hbase : FreeGroup.of (0 : Fin 2) ∈ freeHullGeneratingSet.alphabet.carrier :=
    Hyperbolic.letterOf_mem ((0 : Fin 2), true)
  have hord : ¬ IsOfFinOrder (FreeGroup.of (0 : Fin 2)) :=
    not_isOfFinOrder_of_isLoxodromic hloxa
  have hemb := h freeHullGeneratingSet
    (fun c : Bool => bif c then FreeGroup.of (1 : Fin 2)
      else FreeGroup.of (0 : Fin 2) ^ (2 : ℕ)) hlox hind
  exact not_isHyperbolicallyEmbedded_zpowers_pow
    freeHullGeneratingSet.alphabet _ false (a := FreeGroup.of (0 : Fin 2))
    hbase hord (n := 2) (by norm_num) rfl hemb

end HullSC
end GroupApproximation
