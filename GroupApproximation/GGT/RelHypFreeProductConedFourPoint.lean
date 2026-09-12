import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.HullSCUnionGeometryFourPoint

/-!
# Farb's clause for the free product, proved: the coned-off alphabet is a union
alphabet

`GGT/RelHypDefinition.lean` states `FreeProductRelativelyHyperbolicStatement` --
Osin, Memoirs 179 (2006), Theorem 2.34; Bowditch, *Relatively hyperbolic
groups*, §9 -- as the one geometric citation of the Fournier-Facio quotient
sentence, and its docstring describes the intended proof:

> coning off the cosets of `U` collapses the `U`-vertex spaces to points,
> leaving a tree of copies of `Γ(H, X)` glued along single points, which is
> hyperbolic because `H` is.

**That is a theorem of this repository already**, in a different vocabulary.
`GGT/HullSCUnionGeometryFourPoint.isFourPointHyperbolic_unionCarrier` proves the
four-point condition for the union alphabet of a free product at the constant of
its factors, with -- in its own words -- "no finiteness of any kind": the factor
alphabets may be infinite.  This module observes that the coned-off relative
alphabet `X ⊔ ℋ` of `(U ∗ H, U)` **is** a union alphabet, namely the one whose
peripheral-factor letters are *all of `U`* and whose partner-factor letters are
`X`, and reads Osin's Theorem 2.34 off it.

So the citation is retired, not weakened.  With
`GGT/RelHypFreeProductPeripheral.lean` supplying the Dahmani--Guirardel--Osin
clause (the induced metric on the peripheral factor is discrete) and
`GGT/CayleyFourPointBridge.lean` supplying the passage from the `ℕ`-valued max
form on `wordDist` to the `ℝ`-valued min form on `gromovProduct`, all three legs
are now proved and `FreeProductRelativelyHyperbolicStatement` is a theorem.

## Why the peripheral factor costs one unit of `δ` and nothing else

The peripheral factor's alphabet is the whole group `U`, so its word metric has
`|u| ≤ 1` for every `u` and its Cayley graph has diameter one.  A space of
diameter one satisfies the four-point condition at `δ = 1` for the reason
`Hyperbolic.isFourPointHyperbolic_of_bounded` records: the left side of the
inequality is at most `2`, and `2 · 1` is already on the right.  So the union
runs at `max δ 1`, and no geometry of `U` is used or needed -- which is as it
must be, since `U` in the application is an arbitrary finitely presented
torsion-free group and has no geometry to offer.

The one thing that is *not* free is the identification of the two alphabets, and
it is only bookkeeping: `RelativeGeneratingSet.alphabet` is
`X.carrier ∪ ⋃ l, ↑(H l)` while `FreeProductUnionNorm.unionCarrier` is
`{x | ∃ i, ∃ a ∈ S i, of a = x}`, and at the two-factor family with `S false`
all of `U` these are the same set.  `alphabet_carrier_freeProductRelGen` is that
equality.

## What this does not do

It says nothing about a general relatively hyperbolic pair.  The union-alphabet
theorem is a statement about free products, and the tree directions of a free
product are what make the constant survive; a pair `(G, {H_λ})` that is not a
free product has no such splitting and Theorem 2.34 for it is untouched.  The
Fournier-Facio paragraph needs only the free-product case.
-/

namespace GroupApproximation
namespace GGT
namespace RelHyp

open Monoid
open GroupApproximation.WordMetric
open GroupApproximation.FreeProductUnionNorm

/-! ## 1.  The whole of a group, as an alphabet -/

/-- **The whole of a group is a symmetric generating set.**  Not the `Finset`
form of `Hyperbolic.isSymmetricGeneratingSet_univ`: the peripheral factor of the
Fournier-Facio pair is infinite, and its alphabet is all of it. -/
theorem isSymmetricGeneratingSet_setUniv (G : Type) [Group G] :
    IsSymmetricGeneratingSet (Set.univ : Set G) :=
  ⟨fun x _ => Set.mem_univ x⁻¹, Subgroup.closure_univ⟩

/-- **A group spelled by whole elements is `1`-hyperbolic.**  Every element is a
letter, so the metric has diameter one and the four-point inequality has at most
`2` on its left. -/
theorem isFourPointHyperbolic_setUniv (G : Type) [Group G] :
    Hyperbolic.IsFourPointHyperbolic (Set.univ : Set G) 1 := by
  refine Hyperbolic.isFourPointHyperbolic_of_bounded
    (S := (Set.univ : Set G)) (B := 1) ?_
  intro x y
  have h : wordNorm (Set.univ : Set G) (x⁻¹ * y) ≤ 1 :=
    wordNorm_le_one_of_mem (Set.mem_univ _)
  exact h

/-! ## 2.  The two factor alphabets of the coned-off graph -/

/-- **The factor alphabets of `Γ(U ∗ H, X ⊔ ℋ)`**: the whole of the peripheral
factor, and the finite generating set of the partner factor.

Osin's asymmetry, as a choice of alphabet rather than as an axiom on a length
function: a peripheral element is one letter however long it is, because the
peripheral factor contributes every one of its elements as a letter. -/
def conedFactorAlphabet (U H : Type) (S : Finset H) :
    ∀ b : Bool, Set (pairFamily U H b)
  | false => Set.univ
  | true => (S : Set H)

theorem conedFactorAlphabet_false (U H : Type) (S : Finset H) :
    conedFactorAlphabet U H S false = (Set.univ : Set U) := rfl

theorem conedFactorAlphabet_true (U H : Type) (S : Finset H) :
    conedFactorAlphabet U H S true = (S : Set H) := rfl

/-- Both factor alphabets are symmetric generating sets. -/
theorem isSymmetricGeneratingSet_conedFactorAlphabet (U H : Type) [Group U]
    [Group H] {S : Finset H} (hS : IsSymmetricGeneratingSet (S : Set H)) :
    ∀ b, IsSymmetricGeneratingSet (conedFactorAlphabet U H S b) := by
  intro b
  cases b with
  | false =>
      have h : IsSymmetricGeneratingSet
          (Set.univ : Set (pairFamily U H false)) :=
        isSymmetricGeneratingSet_setUniv (pairFamily U H false)
      exact h
  | true => exact hS

/-- Both factor alphabets satisfy the four-point condition at `max δ 1`: the
partner factor at its own constant, the peripheral factor because its metric is
bounded by one. -/
theorem isFourPointHyperbolic_conedFactorAlphabet (U H : Type) [Group U]
    [Group H] {S : Finset H} {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic (S : Set H) δ) :
    ∀ b, Hyperbolic.IsFourPointHyperbolic (conedFactorAlphabet U H S b)
      (max δ 1) := by
  intro b
  cases b with
  | false =>
      have h : Hyperbolic.IsFourPointHyperbolic
          (Set.univ : Set (pairFamily U H false)) 1 :=
        isFourPointHyperbolic_setUniv (pairFamily U H false)
      exact h.mono (le_max_right δ 1)
  | true => exact hδ.mono (le_max_left δ 1)

/-! ## 3.  The relative alphabet is the union alphabet -/

/-- **The coned-off relative alphabet of `(U ∗ H, U)` is a union alphabet.**

`RelativeGeneratingSet.alphabet` writes it as `X ∪ ⋃ l, H l` and
`FreeProductUnionNorm.unionCarrier` writes it as the letters of each factor
inside that factor; at the two-factor family, with the peripheral factor
contributing all of itself, the two descriptions name the same set. -/
theorem alphabet_carrier_freeProductRelGen (U H : Type) [Group U] [Group H]
    (S : Finset H) (hS : IsSymmetricGeneratingSet (S : Set H)) :
    (freeProductRelGen U H S hS).alphabet.carrier
      = unionCarrier (conedFactorAlphabet U H S) := by
  ext x
  constructor
  · intro hx
    rw [RelativeGeneratingSet.alphabet_carrier] at hx
    rcases hx with hx | hx
    · have himg : x ∈ (pairRelGen (G := pairFamily U H) S hS).carrier := hx
      rw [pairRelGen_carrier] at himg
      obtain ⟨s, hs, rfl⟩ := himg
      refine ⟨true, s, ?_, rfl⟩
      exact hs
    · rw [Set.mem_iUnion] at hx
      obtain ⟨-, hu⟩ := hx
      have hu' : x ∈ pairPeripheral (pairFamily U H) := hu
      obtain ⟨u, rfl⟩ := mem_pairPeripheral.mp hu'
      refine ⟨false, u, ?_, rfl⟩
      exact Set.mem_univ u
  · intro hx
    obtain ⟨i, a, ha, rfl⟩ := hx
    cases i with
    | false =>
        exact (freeProductRelGen U H S hS).peripheral_subset_alphabet ()
          (of_mem_pairPeripheral (G := pairFamily U H) a)
    | true =>
        refine (freeProductRelGen U H S hS).subset_alphabet ?_
        have hmem : (CoprodI.of a : CoprodI (pairFamily U H))
            ∈ (pairRelGen (G := pairFamily U H) S hS).carrier := by
          rw [pairRelGen_carrier]
          refine ⟨a, ?_, rfl⟩
          exact ha
        exact hmem

/-! ## 4.  Osin's Theorem 2.34 for the free product -/

/-- **Farb's clause for the free product, at the sharp constant.**

The coned-off Cayley graph `Γ(U ∗ H, X ⊔ U)` satisfies the four-point condition
at `max δ 1`, where `δ` is the constant of `H` at the very generating set `X`
that `IsHyperbolicGroup H` supplies.  No transport between generating sets, and
so no Morse lemma; no finiteness of the peripheral alphabet, and so no
restriction on `U`.

Stated with the constant exposed rather than bound existentially, because a
consumer that has to *build* over this graph -- Fournier-Facio's Proposition 2.3
choosing its relators -- needs the constant and the alphabet, not their
existence. -/
theorem isFourPointHyperbolic_freeProductRelGen (U H : Type) [Group U] [Group H]
    (S : Finset H) (hS : IsSymmetricGeneratingSet (S : Set H)) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic (S : Set H) δ) :
    Hyperbolic.IsFourPointHyperbolic
      (freeProductRelGen U H S hS).alphabet.carrier (max δ 1) := by
  haveI := pairFamilyDecEq U H
  have hmain : Hyperbolic.IsFourPointHyperbolic
      (unionCarrier (conedFactorAlphabet U H S)) (max δ 1) :=
    HullSCUnionGeometry.isFourPointHyperbolic_unionCarrier
      (isSymmetricGeneratingSet_conedFactorAlphabet U H hS)
      (isFourPointHyperbolic_conedFactorAlphabet U H hδ)
  rw [alphabet_carrier_freeProductRelGen U H S hS]
  exact hmain

/-- **Farb's clause for the free product, proved.** -/
theorem freeProductConedFourPointStatement_proved :
    FreeProductConedFourPointStatement := by
  intro U H instU instH S hS δ hδ
  exact ⟨max δ 1, isFourPointHyperbolic_freeProductRelGen U H S hS hδ⟩

/-- **`FreeProductConedHyperbolicStatement`, proved.**  The `ℝ`-valued min form,
through `GGT/CayleyFourPointBridge.lean`. -/
theorem freeProductConedHyperbolicStatement_proved :
    FreeProductConedHyperbolicStatement :=
  freeProductConedHyperbolicStatement_of_fourPoint
    freeProductConedFourPointStatement_proved

/-- **Osin, Memoirs 179 (2006), Theorem 2.34, for the free product: proved.**

`U ∗ H` is hyperbolic relative to `U` whenever `H` is word hyperbolic.  This
retires the third of the three named `Prop`s that every generation of the
Fournier-Facio quotient discharge has carried; what remains of that sentence is
Osin's small-cancellation theorem and Fournier-Facio's Proposition 2.3. -/
theorem freeProductRelativelyHyperbolicStatement_proved :
    FreeProductRelativelyHyperbolicStatement :=
  freeProductRelativelyHyperbolicStatement_of_fourPoint
    freeProductConedFourPointStatement_proved

end RelHyp
end GGT
end GroupApproximation
