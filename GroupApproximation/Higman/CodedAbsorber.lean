import GroupApproximation.Higman.EvalRaw
import GroupApproximation.Computability.PresentationCodeCompleteness
import GroupApproximation.Algebra.TorsionFreeQuotient
import Mathlib.Data.DFinsupp.Encodable

/-!
# An absorber indexed by the *Primcodable* presentation codes

`Higman.Program`'s split (B1) asks for a recursive presentation of
`Monsters.CodedDirectSum`, the restricted direct product of the groups of all
finite presentation codes.  Its index type is
`Monsters.FinitePresentationCode = Σ n, Finset (FreeGroup (Fin n))`, which is
countable but is **not** a `Primcodable` type: its elements are finite sets of
elements of a quotient type, so nothing computable enumerates it, and a
recursive presentation needs a computable enumeration of generators.

That obstruction is an artefact of the index, not of the mathematics.  This
repository already has a `Primcodable` datatype of finite presentations,
`Computability.PresentationCodes.PresentationCode = ℕ × List (List (ℕ × Bool))`,
with an interpretation `Carrier` and --- crucially --- an *adequacy* theorem,
`PresentationCodes.exists_code_mulEquiv`: every finitely presented group is
`Carrier c` for some code.  Indexing the absorber by that type instead gives
the same absorbing group, with an index over which one can actually compute.

## What is here

Everything `Monsters.ChiodoTorsionFreeAbsorber` proves, over the Primcodable
index: the restricted direct product `PCDirectSum`, the coordinate retraction,
the torsion-free quotient `PCAbsorber`, and the absorbing property, all
unconditional.  Then the part that the old index made impossible:

* `codeOfNat` --- an explicit surjection `ℕ → PresentationCode`, namely
  `Encodable.decode` with a default.  It is computable, because
  `PresentationCode` is `Primcodable`.
* `pcGen` --- an explicit family `ℕ → PCDirectSum`, built from `codeOfNat`
  and `PresentationCodes.letterOf`, the total letter function the coding
  already carries for exactly this reason.
* `spans_pcGen` --- it generates.

So the two structural fields of a `Higman.RecursivePresentation PCAbsorber`
are in place and are given by explicit formulas.  What is left of (B1) is the
third field alone: recursive enumerability of
`{w | evalRaw pcGen w = 1}`, for which `Higman.EvalRaw` supplies the
coordinatewise criterion and the finiteness of the set of relevant blocks, and
`Computability.WordProblemRE.rePred_wordProblemPred` supplies each block's
condition.  That is not proved here.

## Relation to the other two absorbers

Three absorbers now exist, all countable, torsion-free and absorbing, all
proved so unconditionally, differing only in index and carrier:
`Monsters.ChiodoAbsorber` (direct sum over the Type-level codes),
`Monsters.ChiodoFreeAbsorber` (free product over the same), and `PCAbsorber`
(direct sum over the Primcodable codes).  The third is the one to feed to
Chiodo's Theorem 2.2, because it is the only one whose generating family is
written down as a computable formula.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.Chiodo
open GroupApproximation.PresentationCodes

/-! ## 1.  Countability of the coded groups -/

instance carrier_countable (c : PresentationCode) : Countable (Carrier c) := by
  unfold Carrier PresentedGroup
  exact Function.Surjective.countable (QuotientGroup.mk'_surjective _)

instance carrier_additive_countable (c : PresentationCode) :
    Countable (Additive (Carrier c)) :=
  Countable.of_equiv (Carrier c) Additive.ofMul

/-! ## 2.  The restricted direct product -/

/-- The restricted direct product of the groups of all Primcodable
presentation codes. -/
def PCDirectSum : Type :=
  Multiplicative (Π₀ c : PresentationCode, Additive (Carrier c))

instance pcDirectSum_group : Group PCDirectSum := by
  unfold PCDirectSum
  infer_instance

instance pcDirectSum_countable : Countable PCDirectSum := by
  unfold PCDirectSum
  exact Countable.of_equiv
    (Π₀ c : PresentationCode, Additive (Carrier c)) Multiplicative.ofAdd

/-- The inclusion of one coordinate. -/
noncomputable def pcOf (c : PresentationCode) : Carrier c →* PCDirectSum := by
  classical
  exact
    { toFun := fun x ↦
        Multiplicative.ofAdd (DFinsupp.single c (Additive.ofMul x))
      map_one' := by
        change Multiplicative.ofAdd
            (DFinsupp.single c (Additive.ofMul (1 : Carrier c))) =
          Multiplicative.ofAdd
            (0 : (Π₀ i : PresentationCode, Additive (Carrier i)))
        apply Multiplicative.ofAdd.injective
        simp
      map_mul' := by
        intro x y
        change Multiplicative.ofAdd
            (DFinsupp.single c (Additive.ofMul (x * y))) =
          Multiplicative.ofAdd
            ((DFinsupp.single c (Additive.ofMul x) :
                (Π₀ i : PresentationCode, Additive (Carrier i))) +
              (DFinsupp.single c (Additive.ofMul y) :
                (Π₀ i : PresentationCode, Additive (Carrier i))))
        exact congrArg Multiplicative.ofAdd
          (DFinsupp.single_add
            (β := fun i : PresentationCode ↦ Additive (Carrier i)) c
            (Additive.ofMul x) (Additive.ofMul y)) }

/-- Evaluation at one coordinate: the retraction the construction runs on. -/
noncomputable def pcEval (c : PresentationCode) : PCDirectSum →* Carrier c where
  toFun q := Additive.toMul (Multiplicative.toAdd q c)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem pcEval_pcOf (c : PresentationCode) (x : Carrier c) :
    pcEval c (pcOf c x) = x := by
  classical
  simp [pcOf, pcEval]

theorem pcOf_injective (c : PresentationCode) : Function.Injective (pcOf c) := by
  intro x y hxy
  have h := congrArg (pcEval c) hxy
  rwa [pcEval_pcOf, pcEval_pcOf] at h

/-! ## 3.  The absorber -/

/-- The absorber over the Primcodable index. -/
abbrev PCAbsorber : Type := TorsionFreeQuotient PCDirectSum

theorem pcAbsorber_torsionFree : IsPowerTorsionFree PCAbsorber :=
  isPowerTorsionFree_torsionFreeQuotient

instance pcAbsorber_countable : Countable PCAbsorber :=
  Function.Surjective.countable toTorsionFreeQuotient_surjective

/-- The map placing one coordinate into the absorber. -/
noncomputable def pcEmb (c : PresentationCode) : Carrier c →* PCAbsorber :=
  (toTorsionFreeQuotient PCDirectSum).comp (pcOf c)

/-- A torsion-free coordinate survives the quotient, by the retraction
principle. -/
theorem pcEmb_injective (c : PresentationCode)
    (hc : IsPowerTorsionFree (Carrier c)) : Function.Injective (pcEmb c) := by
  unfold pcEmb
  exact injective_of_retraction hc (pcOf c) (pcEval c) (pcEval_pcOf c)

/-- **The absorbing property.**  Every finitely presented torsion-free group
embeds in `PCAbsorber`.  Adequacy of the coding is
`PresentationCodes.exists_code_mulEquiv`. -/
theorem embeds_pcAbsorber (Q : Type) [Group Q] [Group.IsFinitelyPresented Q]
    (hQ : IsPowerTorsionFree Q) :
    ∃ f : Q →* PCAbsorber, Function.Injective f := by
  obtain ⟨c, ⟨e⟩⟩ := exists_code_mulEquiv Q
  have hc : IsPowerTorsionFree (Carrier c) :=
    IsPowerTorsionFree.comap hQ e.toMonoidHom e.injective
  exact ⟨(pcEmb c).comp e.symm.toMonoidHom,
    (pcEmb_injective c hc).comp e.symm.injective⟩

/-- The absorbing property in the shape the reduction consumes. -/
theorem universal_of_embedding_pcAbsorber {P : Type} [Group P]
    (g : PCAbsorber →* P) (hg : Function.Injective g) :
    ∀ (Q : Type) [Group Q] [Group.IsFinitelyPresented Q],
      IsPowerTorsionFree Q → ∃ f : Q →* P, Function.Injective f := by
  intro Q _ _ hQ
  obtain ⟨f, hf⟩ := embeds_pcAbsorber Q hQ
  exact ⟨g.comp f, hg.comp hf⟩

/-! ## 4.  An explicit generating family -/

/-- An explicit surjection `ℕ → PresentationCode`: decode, with a default.
Computable, because `PresentationCode` is `Primcodable`. -/
def codeOfNat (n : ℕ) : PresentationCode :=
  (Encodable.decode (α := PresentationCode) n).getD (0, [])

theorem codeOfNat_surjective : Function.Surjective codeOfNat := by
  intro c
  exact ⟨Encodable.encode c, by simp [codeOfNat]⟩

/-- **The generating family.**  The `n`-th generator is the `k`-th generator
of the `m`-th code, where `(m, k)` is the Cantor unpairing of `n`, using the
coding's own total letter function `PresentationCodes.letterOf`. -/
noncomputable def pcGen (n : ℕ) : PCDirectSum :=
  pcOf (codeOfNat n.unpair.1)
    (PresentedGroup.of (letterOf (codeOfNat n.unpair.1) n.unpair.2))

/-- Every generator of every coded group occurs in the family. -/
theorem pcOf_of_mem_range_pcGen (c : PresentationCode) (i : Fin (genCount c)) :
    pcOf c (PresentedGroup.of i) ∈ Set.range pcGen := by
  refine ⟨Nat.pair (Encodable.encode c) (i : ℕ), ?_⟩
  have hc : codeOfNat (Nat.pair (Encodable.encode c) (i : ℕ)).unpair.1 = c := by
    simp [Nat.unpair_pair, codeOfNat]
  have hk : (Nat.pair (Encodable.encode c) (i : ℕ)).unpair.2 = (i : ℕ) := by
    simp [Nat.unpair_pair]
  show pcOf (codeOfNat _) (PresentedGroup.of (letterOf (codeOfNat _) _)) =
    pcOf c (PresentedGroup.of i)
  rw [hc, hk]
  obtain ⟨m, l⟩ := c
  rw [letterOf_val m l i]

/-- Every coordinate inclusion lands in the subgroup generated by the family:
a coded group is generated by its own generators. -/
theorem pcOf_mem_closure_pcGen (c : PresentationCode) (a : Carrier c) :
    pcOf c a ∈ Subgroup.closure (Set.range pcGen) := by
  classical
  have ha : a ∈ Subgroup.closure
      (Set.range (PresentedGroup.of : Fin (genCount c) → Carrier c)) := by
    rw [PresentedGroup.closure_range_of]
    exact Subgroup.mem_top a
  induction ha using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Subgroup.subset_closure (pcOf_of_mem_range_pcGen c i)
  | one =>
      rw [map_one]
      exact Subgroup.one_mem _
  | mul y z _ _ ihy ihz =>
      rw [map_mul]
      exact Subgroup.mul_mem _ ihy ihz
  | inv y _ ihy =>
      rw [map_inv]
      exact Subgroup.inv_mem _ ihy

/-- **The `spans` field of (B1), for the Primcodable absorber.** -/
theorem spans_pcGen : Subgroup.closure (Set.range pcGen) = ⊤ := by
  classical
  rw [Subgroup.eq_top_iff']
  intro g
  suffices h : ∀ f : Π₀ c : PresentationCode, Additive (Carrier c),
      (Multiplicative.ofAdd f : PCDirectSum) ∈
        Subgroup.closure (Set.range pcGen) by
    exact h (Multiplicative.toAdd g)
  intro f
  refine DFinsupp.induction
    (p := fun f : Π₀ c : PresentationCode, Additive (Carrier c) ↦
      (Multiplicative.ofAdd f : PCDirectSum) ∈
        Subgroup.closure (Set.range pcGen)) f ?_ ?_
  · change (1 : PCDirectSum) ∈ Subgroup.closure (Set.range pcGen)
    exact Subgroup.one_mem _
  · intro c a f' _ _ ih
    have ha : (Multiplicative.ofAdd (DFinsupp.single c a) : PCDirectSum) =
        pcOf c (Additive.toMul a) := by
      apply Multiplicative.ofAdd.injective
      simp [pcOf]
    let tail : PCDirectSum := Multiplicative.ofAdd f'
    have htail : tail ∈ Subgroup.closure (Set.range pcGen) := ih
    have hm : pcOf c (Additive.toMul a) * tail ∈
        Subgroup.closure (Set.range pcGen) :=
      Subgroup.mul_mem _ (pcOf_mem_closure_pcGen c (Additive.toMul a)) htail
    simp only [tail] at hm
    rw [← ha] at hm
    exact hm

end Higman
end GroupApproximation
