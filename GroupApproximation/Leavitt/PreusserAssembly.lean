import GroupApproximation.Leavitt.CongruencePlumbing
import GroupApproximation.Leavitt.LeavittMarkNontrivial
import GroupApproximation.Leavitt.BinaryLeavittSimple
import GroupApproximation.Leavitt.ExchangeRefinement
import GroupApproximation.Leavitt.RowAnnihilatorTransvection
import GroupApproximation.Leavitt.PreusserSandwichStep

/-!
# Assembling Preusser's sandwich from its entry-level half

`GroupApproximation.Leavitt.CongruenceSubgroups` proves the manuscript's
Proposition `prop:simple` along the cited route, but with one explicit binder
left standing: `isSimpleGroup_of_preusser_sandwich` takes

```
hpreusser : ∀ (N : Subgroup (elementaryGroup ι R)), N.Normal →
  ∃ I : TwoSidedIdeal R, relativeElementary ι I ≤ N ∧
    N.map (elementaryGroup ι R).subtype ≤ congruenceSubgroup ι I
```

as an assumption.  This file shows exactly how that assumption is produced from
the entry-level statement of Preusser's Proposition 21 (Preusser, *On general
linear groups over exchange rings*, Linear and Multilinear Algebra **70**
(2022), no. 4, 705--713), and then instantiates the resulting simplicity
theorem for the binary Leavitt algebra.

## The chain

For a normal `N ≤ EL_ι(R)` the level ideal is the canonical one,
`I := normalLevel hcard N` -- the coefficients whose transvections already lie
in `N`.  With that choice:

* the **lower** inclusion `EL_ι(R, I) ≤ N` is `relativeElementary_normalLevel_le`
  and is already unconditional in the tree;
* the **upper** inclusion `N ≤ C_ι(R, I)` is what needs Proposition 21.  By
  `mem_normalLevel_iff`, saying that an entry `elMat g i j` lies in
  `normalLevel hcard N` is exactly saying that `e_{kl}(elMat g i j) ∈ N` for
  every `k ≠ l`, which is Proposition 21(i) with `a = b = 1`; likewise the
  diagonal-difference clause `a * elMat g i i - elMat g j j * a ∈ I` is
  Proposition 21(ii) with `a = b = 1`.  The entrywise description of
  `C_ι(R, I)` (Preusser's Remark 11) is
  `map_le_congruenceSubgroup_of_entries` in
  `GroupApproximation.Leavitt.CongruencePlumbing`, and it converts the two
  entry statements into the upper inclusion.

## Inputs discharged here

Both ingredients of Proposition 21 are proved in the tree.
`RowAnnihilator.elGen_mem_of_row_annihilator` is Preusser's exchange-free
Proposition 20 calculation.  `ExchangeRefinement` promotes the one-element
right-exchange property to the finite orthogonal refinement used in
Proposition 21.  The assembly below combines them and leaves no theorem
parameter at the binary-Leavitt endpoint.

## Relation to the repository's actual endpoint

The simplicity of `EL_ι(L_{𝔽₂}(1,2))` is also proved unconditionally in
`GroupApproximation.Leavitt.RootDetectionBinary`, by direct root extraction and
with no sandwich classification.  This file supplies the independent
normal-subgroup derivation cited by the manuscript.
-/

namespace GroupApproximation
namespace PreusserAssembly

open ElementarySimplicity

/-! ### The two conclusions of Preusser's Proposition 21

Both are stated in the "every position, every coefficient" form that
Proposition 21 actually delivers: the transvection is produced in *every* root
position `k ≠ l` and with an arbitrary two-sided coefficient sandwich `a · - · b`.
That is more than the assembly below consumes -- it only ever uses `a = b = 1`
-- but it is the form the source proves, and weakening it here would make the
interface to T4 a different statement from the one T4 is asked to prove. -/

/-- **Preusser, Proposition 21(i)**, quantified over normal subgroups of
`EL_ι(R)`: every matrix entry of every member of a normal subgroup is realized,
after an arbitrary two-sided coefficient sandwich, as the coefficient of a
transvection in that subgroup, in every root position. -/
def Prop21Entry (ι R : Type*) [Fintype ι] [DecidableEq ι] [Ring R] : Prop :=
  ∀ (N : Subgroup (elementaryGroup ι R)), N.Normal →
    ∀ (g : elementaryGroup ι R), g ∈ N →
      ∀ (i j : ι), i ≠ j → ∀ (k l : ι) (hkl : k ≠ l) (a b : R),
          elGen k l hkl (a * elMat g i j * b) ∈ N

/-- **Preusser, Proposition 21(ii)**, quantified over normal subgroups of
`EL_ι(R)`: the same for the two-index diagonal differences
`c * g i i - g j j * c`, which are the coefficients Remark 11 uses to describe
the congruence subgroup on the diagonal. -/
def Prop21DiagDiff (ι R : Type*) [Fintype ι] [DecidableEq ι] [Ring R] : Prop :=
  ∀ (N : Subgroup (elementaryGroup ι R)), N.Normal →
    ∀ (g : elementaryGroup ι R), g ∈ N →
      ∀ (i j : ι) (c : R) (k l : ι) (hkl : k ≠ l) (a b : R),
        elGen k l hkl (a * (c * elMat g i i - elMat g j j * c) * b) ∈ N

/-! ### From Proposition 21 to the canonical level ideal -/

section Level

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **Every entry lands in the canonical level.**  Membership in
`normalLevel hcard N` *is* the statement that the transvections with that
coefficient all lie in `N` (`mem_normalLevel_iff`), so this is Proposition
21(i) read with the trivial sandwich `a = b = 1`. -/
theorem elMat_mem_normalLevel (hcard : 3 ≤ Fintype.card ι)
    (hentry : Prop21Entry ι R)
    (N : Subgroup (elementaryGroup ι R)) [hN : N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N) (i j : ι) (hij : i ≠ j) :
    elMat g i j ∈ normalLevel hcard N := by
  refine (mem_normalLevel_iff hcard N).mpr ?_
  intro k l hkl
  have h := hentry N hN g hg i j hij k l hkl 1 1
  simpa only [one_mul, mul_one] using h

/-- **Every two-index diagonal difference lands in the canonical level**, by
the same reading of Proposition 21(ii). -/
theorem diagDiff_mem_normalLevel (hcard : 3 ≤ Fintype.card ι)
    (hdiag : Prop21DiagDiff ι R)
    (N : Subgroup (elementaryGroup ι R)) [hN : N.Normal]
    {g : elementaryGroup ι R} (hg : g ∈ N) (i j : ι) (c : R) :
    c * elMat g i i - elMat g j j * c ∈ normalLevel hcard N := by
  refine (mem_normalLevel_iff hcard N).mpr ?_
  intro k l hkl
  have h := hdiag N hN g hg i j c k l hkl 1 1
  simpa only [one_mul, mul_one] using h

/-- **The upper half of the sandwich, at the canonical level.**  The two
entrywise clauses supplied by Proposition 21 are exactly the hypotheses of the
entrywise description of `C_ι(R, I)` (Preusser's Remark 11, formalized as
`map_le_congruenceSubgroup_of_entries`).  Note that the off-diagonal clause is
obtained for *all* index pairs, not just the off-diagonal ones; the extra
information is simply discarded. -/
theorem map_le_congruenceSubgroup_normalLevel (hcard : 3 ≤ Fintype.card ι)
    (hentry : Prop21Entry ι R) (hdiag : Prop21DiagDiff ι R)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] :
    N.map (elementaryGroup ι R).subtype
      ≤ congruenceSubgroup ι (normalLevel hcard N) :=
  map_le_congruenceSubgroup_of_entries N (normalLevel hcard N)
    (fun _g hg i j hij ↦ elMat_mem_normalLevel hcard hentry N hg i j hij)
    (fun _g hg i j a ↦ diagDiff_mem_normalLevel hcard hdiag N hg i j a)

/-! ### Discharging Proposition 21 from the proved prerequisites -/

/-- Preusser's Proposition 20 in the packaged form consumed by the sandwich
step. -/
theorem rowAnnihilatorTransvection (hcard : 3 ≤ Fintype.card ι)
    (N : Subgroup (elementaryGroup ι R)) [N.Normal] :
    PreusserSandwich.RowAnnihilatorTransvection N := by
  intro g hg i j x y hxj hann k l hkl a b
  exact RowAnnihilator.elGen_mem_of_row_annihilator
    hcard N hg i j x y hxj hann hkl a b

/-- Preusser's Proposition 21(i), for every ring with the finite right-exchange
refinement. -/
theorem prop21Entry (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R) :
    Prop21Entry ι R := by
  exact PreusserSandwich.prop21Entry_of_prop20 hcard hex
    (fun N hN ↦ by
      letI := hN
      exact rowAnnihilatorTransvection hcard N)

/-- Preusser's Proposition 21(ii), under the same exchange hypothesis. -/
theorem prop21DiagDiff (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R) :
    Prop21DiagDiff ι R := by
  exact PreusserSandwich.prop21DiagDiff_of_prop20 hcard hex
    (fun N hN ↦ by
      letI := hN
      exact rowAnnihilatorTransvection hcard N)

end Level

/-! ### The sandwich, and the simplicity theorem it feeds -/

section Sandwich

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]

/-- **The forward direction of Preusser's Theorem 3, for `N ⊴ EL_ι(R)`.**

The witnessing ideal is the canonical level `normalLevel hcard N`, for which the
lower inclusion is unconditional (`relativeElementary_normalLevel_le`) and the
upper inclusion is the previous lemma.

Two respects in which this is weaker than Preusser's Theorem 3, neither of them
needed by `isSimpleGroup_of_preusser_sandwich`: the source classifies every
subgroup of `GL_ι(R)` *normalized by* `EL_ι(R)`, not merely the normal subgroups
of `EL_ι(R)`; and the source asserts the level ideal is unique, where this is a
bare existential.

The two Proposition 21 clauses are supplied above from the proved
row-annihilator and exchange-refinement theorems. -/
theorem preusser_sandwich (hcard : 3 ≤ Fintype.card ι)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (N : Subgroup (elementaryGroup ι R)) (hN : N.Normal) :
    ∃ I : TwoSidedIdeal R, relativeElementary ι I ≤ N ∧
      N.map (elementaryGroup ι R).subtype ≤ congruenceSubgroup ι I := by
  haveI := hN
  exact ⟨normalLevel hcard N, relativeElementary_normalLevel_le hcard N,
    map_le_congruenceSubgroup_normalLevel hcard
      (prop21Entry hcard hex) (prop21DiagDiff hcard hex) N⟩

/-- **`isSimpleGroup_of_preusser_sandwich` with its sandwich hypothesis
discharged from Proposition 21.**  Everything else that theorem asks for --
simplicity of the coefficient ring, triviality of the central units, and
nontriviality of `EL_ι(R)` -- is passed straight through.

The finite right-exchange refinement is the only additional algebraic input. -/
theorem isSimpleGroup_via_preusser (hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R]
    (hcentral : ∀ u : Rˣ, (∀ x : R, Commute (u : R) x) → (u : R) = 1)
    (hex : ExchangePrerequisite.HasFiniteRightExchangePartitions R)
    (hne : Nontrivial (elementaryGroup ι R)) :
    IsSimpleGroup (elementaryGroup ι R) :=
  isSimpleGroup_of_preusser_sandwich hcard hcentral
    (fun N hN ↦ preusser_sandwich hcard hex N hN) hne

end Sandwich

/-! ### Instantiation at the binary Leavitt algebra

The three side conditions of `isSimpleGroup_via_preusser` are all available in the
library for `R = L_{𝔽₂}(1,2)`:

* `IsSimpleRing R` from single-sandwich division
  (`HasSingleSandwichDivision.isSimpleRing`, applied to
  `BinaryLeavitt.hasSingleSandwichDivision`);
* triviality of the central units from `BinaryLeavitt.central_units_trivial`;
* nontriviality of `EL_ι(R)` from `LeavittMark.elGen_ne_one_of_ne_zero`, the
  same witness the direct route uses.

The finite exchange refinement is
`BinaryLeavitt.hasFiniteRightExchangePartitions`; Proposition 20 and both
clauses of Proposition 21 are discharged above. -/

section BinaryLeavitt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The unconditional Preusser route to Proposition `prop:simple`.** -/
theorem isSimpleGroup_elementaryGroup_binaryLeavitt_via_preusser
    (hcard : 3 ≤ Fintype.card ι) :
    IsSimpleGroup
      (elementaryGroup ι (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2))) := by
  haveI : IsSimpleRing (BinaryLeavitt.BinaryLeavittAlgebra (ZMod 2)) :=
    HasSingleSandwichDivision.isSimpleRing
      (BinaryLeavitt.hasSingleSandwichDivision (ZMod 2))
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  refine isSimpleGroup_via_preusser hcard ?_
    (BinaryLeavitt.hasFiniteRightExchangePartitions (ZMod 2))
    ⟨⟨elGen i j hij 1, 1,
      LeavittMark.elGen_ne_one_of_ne_zero i j hij one_ne_zero⟩⟩
  intro u hu
  have h : u = 1 :=
    BinaryLeavitt.central_units_trivial u fun y ↦ (hu y).eq
  exact congrArg Units.val h

end BinaryLeavitt

end PreusserAssembly
end GroupApproximation
