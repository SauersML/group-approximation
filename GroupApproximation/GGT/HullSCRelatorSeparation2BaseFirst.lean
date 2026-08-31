import GroupApproximation.GGT.HullSCRelatorSeparation2WindowExact

/-!
# Avoidance for windows beginning at the base letter

With an even alternating run, the final block has index `true` and the first
block has index `false`.  A cyclic same-index span which starts at the final
block and crosses the unique base letter is handled after peeling that final
block by an expression

`baseLetter * a_false^n * tail`.

The exponent `n` is the head of the exponent list.  Only finitely many powers
can put any one of the finitely many bounded tails in `H_true`, because the
power belongs to the distinct subgroup `H_false`.  This file packages that
finite obstruction and the resulting head clause.
-/

namespace GroupApproximation
namespace HullSC

universe u

section BaseFirst

variable {G : Type u} [Group G]

/-- The head-exponent clause needed for the exceptional cyclic seam.  It is
vacuous for the empty list and otherwise tests all bounded prefixes following
the first alternating block. -/
def BaseFirstAvoidance (D : GGT.RelGenSet G Bool) (a : Bool → G)
    (baseLetter : G) (W : ℕ) : List ℕ → Prop
  | [] => True
  | n :: post => ∀ r : ℕ, r ≤ W →
      baseLetter * a false ^ n *
          GGT.RelLetter.listVal
            (blockWord (a false) (a true) true (post.take r))
        ∉ D.fam true

/-- The powers forbidden for the first exponent by base-first cyclic windows. -/
def baseFirstBadPow (D : GGT.RelGenSet G Bool) (a : Bool → G)
    (ms : List ℕ) (W : ℕ) (baseLetter : G) : Set G :=
  (fun n : ℕ => a false ^ n) ''
    {n : ℕ | ∃ r : ℕ, r ≤ W ∧
      baseLetter * a false ^ n *
          GGT.RelLetter.listVal
            (blockWord (a false) (a true) true (ms.take r))
        ∈ D.fam true}

/-- The base-first obstruction set is finite. -/
theorem finite_baseFirstBadPow {D : GGT.RelGenSet G Bool}
    (hemb : D.IsHyperbolicallyEmbedded) {a : Bool → G}
    (hinj : ∀ s : Bool, Function.Injective (fun n : ℕ => a s ^ n))
    (hmem : ∀ s : Bool, a s ∈ D.fam s) (ms : List ℕ) (W : ℕ)
    (baseLetter : G) : (baseFirstBadPow D a ms W baseLetter).Finite := by
  refine Set.Finite.image _ ?_
  have hpow : ∀ n : ℕ, a false ^ n ∈ D.fam false :=
    fun n => pow_mem (hmem false) n
  have hsub :
      {n : ℕ | ∃ r : ℕ, r ≤ W ∧
        baseLetter * a false ^ n *
            GGT.RelLetter.listVal
              (blockWord (a false) (a true) true (ms.take r))
          ∈ D.fam true} ⊆
        ⋃ r ∈ Set.Iic W,
          {n : ℕ | baseLetter * a false ^ n *
              GGT.RelLetter.listVal
                (blockWord (a false) (a true) true (ms.take r))
            ∈ D.fam true} := by
    rintro n ⟨r, hr, hn⟩
    exact Set.mem_biUnion hr hn
  refine Set.Finite.subset ?_ hsub
  refine (Set.finite_Iic W).biUnion ?_
  intro r _hr
  exact finite_mul_pow_mul_mem_fam hemb (by simp) (hinj false) hpow

/-- Avoiding the obstruction set gives every bounded base-first window. -/
theorem baseFirstAvoidance_of_notMem
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {ms : List ℕ}
    {W m : ℕ} {baseLetter : G}
    (h : a false ^ m ∉ baseFirstBadPow D a ms W baseLetter) :
    ∀ r : ℕ, r ≤ W →
      baseLetter * a false ^ m *
          GGT.RelLetter.listVal
            (blockWord (a false) (a true) true (ms.take r))
        ∉ D.fam true := by
  intro r hr hc
  apply h
  exact ⟨m, ⟨r, hr, hc⟩, rfl⟩

/-- The obstruction-set formulation produces the packaged head clause. -/
theorem baseFirstAvoidance_cons_of_notMem
    {D : GGT.RelGenSet G Bool} {a : Bool → G} {ms : List ℕ}
    {W m : ℕ} {baseLetter : G}
    (h : a false ^ m ∉ baseFirstBadPow D a ms W baseLetter) :
    BaseFirstAvoidance D a baseLetter W (m :: ms) :=
  baseFirstAvoidance_of_notMem h

end BaseFirst

end HullSC
end GroupApproximation
