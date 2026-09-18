import GroupApproximation.Steinberg.Functoriality
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.K2RefinementDescend
import GroupApproximation.Meta.AxiomGuard

/-!
# The Leavitt refinement commutes with padding, up to one index swap (lane sk-leavitt-25)

Let `R` carry a Leavitt family `L`, let `r : Fin n` and `n ≤ N`.  Write `D_n = refineHom L r`
(`St_n(R) → St_{n+1}(R)`, splitting `r` into `castSucc r` and `last n`) and
`D_N = refineHom L (castLE r)` (`St_N(R) → St_{N+1}(R)`, splitting `castLE r` into
`castSucc (castLE r)` and `last N`).  Padding along `Fin.castLE` is `SteinbergGroup.indexMap`.

On a generator `xᵢⱼ(a)` both composites

* `pad_{n+1 → N+1} ∘ D_n`, and
* `D_N ∘ pad_{n → N}`

write the same product of roots.  The only difference is the index of the new split coordinate:
`castLE (last n)` (value `n`) in the first, `last N` (value `N`) in the second.  Every other
index `i < n` has value `i` on both sides.  So with `σ = swap (last N) (castLE (last n))`,

  `pad_{n+1 → N+1} ∘ D_n = indexMap σ ∘ D_N ∘ pad_{n → N}`   (`usedRankFour_intertwine`).

No conjugation is needed: `σ` is applied as an index relabelling, which is a homomorphism.
Consequence (`usedRankFour_pad_refine_eq_one`): if `w` dies in `St_N(R)`, then `D_n w` dies in
`St_{N+1}(R)`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2

open GroupApproximation.SteinbergGroup

/-- The index swap `last N ↔ castLE (last n)` of `Fin (N + 1)`. -/
def usedRankFourSwap {n N : ℕ} (h : n ≤ N) : Fin (N + 1) ≃ Fin (N + 1) :=
  Equiv.swap (Fin.last N) (Fin.castLE (Nat.add_le_add_right h 1) (Fin.last n))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.usedRankFourSwap

/-- The swap fixes the old indices: `σ (castSucc (castLE i)) = castLE (castSucc i)`. -/
theorem usedRankFourSwap_castSucc {n N : ℕ} (h : n ≤ N) (i : Fin n) :
    (usedRankFourSwap h).toEmbedding (Fin.castSucc (Fin.castLEEmb h i)) =
      Fin.castLEEmb (Nat.add_le_add_right h 1) (Fin.castSucc i) := by
  have h1 : Fin.castSucc (Fin.castLEEmb h i) ≠ Fin.last N := Fin.castSucc_ne_last _
  have h2 : Fin.castSucc (Fin.castLEEmb h i) ≠
      Fin.castLE (Nat.add_le_add_right h 1) (Fin.last n) := by
    intro e
    have e' : i.val = n := congrArg Fin.val e
    exact absurd e' (Nat.ne_of_lt i.isLt)
  show Equiv.swap (Fin.last N) (Fin.castLE (Nat.add_le_add_right h 1) (Fin.last n))
      (Fin.castSucc (Fin.castLEEmb h i)) =
    Fin.castLEEmb (Nat.add_le_add_right h 1) (Fin.castSucc i)
  exact (Equiv.swap_apply_of_ne_of_ne h1 h2).trans (Fin.ext rfl)

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.usedRankFourSwap_castSucc

/-- The swap sends the new split index `last N` to the padded split index `castLE (last n)`. -/
theorem usedRankFourSwap_last {n N : ℕ} (h : n ≤ N) :
    (usedRankFourSwap h).toEmbedding (Fin.last N) =
      Fin.castLEEmb (Nat.add_le_add_right h 1) (Fin.last n) :=
  Equiv.swap_apply_left (Fin.last N) (Fin.castLE (Nat.add_le_add_right h 1) (Fin.last n))

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.usedRankFourSwap_last

/-- Equal indices give equal Steinberg generators, whatever the off-diagonal proofs. -/
theorem usedRankFour_x_congr {I R : Type*} [Fintype I] [DecidableEq I] [Ring R]
    {p q p' q' : I} {hpq : p ≠ q} {hpq' : p' ≠ q'} {a : R} (hp : p = p') (hq : q = q') :
    x p q hpq a = x p' q' hpq' a := by
  subst hp
  subst hq
  rfl

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.usedRankFour_x_congr

variable {R : Type*} [Ring R] (L : LeavittFamily R)

/-- **The intertwining identity.**  Padding after refining equals refining after padding, followed
by the index swap `σ = swap (last N) (castLE (last n))`. -/
theorem usedRankFour_intertwine {n N : ℕ} (r : Fin n) (h : n ≤ N) :
    (SteinbergGroup.indexMap (R := R) (Fin.castLEEmb (Nat.add_le_add_right h 1))).comp
        (LeavittFP.refineHom L r) =
      (SteinbergGroup.indexMap (R := R) (usedRankFourSwap h).toEmbedding).comp
        ((LeavittFP.refineHom L (Fin.castLE h r)).comp
          (SteinbergGroup.indexMap (R := R) (Fin.castLEEmb h))) := by
  apply PresentedGroup.ext
  rintro ⟨i, j, hij, a⟩
  change SteinbergGroup.indexMap (Fin.castLEEmb (Nat.add_le_add_right h 1))
      (LeavittFP.refineHom L r (x i j hij a)) =
    SteinbergGroup.indexMap (usedRankFourSwap h).toEmbedding
      (LeavittFP.refineHom L (Fin.castLE h r)
        (SteinbergGroup.indexMap (Fin.castLEEmb h) (x i j hij a)))
  rw [SteinbergGroup.indexMap_x, LeavittFP.refineHom_x, LeavittFP.refineHom_x]
  by_cases hi : i = r
  · have hi' : Fin.castLEEmb h i = Fin.castLE h r := by
      subst hi
      rfl
    rw [LeavittFP.refineRoot_of_row L r hij a hi,
      LeavittFP.refineRoot_of_row L (Fin.castLE h r) _ a hi']
    simp only [map_mul, SteinbergGroup.indexMap_x]
    refine congrArg₂ (· * ·) ?_ ?_
    · exact usedRankFour_x_congr (usedRankFourSwap_castSucc h i).symm
        (usedRankFourSwap_castSucc h j).symm
    · exact usedRankFour_x_congr (usedRankFourSwap_last h).symm
        (usedRankFourSwap_castSucc h j).symm
  · have hi' : ¬ Fin.castLEEmb h i = Fin.castLE h r := fun e =>
      hi (Fin.ext (congrArg Fin.val e))
    by_cases hj : j = r
    · have hj' : Fin.castLEEmb h j = Fin.castLE h r := by
        subst hj
        rfl
      rw [LeavittFP.refineRoot_of_col L r hij a hi hj,
        LeavittFP.refineRoot_of_col L (Fin.castLE h r) _ a hi' hj']
      simp only [map_mul, SteinbergGroup.indexMap_x]
      refine congrArg₂ (· * ·) ?_ ?_
      · exact usedRankFour_x_congr (usedRankFourSwap_castSucc h i).symm
          (usedRankFourSwap_castSucc h j).symm
      · exact usedRankFour_x_congr (usedRankFourSwap_castSucc h i).symm
          (usedRankFourSwap_last h).symm
    · have hj' : ¬ Fin.castLEEmb h j = Fin.castLE h r := fun e =>
        hj (Fin.ext (congrArg Fin.val e))
      rw [LeavittFP.refineRoot_of_plain L r hij a hi hj,
        LeavittFP.refineRoot_of_plain L (Fin.castLE h r) _ a hi' hj']
      simp only [SteinbergGroup.indexMap_x]
      exact usedRankFour_x_congr (usedRankFourSwap_castSucc h i).symm
        (usedRankFourSwap_castSucc h j).symm

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.usedRankFour_intertwine

/-- **Stable death transfers along the refinement.**  If `w ∈ St_n(R)` dies in `St_N(R)`, then
`refineHom L r w ∈ St_{n+1}(R)` dies in `St_{N+1}(R)`. -/
theorem usedRankFour_pad_refine_eq_one {n N : ℕ} (r : Fin n) (h : n ≤ N)
    {w : SteinbergGroup (Fin n) R}
    (hw : SteinbergGroup.indexMap (Fin.castLEEmb h) w = 1) :
    SteinbergGroup.indexMap (Fin.castLEEmb (Nat.add_le_add_right h 1))
      (LeavittFP.refineHom L r w) = 1 := by
  have e : SteinbergGroup.indexMap (Fin.castLEEmb (Nat.add_le_add_right h 1))
        (LeavittFP.refineHom L r w) =
      SteinbergGroup.indexMap (usedRankFourSwap h).toEmbedding
        (LeavittFP.refineHom L (Fin.castLE h r)
          (SteinbergGroup.indexMap (Fin.castLEEmb h) w)) :=
    DFunLike.congr_fun (usedRankFour_intertwine L r h) w
  rw [e, hw, map_one, map_one]

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.usedRankFour_pad_refine_eq_one

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2
