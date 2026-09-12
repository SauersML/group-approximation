import GroupApproximation.CharClass.OddPAcyclicTag
import GroupApproximation.CharClass.OddPAcyclicAlgebra

/-!
# The five slot relations of the telescoping contraction

Lane `lix-cupone`, block `OddPAcyclic*` (lix-steenrod's plan §3.4, route (A)).

On the full model `tupAllMod K X r` (all tuples, no degree constraint) a slot operator applies a
map of tagged simplices in one slot, with a sign read off the **input** prefix:

```text
slotOp F sgn j (t) = sgn (tupPre t j) · (slot j of t replaced by F (t j)).
```

`OddPTupleD.slotBd j` is `slotOp tagBd (-1)^·`.  This file adds `slotS j = slotOp tagS (-1)^·` and
`slotE j = slotOp tagE 1` and proves the five relations `OddPAcyclicAlgebra.sum_mul_contrOp_add`
consumes:

* `slotBd j * slotS j + slotS j * slotBd j = 1 - slotE j`;
* `slotBd l * slotS j + slotS j * slotBd l = 0` for `j ≠ l`;
* `slotBd l * slotE j = slotE j * slotBd l` for `j ≠ l`;
* `slotBd j * slotE j = 0`, `slotE j * slotBd j = 0`.

## The signs, and where they come from

On one slot both odd operators carry the same prefix sign, which squares away, and what is left is
the one-slot contraction of `OddPAcyclicTag`.  On two different slots `j < l` the operator on the
earlier slot moves the later prefix: `tagBd` drops it by one (`tupPre_update_of_lt`), `tagS` raises it
by one (`tupPre_update_of_lt_raise` below), and `tagE` leaves it alone on its support, which lives in
degree `0` like its input (`tupPre_update_of_fst_eq`).  The operator on the later slot never moves the
earlier prefix (`tupPre_update_of_le`).  So two odd operators pick up opposite signs in the two orders
and anticommute, and `slotE` commutes.  Model-tested at `r = 1, 2, 3` on the chains of the
2-simplex, including the negative control that an unsigned `slotS` breaks the second relation.
-/

namespace GroupApproximation.CharClass

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace OddPAcyclic

variable (K : Type) [Field K] (X : TopCat.{0})

/-! ## 1. Prefix bookkeeping -/

/-- A slot update that raises the degree by one raises every later prefix by one. -/
theorem tupPre_update_of_lt_raise {r : ℕ} (t : Fin r → TagSimp X) (j : Fin r) (τ : TagSimp X)
    (l : Fin r) (h : j < l) (hd : τ.1 = (t j).1 + 1) :
    tupPre (Function.update t j τ) l = tupPre t l + 1 := by
  have key := tupPre_update_of_lt (Function.update t j τ) j (t j) l h
    (by rw [Function.update_self, hd])
  rw [Function.update_idem, Function.update_eq_self] at key
  exact key.symm

/-- A slot update that keeps the degree keeps every prefix. -/
theorem tupPre_update_of_fst_eq {r : ℕ} (t : Fin r → TagSimp X) (j : Fin r) (τ : TagSimp X)
    (l : Fin r) (hd : τ.1 = (t j).1) : tupPre (Function.update t j τ) l = tupPre t l := by
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m = j
  · subst hm
    rw [Function.update_self, hd]
  · rw [Function.update_of_ne hm]

/-! ## 2. Generic slot operators -/

/-- Replace slot `j` of `t` by every tagged simplex of a chain, linearly. -/
def slotLift {r : ℕ} (t : TupAll X r) (j : Fin r) : (TagSimp X →₀ K) →ₗ[K] tupAllMod K X r :=
  Finsupp.linearCombination K (fun τ : TagSimp X => Finsupp.single (Function.update t j τ) (1 : K))

/-- A slot operator on one tuple: apply `F` in slot `j`, with the sign `sgn` of the input prefix. -/
def slotOpGen (F : TagSimp X → TagSimp X →₀ K) (sgn : ℕ → K) {r : ℕ} (j : Fin r)
    (t : TupAll X r) : tupAllMod K X r :=
  sgn (tupPre t j) • slotLift K X t j (F (t j))

/-- The slot operator on the full model. -/
def slotOp (F : TagSimp X → TagSimp X →₀ K) (sgn : ℕ → K) {r : ℕ} (j : Fin r) :
    Module.End K (tupAllMod K X r) :=
  Finsupp.linearCombination K (slotOpGen K X F sgn j)

/-- The slot contraction. -/
def slotS {r : ℕ} (j : Fin r) : Module.End K (tupAllMod K X r) :=
  slotOp K X (tagS K X) (fun m => (-1 : K) ^ m) j

/-- The slot projection. -/
def slotE {r : ℕ} (j : Fin r) : Module.End K (tupAllMod K X r) :=
  slotOp K X (tagE K X) (fun _ => (1 : K)) j

theorem slotBd_eq_slotOp {r : ℕ} (j : Fin r) :
    slotBd K X j = slotOp K X (tagBd K X) (fun m => (-1 : K) ^ m) j :=
  rfl

theorem slotOp_single (F : TagSimp X → TagSimp X →₀ K) (sgn : ℕ → K) {r : ℕ} (j : Fin r)
    (t : TupAll X r) :
    slotOp K X F sgn j (Finsupp.single t (1 : K)) = sgn (tupPre t j) • slotLift K X t j (F (t j)) := by
  rw [slotOp, Finsupp.linearCombination_single, one_smul, slotOpGen]

theorem slotLift_single_self {r : ℕ} (t : TupAll X r) (j : Fin r) :
    slotLift K X t j (Finsupp.single (t j) (1 : K)) = Finsupp.single t (1 : K) := by
  rw [slotLift, Finsupp.linearCombination_single, one_smul, Function.update_eq_self]

/-- **One slot, twice**: the prefix at `j` does not move when slot `j` is replaced. -/
theorem slotOp_slotLift_same (F : TagSimp X → TagSimp X →₀ K) (sgn : ℕ → K) {r : ℕ}
    (j : Fin r) (t : TupAll X r) (w : TagSimp X →₀ K) :
    slotOp K X F sgn j (slotLift K X t j w)
      = sgn (tupPre t j) • slotLift K X t j (Finsupp.linearCombination K F w) := by
  have hfun : ∀ τ : TagSimp X,
      slotOp K X F sgn j (Finsupp.single (Function.update t j τ) (1 : K))
        = sgn (tupPre t j) • slotLift K X t j (F τ) := by
    intro τ
    rw [slotOp_single, tupPre_update_of_le t j τ j le_rfl, Function.update_self]
    congr 1
    rw [slotLift, slotLift]
    simp only [Function.update_idem]
  calc slotOp K X F sgn j (slotLift K X t j w)
      = Finsupp.linearCombination K
          (fun τ : TagSimp X => slotOp K X F sgn j (Finsupp.single (Function.update t j τ) (1 : K)))
          w :=
        Finsupp.apply_linearCombination K (slotOp K X F sgn j) _ w
    _ = Finsupp.linearCombination K
          (fun τ : TagSimp X => sgn (tupPre t j) • slotLift K X t j (F τ)) w :=
        tupLC_congr_fun K hfun w
    _ = sgn (tupPre t j) •
          Finsupp.linearCombination K (fun τ : TagSimp X => slotLift K X t j (F τ)) w :=
        tupLC_smul_fun K _ _ w
    _ = sgn (tupPre t j) • slotLift K X t j (Finsupp.linearCombination K F w) :=
        (congrArg (fun z => sgn (tupPre t j) • z)
          (Finsupp.apply_linearCombination K (slotLift K X t j) F w)).symm

/-- **Two different slots**, on a basis element. -/
theorem slotOp_slotOp_single_of_ne (F G : TagSimp X → TagSimp X →₀ K) (sF sG : ℕ → K)
    {r : ℕ} {j l : Fin r} (hne : l ≠ j) (t : TupAll X r) :
    slotOp K X F sF l (slotOp K X G sG j (Finsupp.single t (1 : K)))
      = sG (tupPre t j) •
          Finsupp.linearCombination K (fun τ : TagSimp X =>
            sF (tupPre (Function.update t j τ) l) •
              Finsupp.linearCombination K (fun τ' : TagSimp X =>
                Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K))
                (F (t l)))
            (G (t j)) := by
  rw [slotOp_single, map_smul, slotLift, Finsupp.apply_linearCombination]
  congr 1
  refine tupLC_congr_fun K (fun τ => ?_) _
  show slotOp K X F sF l (Finsupp.single (Function.update t j τ) (1 : K)) = _
  rw [slotOp_single, Function.update_of_ne hne, slotLift]

/-! ## 3. Moving a sign past a slot operator on an earlier slot -/

/-- `tagS` on an earlier slot raises the later prefix by one on its whole support. -/
theorem tupLC_sign_of_lt_tagS {M : Type} [AddCommGroup M] [Module K M] {r : ℕ}
    (t : TupAll X r) {j l : Fin r} (hjl : j < l) (G : TagSimp X → M) :
    Finsupp.linearCombination K
        (fun τ : TagSimp X => ((-1 : K) ^ tupPre (Function.update t j τ) l) • G τ)
        (tagS K X (t j))
      = (-((-1 : K) ^ tupPre t l)) • Finsupp.linearCombination K G (tagS K X (t j)) := by
  have key : ∀ τ₀ : TagSimp X, t j = τ₀ →
      Finsupp.linearCombination K
          (fun τ : TagSimp X => ((-1 : K) ^ tupPre (Function.update t j τ) l) • G τ)
          (tagS K X τ₀)
        = (-((-1 : K) ^ tupPre t l)) • Finsupp.linearCombination K G (tagS K X τ₀) := by
    intro τ₀ h
    obtain ⟨n, σ⟩ := τ₀
    rw [tagS_eq, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain,
      ← tupLC_smul_fun]
    refine tupLC_congr_fun K (fun σ' => ?_) _
    have hd : (⟨n + 1, σ'⟩ : TagSimp X).1 = (t j).1 + 1 := by
      rw [h]
    have hp := tupPre_update_of_lt_raise X t j ⟨n + 1, σ'⟩ l hjl hd
    show ((-1 : K) ^ tupPre (Function.update t j ⟨n + 1, σ'⟩) l) • G ⟨n + 1, σ'⟩
      = (-((-1 : K) ^ tupPre t l)) • G ⟨n + 1, σ'⟩
    rw [hp, pow_succ, mul_neg_one]
  exact key (t j) rfl

/-- `tagE` on another slot moves no prefix on its support. -/
theorem tupLC_sign_tagE {M : Type} [AddCommGroup M] [Module K M] {r : ℕ}
    (t : TupAll X r) (j l : Fin r) (G : TagSimp X → M) :
    Finsupp.linearCombination K
        (fun τ : TagSimp X => ((-1 : K) ^ tupPre (Function.update t j τ) l) • G τ)
        (tagE K X (t j))
      = ((-1 : K) ^ tupPre t l) • Finsupp.linearCombination K G (tagE K X (t j)) := by
  have key : ∀ τ₀ : TagSimp X, t j = τ₀ →
      Finsupp.linearCombination K
          (fun τ : TagSimp X => ((-1 : K) ^ tupPre (Function.update t j τ) l) • G τ)
          (tagE K X τ₀)
        = ((-1 : K) ^ tupPre t l) • Finsupp.linearCombination K G (tagE K X τ₀) := by
    intro τ₀ h
    obtain ⟨n, σ⟩ := τ₀
    cases n with
    | zero =>
      rw [tagE_zero_eq, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain,
        ← tupLC_smul_fun]
      refine tupLC_congr_fun K (fun σ' => ?_) _
      have hd : (⟨0, σ'⟩ : TagSimp X).1 = (t j).1 := by
        rw [h]
      show ((-1 : K) ^ tupPre (Function.update t j ⟨0, σ'⟩) l) • G ⟨0, σ'⟩
        = ((-1 : K) ^ tupPre t l) • G ⟨0, σ'⟩
      rw [tupPre_update_of_fst_eq X t j ⟨0, σ'⟩ l hd]
    | succ n => rw [tagE_succ, map_zero, map_zero, smul_zero]
  exact key (t j) rfl

/-! ## 4. The five relations -/

theorem neg_one_pow_mul_self (p : ℕ) : ((-1 : K) ^ p) * ((-1 : K) ^ p) = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- **One slot: `∂ s + s ∂ = 1 - e`.** -/
theorem slotBd_mul_slotS_add
    (hK : ∀ k : ℕ, LinearMap.ker (((singFreeR K).obj X).d (k + 1) k).hom
      ≤ LinearMap.range (((singFreeR K).obj X).d (k + 2) (k + 1)).hom) {r : ℕ} (j : Fin r) :
    slotBd K X j * slotS K X j + slotS K X j * slotBd K X j = 1 - slotE K X j := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply,
    Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
  rw [slotBd_eq_slotOp, slotS, slotE, slotOp_single, slotOp_single, slotOp_single, map_smul,
    map_smul, slotOp_slotLift_same, slotOp_slotLift_same, smul_smul, smul_smul,
    neg_one_pow_mul_self]
  simp only [one_smul]
  rw [← map_add (slotLift K X t j)]
  change slotLift K X t j (bdLC K X (tagS K X (t j)) + sLC K X (tagBd K X (t j))) = _
  rw [bdLC_tagS_add_sLC_tagBd K X hK, map_sub, slotLift_single_self]

/-- **One slot: `∂ e = 0`.** -/
theorem slotBd_mul_slotE {r : ℕ} (j : Fin r) : slotBd K X j * slotE K X j = 0 := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.zero_apply]
  rw [slotBd_eq_slotOp, slotE, slotOp_single, map_smul, slotOp_slotLift_same]
  change (1 : K) • ((-1 : K) ^ tupPre t j) • slotLift K X t j (bdLC K X (tagE K X (t j))) = 0
  rw [bdLC_tagE, map_zero, smul_zero, smul_zero]

/-- **One slot: `e ∂ = 0`.** -/
theorem slotE_mul_slotBd {r : ℕ} (j : Fin r) : slotE K X j * slotBd K X j = 0 := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.zero_apply]
  rw [slotBd_eq_slotOp, slotE, slotOp_single, map_smul, slotOp_slotLift_same]
  change ((-1 : K) ^ tupPre t j) • (1 : K) • slotLift K X t j (eLC K X (tagBd K X (t j))) = 0
  rw [eLC_tagBd, map_zero, smul_zero, smul_zero]

/-- The double sums of two slot operators on different slots agree after swapping the order of
summation, because the two slot updates commute. -/
theorem tupLC_swap_update {r : ℕ} (t : TupAll X r) {j l : Fin r} (hjl : j ≠ l)
    (u v : TagSimp X →₀ K) :
    Finsupp.linearCombination K (fun τ : TagSimp X =>
        Finsupp.linearCombination K (fun τ' : TagSimp X =>
          Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K)) v) u
      = Finsupp.linearCombination K (fun τ' : TagSimp X =>
          Finsupp.linearCombination K (fun τ : TagSimp X =>
            Finsupp.single (Function.update (Function.update t l τ') j τ) (1 : K)) u) v := by
  rw [tupLC_comm K (fun τ τ' : TagSimp X =>
    Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K)) u v]
  have hU : ∀ τ τ' : TagSimp X, Function.update (Function.update t j τ) l τ'
      = Function.update (Function.update t l τ') j τ :=
    fun τ τ' => Function.update_comm hjl τ τ' t
  simp only [hU]

/-- **Different slots: `∂_l s_j + s_j ∂_l = 0`.** -/
theorem slotBd_mul_slotS_add_of_ne {r : ℕ} {j l : Fin r} (hjl : j ≠ l) :
    slotBd K X l * slotS K X j + slotS K X j * slotBd K X l = 0 := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply,
    Module.End.mul_apply, LinearMap.zero_apply]
  rw [slotBd_eq_slotOp, slotS, slotOp_slotOp_single_of_ne K X _ _ _ _ hjl.symm,
    slotOp_slotOp_single_of_ne K X _ _ _ _ hjl]
  rcases lt_or_gt_of_ne hjl with h | h
  · -- `j < l`: `s_j` raises the prefix at `l`; `∂_l` leaves the prefix at `j` alone
    have hB : ∀ τ : TagSimp X, tupPre (Function.update t l τ) j = tupPre t j :=
      fun τ => tupPre_update_of_le t l τ j h.le
    simp only [hB]
    rw [tupLC_sign_of_lt_tagS K X t h (fun τ => Finsupp.linearCombination K (fun τ' : TagSimp X =>
        Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K)) (tagBd K X (t l))),
      tupLC_smul_fun K ((-1 : K) ^ tupPre t j) (fun τ' => Finsupp.linearCombination K
        (fun τ : TagSimp X => Finsupp.single (Function.update (Function.update t l τ') j τ) (1 : K))
        (tagS K X (t j))) (tagBd K X (t l)),
      tupLC_swap_update K X t hjl (tagS K X (t j)) (tagBd K X (t l)), smul_smul, smul_smul,
      ← add_smul]
    have hs : (-1 : K) ^ tupPre t j * -((-1 : K) ^ tupPre t l)
        + (-1 : K) ^ tupPre t l * (-1 : K) ^ tupPre t j = 0 := by ring
    rw [hs, zero_smul]
  · -- `l < j`: `∂_l` drops the prefix at `j`; `s_j` leaves the prefix at `l` alone
    have hA : ∀ τ : TagSimp X, tupPre (Function.update t j τ) l = tupPre t l :=
      fun τ => tupPre_update_of_le t j τ l h.le
    simp only [hA]
    rw [tupLC_sign_of_lt K X t h (fun τ' => Finsupp.linearCombination K (fun τ : TagSimp X =>
        Finsupp.single (Function.update (Function.update t l τ') j τ) (1 : K)) (tagS K X (t j))),
      tupLC_smul_fun K ((-1 : K) ^ tupPre t l) (fun τ => Finsupp.linearCombination K
        (fun τ' : TagSimp X => Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K))
        (tagBd K X (t l))) (tagS K X (t j)),
      tupLC_swap_update K X t hjl (tagS K X (t j)) (tagBd K X (t l)), smul_smul, smul_smul,
      ← add_smul]
    have hs : (-1 : K) ^ tupPre t j * (-1 : K) ^ tupPre t l
        + (-1 : K) ^ tupPre t l * -((-1 : K) ^ tupPre t j) = 0 := by ring
    rw [hs, zero_smul]

/-- **Different slots: `∂_l e_j = e_j ∂_l`.** -/
theorem slotBd_mul_slotE_of_ne {r : ℕ} {j l : Fin r} (hjl : j ≠ l) :
    slotBd K X l * slotE K X j = slotE K X j * slotBd K X l := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply]
  rw [slotBd_eq_slotOp, slotE, slotOp_slotOp_single_of_ne K X _ _ _ _ hjl.symm,
    slotOp_slotOp_single_of_ne K X _ _ _ _ hjl]
  simp only [one_smul]
  rw [tupLC_sign_tagE K X t j l (fun τ => Finsupp.linearCombination K (fun τ' : TagSimp X =>
      Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K)) (tagBd K X (t l))),
    tupLC_swap_update K X t hjl (tagE K X (t j)) (tagBd K X (t l))]

/-- **The telescoping identity on the full model**: with `S = contrOp slotS slotE`,
`d S + S d = 1 - slotE 0 * ⋯ * slotE (r-1)`. -/
theorem tupDAll_mul_contrOp_add
    (hK : ∀ k : ℕ, LinearMap.ker (((singFreeR K).obj X).d (k + 1) k).hom
      ≤ LinearMap.range (((singFreeR K).obj X).d (k + 2) (k + 1)).hom) (r : ℕ) :
    tupDAll K X r * contrOp (fun j : Fin r => slotS K X j) (fun j => slotE K X j)
      + contrOp (fun j : Fin r => slotS K X j) (fun j => slotE K X j) * tupDAll K X r
      = 1 - eAll (fun j : Fin r => slotE K X j) :=
  sum_mul_contrOp_add (fun j : Fin r => slotBd K X j) (fun j => slotS K X j)
    (fun j => slotE K X j)
    (fun j => slotBd_mul_slotS_add K X hK j)
    (fun _ _ hjl => slotBd_mul_slotS_add_of_ne K X hjl)
    (fun _ _ hjl => slotBd_mul_slotE_of_ne K X hjl)
    (fun j => slotBd_mul_slotE K X j)
    (fun j => slotE_mul_slotBd K X j)

end OddPAcyclic

end

end GroupApproximation.CharClass
