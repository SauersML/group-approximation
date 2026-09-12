import GroupApproximation.CharClass.OddPTupleSign

/-!
# `d ∘ d = 0` for the flat `r`-fold tensor power of the singular chains

`OddPTuple.lean` defines the carrier `tupMod K X r k` and the differential `tupD`, and
`OddPTupleSign.lean` proves how the Koszul prefix moves.  This file proves the square-zero law.

## The route

The degree-`k` carrier is totalised: `tupUpdate` returns `0` off the target degree, so a double
sum over two slots carries an `if` at every term.  Rather than fight those, we pass to the **full
model** `tupAllMod K X r`, the free module on *all* tuples with no degree constraint, where the
differential is the plain sum of slot operators

    tupDAll = ∑ j, slotBd j,    slotBd j (t) = (-1)^{pre t j} · (slot j of t replaced by ∂(t j)),

and the degree-`k` carrier embeds by `tupIncl` (injective), intertwining `tupD` with `tupDAll`.
On the full model the law is three facts:

* `slotBd j * slotBd j = 0`: the prefix at slot `j` does not move when slot `j` is differentiated,
  so the signs square away and what is left is `∂ ∘ ∂ = 0` in one slot (`tupLC_tagBd_tagBd`,
  from `HomologicalComplex.d_comp_d`, no simplicial identity needed);
* `slotBd l * slotBd j + slotBd j * slotBd l = 0` for `j < l`: the two orders give the same basis
  elements (`Function.update_comm`) with opposite signs, because differentiating `j` first drops
  the prefix at `l` by one (`tupPre_update_of_lt`) while differentiating `l` first leaves the
  prefix at `j` alone (`tupPre_update_of_le`);
* a ring identity: a sum of square-zero, pairwise anticommuting elements squares to zero
  (`sum_mul_self_eq_zero_of_anticomm`, by induction on the number of summands, no division by 2).

This supersedes `OddPTupleSlot.lean` and `OddPTupleBd.lean` (parked, red, imported by nothing):
the one-slot square-zero law they were built for is `tupLC_tagBd_tagBd` here.

## Two spelling rules this file follows

* The slot boundary on a tagged simplex is restated as `tagBd_succ_eq`, a `Finsupp.mapDomain` of
  `chainBd`, with every argument typed at the bare `Finsupp`.  The original `tagBd_succ` feeds a
  `ModuleCat` carrier-typed term to `tagAt`, and `rw` meets that argument at `instances`
  transparency, where the carrier and the `Finsupp` are different types.
* A degree that a slot boundary lowers is never read off the support of a chain.  Every sum over
  `tagBd (t j)` is first rewritten along `Finsupp.linearCombination_mapDomain`, so the summand is a
  function of `σ'` with the tag `⟨n, σ'⟩` spelled on the nose, and the degree drop is `rfl`-visible.
-/

namespace GroupApproximation.CharClass

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree
open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree.AlexanderWhitney

noncomputable section

/-! ## 0. A ring identity -/

/-- **A sum of square-zero, pairwise anticommuting elements squares to zero.**  By induction on the
number of summands: `(a₀ + S)² = a₀² + (a₀ S + S a₀) + S²`, and the middle term is a sum of
anticommutators.  No division by two, so it holds over every ring. -/
theorem sum_mul_self_eq_zero_of_anticomm {R : Type*} [Ring R] :
    ∀ {r : ℕ} (a : Fin r → R), (∀ j, a j * a j = 0) →
      (∀ j l, j < l → a l * a j + a j * a l = 0) → (∑ j, a j) * (∑ j, a j) = 0
  | 0, _, _, _ => by simp
  | r + 1, a, hsq, hanti => by
    rw [Fin.sum_univ_succ, add_mul, mul_add, mul_add, hsq 0,
      sum_mul_self_eq_zero_of_anticomm (fun i : Fin r => a i.succ) (fun i => hsq i.succ)
        (fun i l h => hanti i.succ l.succ (Fin.succ_lt_succ_iff.mpr h)),
      zero_add, add_zero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by
      rw [add_comm]
      exact hanti 0 i.succ (Fin.succ_pos i)

/-! ## 1. Three facts about `Finsupp.linearCombination` -/

section LinearCombination

variable (K : Type) [CommRing K]

/-- A scalar on every value comes out of the linear combination. -/
theorem tupLC_smul_fun {α M : Type} [AddCommGroup M] [Module K M] (k : K) (v : α → M)
    (z : α →₀ K) :
    Finsupp.linearCombination K (fun a => k • v a) z = k • Finsupp.linearCombination K v z := by
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero, smul_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
  | single a c =>
    simp only [Finsupp.linearCombination_single]
    exact smul_comm c k (v a)

/-- Pointwise equal families give equal linear combinations. -/
theorem tupLC_congr_fun {α M : Type} [AddCommGroup M] [Module K M] {v w : α → M}
    (h : ∀ a, v a = w a) (z : α →₀ K) :
    Finsupp.linearCombination K v z = Finsupp.linearCombination K w z := by
  rw [funext h]

/-- **Fubini for linear combinations.** -/
theorem tupLC_comm {α β M : Type} [AddCommGroup M] [Module K M] (g : α → β → M)
    (x : α →₀ K) (y : β →₀ K) :
    Finsupp.linearCombination K (fun a => Finsupp.linearCombination K (fun b => g a b) y) x
      = Finsupp.linearCombination K
          (fun b => Finsupp.linearCombination K (fun a => g a b) x) y := by
  induction x using Finsupp.induction_linear with
  | zero => simp [Finsupp.linearCombination_apply]
  | add x1 x2 h1 h2 =>
    rw [map_add, h1, h2, ← LinearMap.add_apply, ← linearCombinationR_add_fun]
    refine tupLC_congr_fun K (fun b => ?_) y
    exact (map_add _ x1 x2).symm
  | single a c =>
    simp only [Finsupp.linearCombination_single]
    exact (tupLC_smul_fun K c (fun b => g a b) y).symm

end LinearCombination

/-! ## 2. The slot boundary, restated over bare `Finsupp`s, and `∂ ∘ ∂ = 0` in one slot -/

section Slot

variable (K : Type) [CommRing K] (X : TopCat.{0})

/-- The signed singular boundary `C_{n+1}(X; K) → C_n(X; K)`, typed at the bare `Finsupp`s. -/
def chainBd (n : ℕ) : (singularSimplices X (n + 1) →₀ K) →ₗ[K] (singularSimplices X n →₀ K) :=
  (((singFreeR K).obj X).d (n + 1) n).hom

/-- `∂ ∘ ∂ = 0`, free from `HomologicalComplex.d_comp_d`.  The degree is spelled `n + 1 + 1`
throughout, never `n + 2`: the number sits inside the type of a `ModuleCat` object. -/
theorem chainBd_chainBd (n : ℕ) (y : singularSimplices X (n + 1 + 1) →₀ K) :
    chainBd K X n (chainBd K X (n + 1) y) = 0 := by
  have hdd : ∀ y' : (((singFreeR K).obj X).X (n + 1 + 1)),
      (((singFreeR K).obj X).d (n + 1) n).hom
        ((((singFreeR K).obj X).d (n + 1 + 1) (n + 1)).hom y') = 0 := by
    intro y'
    have h' := congrArg (fun (g : (((singFreeR K).obj X).X (n + 1 + 1))
        ⟶ (((singFreeR K).obj X).X n)) => g.hom y')
      (HomologicalComplex.d_comp_d ((singFreeR K).obj X) (n + 1 + 1) (n + 1) n)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at h'
    exact h'
  exact hdd y

/-- The boundary of a tagged simplex of positive degree, as a `mapDomain` of `chainBd`, with every
argument typed at the bare `Finsupp`.  Definitional; use it in place of `tagBd_succ` wherever
`rw` has to look inside the result. -/
theorem tagBd_succ_eq (n : ℕ) (σ : singularSimplices X (n + 1)) :
    tagBd K X ⟨n + 1, σ⟩
      = Finsupp.mapDomain (fun σ' : singularSimplices X n => (⟨n, σ'⟩ : TagSimp X))
          (chainBd K X n (Finsupp.single σ (1 : K))) :=
  rfl

/-- **`∂ ∘ ∂ = 0` in one slot**: differentiating every simplex of the boundary of a tagged simplex,
and summing, gives zero. -/
theorem tupLC_tagBd_tagBd (τ : TagSimp X) :
    Finsupp.linearCombination K (tagBd K X) (tagBd K X τ) = 0 := by
  obtain ⟨n, σ⟩ := τ
  cases n with
  | zero => rw [tagBd_zero, map_zero]
  | succ n =>
    rw [tagBd_succ_eq, Finsupp.linearCombination_mapDomain]
    cases n with
    | zero => exact linearCombinationR_zero_fun _
    | succ n =>
      refine (linearCombinationR_comp_single ((tagAt K X n).comp (chainBd K X n)) _).trans ?_
      rw [LinearMap.comp_apply, chainBd_chainBd, map_zero]

end Slot

/-! ## 3. The full model and its slot operators -/

/-- All `r`-tuples of tagged simplices, with no constraint on the total degree. -/
abbrev TupAll (X : TopCat.{0}) (r : ℕ) : Type := Fin r → TagSimp X

/-- The free `K`-module on all tuples: every graded piece at once. -/
abbrev tupAllMod (K : Type) [CommRing K] (X : TopCat.{0}) (r : ℕ) : Type := TupAll X r →₀ K

/-- Differentiate slot `j` of one tuple, with the Koszul sign of that slot. -/
def slotBdGen (K : Type) [CommRing K] (X : TopCat.{0}) {r : ℕ} (j : Fin r) (t : TupAll X r) :
    tupAllMod K X r :=
  ((-1 : K) ^ tupPre t j) •
    Finsupp.linearCombination K
      (fun τ : TagSimp X => Finsupp.single (Function.update t j τ) (1 : K)) (tagBd K X (t j))

/-- The slot-`j` boundary on the full model. -/
def slotBd (K : Type) [CommRing K] (X : TopCat.{0}) {r : ℕ} (j : Fin r) :
    Module.End K (tupAllMod K X r) :=
  Finsupp.linearCombination K (slotBdGen K X j)

/-- The differential of the full model: the sum of the slot boundaries. -/
def tupDAll (K : Type) [CommRing K] (X : TopCat.{0}) (r : ℕ) : Module.End K (tupAllMod K X r) :=
  ∑ j : Fin r, slotBd K X j

/-- The degree-`k` carrier inside the full model. -/
def tupIncl (K : Type) [CommRing K] (X : TopCat.{0}) (r k : ℕ) :
    tupMod K X r k →ₗ[K] tupAllMod K X r :=
  Finsupp.lmapDomain K K Subtype.val

section FullModel

variable (K : Type) [CommRing K] (X : TopCat.{0}) {r : ℕ}

theorem slotBd_single (j : Fin r) (t : TupAll X r) :
    slotBd K X j (Finsupp.single t (1 : K)) = slotBdGen K X j t := by
  rw [slotBd, Finsupp.linearCombination_single, one_smul]

/-- **The sign, where the degree drop is used.**  With `j < l`, the prefix at `l` of a tuple whose
slot `j` has been replaced by a face of `t j` is one less than at `t`, so its sign is the negative. -/
theorem tupLC_sign_of_lt {M : Type} [AddCommGroup M] [Module K M] (t : TupAll X r)
    {j l : Fin r} (hjl : j < l) (G : TagSimp X → M) :
    Finsupp.linearCombination K
        (fun τ : TagSimp X => ((-1 : K) ^ tupPre (Function.update t j τ) l) • G τ)
        (tagBd K X (t j))
      = (-((-1 : K) ^ tupPre t l)) • Finsupp.linearCombination K G (tagBd K X (t j)) := by
  have key : ∀ τ₀ : TagSimp X, t j = τ₀ →
      Finsupp.linearCombination K
          (fun τ : TagSimp X => ((-1 : K) ^ tupPre (Function.update t j τ) l) • G τ)
          (tagBd K X τ₀)
        = (-((-1 : K) ^ tupPre t l)) • Finsupp.linearCombination K G (tagBd K X τ₀) := by
    intro τ₀ h
    obtain ⟨n, σ⟩ := τ₀
    cases n with
    | zero => simp only [tagBd_zero, map_zero, smul_zero]
    | succ n =>
      rw [tagBd_succ_eq, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain,
        ← tupLC_smul_fun]
      refine tupLC_congr_fun K (fun σ' => ?_) _
      have hd : (⟨n, σ'⟩ : TagSimp X).1 + 1 = (t j).1 := congrArg Sigma.fst h.symm
      have hp := tupPre_update_of_lt t j ⟨n, σ'⟩ l hjl hd
      have hs : ((-1 : K) ^ tupPre (Function.update t j ⟨n, σ'⟩) l)
          = -((-1 : K) ^ tupPre t l) := by
        rw [← hp, pow_succ]
        ring
      show ((-1 : K) ^ tupPre (Function.update t j ⟨n, σ'⟩) l) • G ⟨n, σ'⟩
        = (-((-1 : K) ^ tupPre t l)) • G ⟨n, σ'⟩
      rw [hs]
  exact key (t j) rfl

/-- Two different slots, differentiated one after the other, on a basis element. -/
theorem slotBd_slotBd_single_of_ne {j l : Fin r} (hne : l ≠ j) (t : TupAll X r) :
    slotBd K X l (slotBd K X j (Finsupp.single t (1 : K)))
      = ((-1 : K) ^ tupPre t j) •
          Finsupp.linearCombination K (fun τ : TagSimp X =>
            ((-1 : K) ^ tupPre (Function.update t j τ) l) •
              Finsupp.linearCombination K (fun τ' : TagSimp X =>
                Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K))
                (tagBd K X (t l)))
            (tagBd K X (t j)) := by
  rw [slotBd_single, slotBdGen, map_smul, Finsupp.apply_linearCombination]
  congr 1
  refine tupLC_congr_fun K (fun τ => ?_) _
  show slotBd K X l (Finsupp.single (Function.update t j τ) (1 : K)) = _
  rw [slotBd_single, slotBdGen, Function.update_of_ne hne]

/-- **Distinct slots anticommute**, on a basis element. -/
theorem slotBd_anticomm_single_of_lt {j l : Fin r} (hjl : j < l) (t : TupAll X r) :
    slotBd K X l (slotBd K X j (Finsupp.single t (1 : K)))
      + slotBd K X j (slotBd K X l (Finsupp.single t (1 : K))) = 0 := by
  rw [slotBd_slotBd_single_of_ne K X hjl.ne' t, slotBd_slotBd_single_of_ne K X hjl.ne t]
  -- differentiating the later slot leaves the prefix at the earlier one alone
  have hB : ∀ τ : TagSimp X, tupPre (Function.update t l τ) j = tupPre t j :=
    fun τ => tupPre_update_of_le t l τ j hjl.le
  simp only [hB]
  rw [tupLC_sign_of_lt K X t hjl (fun τ => Finsupp.linearCombination K (fun τ' : TagSimp X =>
      Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K)) (tagBd K X (t l))),
    tupLC_smul_fun K ((-1 : K) ^ tupPre t j) (fun τ => Finsupp.linearCombination K
      (fun τ' : TagSimp X => Finsupp.single (Function.update (Function.update t l τ) j τ') (1 : K))
      (tagBd K X (t j))) (tagBd K X (t l)),
    tupLC_comm K (fun τ τ' : TagSimp X =>
      Finsupp.single (Function.update (Function.update t j τ) l τ') (1 : K))
      (tagBd K X (t j)) (tagBd K X (t l))]
  have hU : ∀ τ τ' : TagSimp X, Function.update (Function.update t j τ) l τ'
      = Function.update (Function.update t l τ') j τ :=
    fun τ τ' => Function.update_comm hjl.ne τ τ' t
  simp only [hU, smul_smul]
  rw [← add_smul]
  have hs : (-1 : K) ^ tupPre t j * -((-1 : K) ^ tupPre t l)
      + (-1 : K) ^ tupPre t l * (-1 : K) ^ tupPre t j = 0 := by ring
  rw [hs, zero_smul]

/-- **A slot boundary squares to zero**, on a basis element. -/
theorem slotBd_mul_self_single (j : Fin r) (t : TupAll X r) :
    slotBd K X j (slotBd K X j (Finsupp.single t (1 : K))) = 0 := by
  rw [slotBd_single, slotBdGen, map_smul, Finsupp.apply_linearCombination]
  have hfun : ∀ τ : TagSimp X,
      (⇑(slotBd K X j) ∘ fun τ : TagSimp X => Finsupp.single (Function.update t j τ) (1 : K)) τ
        = ((-1 : K) ^ tupPre t j) •
            Finsupp.linearCombination K
              (fun τ' : TagSimp X => Finsupp.single (Function.update t j τ') (1 : K))
              (tagBd K X τ) := by
    intro τ
    show slotBd K X j (Finsupp.single (Function.update t j τ) (1 : K)) = _
    rw [slotBd_single, slotBdGen, tupPre_update_of_le t j τ j le_rfl, Function.update_self]
    simp only [Function.update_idem]
  rw [tupLC_congr_fun K hfun, tupLC_smul_fun]
  have h0 := Finsupp.apply_linearCombination K
    (Finsupp.linearCombination K
      (fun τ' : TagSimp X => Finsupp.single (Function.update t j τ') (1 : K)))
    (tagBd K X) (tagBd K X (t j))
  rw [tupLC_tagBd_tagBd, map_zero] at h0
  have h1 : Finsupp.linearCombination K (fun τ : TagSimp X => Finsupp.linearCombination K
      (fun τ' : TagSimp X => Finsupp.single (Function.update t j τ') (1 : K)) (tagBd K X τ))
      (tagBd K X (t j)) = 0 := h0.symm
  rw [h1, smul_zero, smul_zero]

theorem slotBd_mul_self (j : Fin r) : slotBd K X j * slotBd K X j = 0 := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply,
    LinearMap.zero_apply]
  exact slotBd_mul_self_single K X j t

theorem slotBd_anticomm {j l : Fin r} (hjl : j < l) :
    slotBd K X l * slotBd K X j + slotBd K X j * slotBd K X l = 0 := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.add_apply,
    Module.End.mul_apply, LinearMap.zero_apply]
  exact slotBd_anticomm_single_of_lt K X hjl t

/-- **`d ∘ d = 0` on the full model.** -/
theorem tupDAll_mul_self : tupDAll K X r * tupDAll K X r = 0 :=
  sum_mul_self_eq_zero_of_anticomm (fun j : Fin r => slotBd K X j)
    (fun j => slotBd_mul_self K X j) (fun _ _ h => slotBd_anticomm K X h)

/-! ## 4. Back to the degree-`k` carrier -/

theorem tupIncl_injective (k : ℕ) : Function.Injective (tupIncl K X r k) :=
  Finsupp.mapDomain_injective Subtype.val_injective

theorem tupIncl_single (k : ℕ) (t : TupIdx X r k) :
    tupIncl K X r k (Finsupp.single t (1 : K)) = Finsupp.single t.1 (1 : K) := by
  rw [tupIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- A totalised slot update that lands in the target degree is the basis element. -/
theorem tupIncl_tupUpdate_of_eq {k : ℕ} (t : TupAll X r) (j : Fin r) (τ : TagSimp X)
    (h : ∑ l, (Function.update t j τ l).1 = k) :
    tupIncl K X r k (tupUpdate K k t j τ) = Finsupp.single (Function.update t j τ) (1 : K) := by
  rw [tupUpdate, dif_pos h]
  exact tupIncl_single K X k ⟨Function.update t j τ, h⟩

/-- Replacing slot `j` of a degree-`(k+1)` tuple by a face of `t j` always lands in degree `k`, so
the totalised update is the plain basis element on the whole support. -/
theorem tupLC_tupIncl_tupUpdate {k : ℕ} (t : TupIdx X r (k + 1)) (j : Fin r) :
    Finsupp.linearCombination K (fun τ : TagSimp X => tupIncl K X r k (tupUpdate K k t.1 j τ))
        (tagBd K X (t.1 j))
      = Finsupp.linearCombination K
          (fun τ : TagSimp X => Finsupp.single (Function.update t.1 j τ) (1 : K))
          (tagBd K X (t.1 j)) := by
  have key : ∀ τ₀ : TagSimp X, t.1 j = τ₀ →
      Finsupp.linearCombination K
          (fun τ : TagSimp X => tupIncl K X r k (tupUpdate K k t.1 j τ)) (tagBd K X τ₀)
        = Finsupp.linearCombination K
            (fun τ : TagSimp X => Finsupp.single (Function.update t.1 j τ) (1 : K))
            (tagBd K X τ₀) := by
    intro τ₀ h
    obtain ⟨n, σ⟩ := τ₀
    cases n with
    | zero => simp only [tagBd_zero, map_zero]
    | succ n =>
      rw [tagBd_succ_eq, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_mapDomain]
      refine tupLC_congr_fun K (fun σ' => ?_) _
      show tupIncl K X r k (tupUpdate K k t.1 j ⟨n, σ'⟩)
        = Finsupp.single (Function.update t.1 j (⟨n, σ'⟩ : TagSimp X)) (1 : K)
      have hj1 : (t.1 j).1 = n + 1 := congrArg Sigma.fst h
      have hdeg : ∑ l, (Function.update t.1 j (⟨n, σ'⟩ : TagSimp X) l).1 = k := by
        have hj : j ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ j
        have hrest : ∀ m ∈ (Finset.univ : Finset (Fin r)).erase j,
            (Function.update t.1 j (⟨n, σ'⟩ : TagSimp X) m).1 = (t.1 m).1 := by
          intro m hm
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
        have e1 : ∑ l, (Function.update t.1 j (⟨n, σ'⟩ : TagSimp X) l).1
            = n + ∑ m ∈ (Finset.univ : Finset (Fin r)).erase j, (t.1 m).1 := by
          rw [← Finset.add_sum_erase _ _ hj, Function.update_self]
          exact congrArg (fun z => n + z) (Finset.sum_congr rfl hrest)
        have e2 : ∑ l, (t.1 l).1
            = (t.1 j).1 + ∑ m ∈ (Finset.univ : Finset (Fin r)).erase j, (t.1 m).1 :=
          (Finset.add_sum_erase _ _ hj).symm
        have ht : ∑ l, (t.1 l).1 = k + 1 := t.2
        omega
      exact tupIncl_tupUpdate_of_eq K X t.1 j ⟨n, σ'⟩ hdeg
  exact key (t.1 j) rfl

theorem tupIncl_tupD_single {k : ℕ} (t : TupIdx X r (k + 1)) :
    tupIncl K X r k (tupD K X r k (Finsupp.single t (1 : K)))
      = tupDAll K X r (tupIncl K X r (k + 1) (Finsupp.single t (1 : K))) := by
  rw [tupD_single, tupDGen, map_sum, tupIncl_single, tupDAll, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Finsupp.apply_linearCombination, slotBd_single, slotBdGen]
  congr 1
  exact tupLC_tupIncl_tupUpdate K X t j

/-- **The inclusion intertwines the two differentials.** -/
theorem tupIncl_comp_tupD (k : ℕ) :
    (tupIncl K X r k).comp (tupD K X r k) = (tupDAll K X r).comp (tupIncl K X r (k + 1)) := by
  apply Finsupp.lhom_ext'
  intro t
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  exact tupIncl_tupD_single K X t

/-- **`d ∘ d = 0` for the flat `r`-fold tensor power of the singular chains**, at every arity `r`
and over every commutative ring `K`. -/
theorem tupD_tupD (k : ℕ) (x : tupMod K X r (k + 1 + 1)) :
    tupD K X r k (tupD K X r (k + 1) x) = 0 := by
  apply tupIncl_injective K X k
  have h1 := LinearMap.congr_fun (tupIncl_comp_tupD K X k) (tupD K X r (k + 1) x)
  have h2 := LinearMap.congr_fun (tupIncl_comp_tupD K X (k + 1)) x
  simp only [LinearMap.comp_apply] at h1 h2
  rw [h1, h2, map_zero, ← Module.End.mul_apply, tupDAll_mul_self, LinearMap.zero_apply]

end FullModel

end

end GroupApproximation.CharClass
