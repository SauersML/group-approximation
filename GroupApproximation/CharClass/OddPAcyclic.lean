import GroupApproximation.CharClass.OddPAcyclicSlot
import GroupApproximation.CharClass.OddPAcyclicSimplex
import GroupApproximation.Meta.AxiomGuard

/-!
# The flat `r`-fold tensor power of the singular chains is acyclic on the models

Lane `lix-cupone`, block `OddPAcyclic*` (lix-steenrod's plan §3.4, route (A)).  The export is the
`AcyclicOnModels` field shape `lix-steenrod`'s `OddPTupleFunctor` wraps at `K = ZMod p`:

```text
tupD_exists_preimage_stdSimplexTop (K) [Field K] (n r k) (y) (hy : tupD y = 0) :
  ∃ z, tupD z = y.
```

## The argument

`OddPAcyclicSlot.tupDAll_mul_contrOp_add` gives, on the full model, `d S + S d = 1 - E` with
`S = contrOp slotS slotE` and `E = slotE 0 * ⋯ * slotE (r-1)`, from the positive-degree acyclicity of
one slot.  Three grading facts turn that into the statement:

* `E` kills every tuple of positive total degree: some slot has positive degree, `slotE` of that slot
  kills the tuple, and every other `slotE` keeps that slot as it is (`OddPAcyclicAlgebra.eAll_eq_zero`);
* `S` raises the total degree by one, because `slotS` does and `slotE` keeps it
  (`OddPAcyclicAlgebra.contrOp_mem`), so `S y` is the image of a degree-`(k+2)` element;
* the degree-`k` carrier embeds in the full model by `tupIncl`, intertwining `tupD` with `tupDAll`
  (`OddPTupleD.tupIncl_comp_tupD`).

A positive-degree cycle `y` then satisfies `d (S y) = y`, and `S y` is the preimage.  Positive-degree
acyclicity of one slot on a standard simplex is `OddPAcyclicSimplex`.
-/

namespace GroupApproximation.CharClass

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

namespace OddPAcyclic

variable (K : Type) [Field K] (X : TopCat.{0})

/-! ## 1. Grading on the full model -/

/-- The tuples of total degree `m`. -/
def degSet (r m : ℕ) : Set (TupAll X r) := {t | ∑ l, (t l).1 = m}

/-- The degree-`m` part of the full model. -/
abbrev degSub (r m : ℕ) : Submodule K (tupAllMod K X r) := Finsupp.supported K K (degSet X r m)

/-- A linear map sending every basis tuple of `s` into `V` sends everything supported on `s`
into `V`. -/
theorem mem_of_supported {r : ℕ} (A : Module.End K (tupAllMod K X r)) (s : Set (TupAll X r))
    (V : Submodule K (tupAllMod K X r)) (h : ∀ t ∈ s, A (Finsupp.single t (1 : K)) ∈ V)
    (x : tupAllMod K X r) (hx : x ∈ Finsupp.supported K K s) : A x ∈ V := by
  rw [Finsupp.supported_eq_span_single] at hx
  have hle : Submodule.span K ((fun t => Finsupp.single t (1 : K)) '' s) ≤ V.comap A := by
    rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    exact h t ht
  exact hle hx

/-- A linear combination of members of a submodule is a member. -/
theorem tupLC_mem {α M : Type} [AddCommGroup M] [Module K M] (V : Submodule K M) (v : α → M)
    (hv : ∀ a, v a ∈ V) (z : α →₀ K) : Finsupp.linearCombination K v z ∈ V := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact V.zero_mem
  | add x y hx hy => rw [map_add]; exact V.add_mem hx hy
  | single a c => rw [Finsupp.linearCombination_single]; exact V.smul_mem c (hv a)

/-- Replacing one slot changes the total degree by the change in that slot. -/
theorem sum_fst_update {r : ℕ} (t : TupAll X r) (j : Fin r) (τ : TagSimp X) :
    ∑ l, (Function.update t j τ l).1 + (t j).1 = ∑ l, (t l).1 + τ.1 := by
  have hj : j ∈ (Finset.univ : Finset (Fin r)) := Finset.mem_univ j
  have hrest : ∀ m ∈ (Finset.univ : Finset (Fin r)).erase j,
      (Function.update t j τ m).1 = (t m).1 := by
    intro m hm
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hm)]
  have e1 : ∑ l, (Function.update t j τ l).1
      = τ.1 + ∑ m ∈ (Finset.univ : Finset (Fin r)).erase j, (t m).1 := by
    rw [← Finset.add_sum_erase _ _ hj, Function.update_self]
    exact congrArg (fun z => τ.1 + z) (Finset.sum_congr rfl hrest)
  have e2 : ∑ l, (t l).1 = (t j).1 + ∑ m ∈ (Finset.univ : Finset (Fin r)).erase j, (t m).1 :=
    (Finset.add_sum_erase _ _ hj).symm
  omega

/-- **The slot contraction raises the total degree by one.** -/
theorem slotS_mem {r : ℕ} (j : Fin r) (m : ℕ) (x : tupAllMod K X r) (hx : x ∈ degSub K X r m) :
    slotS K X j x ∈ degSub K X r (m + 1) := by
  refine mem_of_supported K X (slotS K X j) (degSet X r m) (degSub K X r (m + 1))
    (fun t ht => ?_) x hx
  rw [slotS, slotOp_single]
  refine (degSub K X r (m + 1)).smul_mem _ ?_
  have key : ∀ τ₀ : TagSimp X, t j = τ₀ →
      slotLift K X t j (tagS K X τ₀) ∈ degSub K X r (m + 1) := by
    intro τ₀ h
    obtain ⟨n, σ⟩ := τ₀
    rw [tagS_eq, slotLift, Finsupp.linearCombination_mapDomain]
    refine tupLC_mem K _ _ (fun σ' => Finsupp.single_mem_supported K (1 : K) ?_) _
    show ∑ l, (Function.update t j (⟨n + 1, σ'⟩ : TagSimp X) l).1 = m + 1
    have hs : ∑ l, (Function.update t j (⟨n + 1, σ'⟩ : TagSimp X) l).1 + (t j).1
        = ∑ l, (t l).1 + (n + 1) := sum_fst_update X t j ⟨n + 1, σ'⟩
    have ht' : ∑ l, (t l).1 = m := ht
    have hj : (t j).1 = n := by rw [h]
    omega
  exact key (t j) rfl

/-- **The slot projection keeps the total degree.** -/
theorem slotE_mem {r : ℕ} (j : Fin r) (m : ℕ) (x : tupAllMod K X r) (hx : x ∈ degSub K X r m) :
    slotE K X j x ∈ degSub K X r m := by
  refine mem_of_supported K X (slotE K X j) (degSet X r m) (degSub K X r m)
    (fun t ht => ?_) x hx
  rw [slotE, slotOp_single]
  refine (degSub K X r m).smul_mem _ ?_
  have key : ∀ τ₀ : TagSimp X, t j = τ₀ → slotLift K X t j (tagE K X τ₀) ∈ degSub K X r m := by
    intro τ₀ h
    obtain ⟨n, σ⟩ := τ₀
    cases n with
    | zero =>
      rw [tagE_zero_eq, slotLift, Finsupp.linearCombination_mapDomain]
      refine tupLC_mem K _ _ (fun σ' => Finsupp.single_mem_supported K (1 : K) ?_) _
      show ∑ l, (Function.update t j (⟨0, σ'⟩ : TagSimp X) l).1 = m
      have hs : ∑ l, (Function.update t j (⟨0, σ'⟩ : TagSimp X) l).1 + (t j).1
          = ∑ l, (t l).1 + 0 := sum_fst_update X t j ⟨0, σ'⟩
      have ht' : ∑ l, (t l).1 = m := ht
      have hj : (t j).1 = 0 := by rw [h]
      omega
    | succ n =>
      rw [tagE_succ, map_zero]
      exact (degSub K X r m).zero_mem
  exact key (t j) rfl

/-- The tuples whose slot `j` has positive degree. -/
def posSet (r : ℕ) (j : Fin r) : Set (TupAll X r) := {t | (t j).1 ≠ 0}

/-- `slotE j` kills a tuple whose slot `j` has positive degree. -/
theorem slotE_posSet {r : ℕ} (j : Fin r) (x : tupAllMod K X r)
    (hx : x ∈ Finsupp.supported K K (posSet X r j)) : slotE K X j x = 0 := by
  have hbasis : ∀ t ∈ posSet X r j,
      slotE K X j (Finsupp.single t (1 : K)) ∈ (⊥ : Submodule K (tupAllMod K X r)) := by
    intro t ht
    have ht' : (t j).1 ≠ 0 := ht
    rw [Submodule.mem_bot, slotE, slotOp_single]
    have key : ∀ τ₀ : TagSimp X, t j = τ₀ → slotLift K X t j (tagE K X τ₀) = 0 := by
      intro τ₀ h
      obtain ⟨n, σ⟩ := τ₀
      cases n with
      | zero => exact absurd (by rw [h]) ht'
      | succ n => rw [tagE_succ, map_zero]
    rw [key (t j) rfl, smul_zero]
  exact (Submodule.mem_bot K).mp (mem_of_supported K X (slotE K X j) (posSet X r j) ⊥ hbasis x hx)

/-- `slotE l`, `l ≠ j`, keeps slot `j` as it is. -/
theorem slotE_mem_posSet {r : ℕ} {j l : Fin r} (hlj : l ≠ j) (x : tupAllMod K X r)
    (hx : x ∈ Finsupp.supported K K (posSet X r j)) :
    slotE K X l x ∈ Finsupp.supported K K (posSet X r j) := by
  refine mem_of_supported K X (slotE K X l) (posSet X r j) (Finsupp.supported K K (posSet X r j))
    (fun t ht => ?_) x hx
  rw [slotE, slotOp_single]
  refine Submodule.smul_mem _ _ ?_
  rw [slotLift]
  refine tupLC_mem K _ _ (fun τ => Finsupp.single_mem_supported K (1 : K) ?_) _
  show (Function.update t l τ j).1 ≠ 0
  rw [Function.update_of_ne hlj.symm]
  exact ht

/-- **The projection of everything kills positive total degree.** -/
theorem eAll_slotE_mem_degSub_succ {r : ℕ} (k : ℕ) (x : tupAllMod K X r)
    (hx : x ∈ degSub K X r (k + 1)) : eAll (fun j : Fin r => slotE K X j) x = 0 := by
  have hbasis : ∀ t ∈ degSet X r (k + 1),
      eAll (fun j : Fin r => slotE K X j) (Finsupp.single t (1 : K))
        ∈ (⊥ : Submodule K (tupAllMod K X r)) := by
    intro t ht
    rw [Submodule.mem_bot]
    have hne : ∑ l, (t l).1 ≠ 0 := by
      have ht' : ∑ l, (t l).1 = k + 1 := ht
      omega
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact eAll_eq_zero (fun i : Fin r => slotE K X i) (Finsupp.supported K K (posSet X r j)) j
      (fun v hv => slotE_posSet K X j v hv)
      (fun l hlj v hv => slotE_mem_posSet K X hlj v hv)
      (Finsupp.single t (1 : K)) (Finsupp.single_mem_supported K (1 : K) hj)
  exact (Submodule.mem_bot K).mp
    (mem_of_supported K X _ (degSet X r (k + 1)) ⊥ hbasis x hx)

/-- The degree-`m` carrier lands in the degree-`m` part of the full model. -/
theorem tupIncl_mem {r : ℕ} (m : ℕ) (y : tupMod K X r m) : tupIncl K X r m y ∈ degSub K X r m := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero]; exact (degSub K X r m).zero_mem
  | add u v hu hv => rw [map_add]; exact (degSub K X r m).add_mem hu hv
  | single t c =>
    rw [tupIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    exact Finsupp.single_mem_supported K c t.2

/-- Everything in the degree-`m` part of the full model comes from the degree-`m` carrier. -/
theorem exists_tupIncl_eq {r : ℕ} (m : ℕ) (w : tupAllMod K X r) (hw : w ∈ degSub K X r m) :
    ∃ z : tupMod K X r m, tupIncl K X r m z = w := by
  refine ⟨Finsupp.comapDomain Subtype.val w Subtype.val_injective.injOn, ?_⟩
  rw [tupIncl, Finsupp.lmapDomain_apply]
  refine Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective w ?_
  rw [Set.range_coe_subtype]
  exact hw

/-! ## 2. The assembly -/

/-- **Positive-degree acyclicity passes from one slot to the flat `r`-fold tensor power**, over a
field, at every arity. -/
theorem tupD_exists_preimage_of_ker_le_range
    (hK : ∀ k : ℕ, LinearMap.ker (((singFreeR K).obj X).d (k + 1) k).hom
      ≤ LinearMap.range (((singFreeR K).obj X).d (k + 2) (k + 1)).hom)
    (r k : ℕ) (y : tupMod K X r (k + 1)) (hy : tupD K X r k y = 0) :
    ∃ z : tupMod K X r (k + 2), tupD K X r (k + 1) z = y := by
  have hmain := LinearMap.congr_fun (tupDAll_mul_contrOp_add K X hK r) (tupIncl K X r (k + 1) y)
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply] at hmain
  have hd : tupDAll K X r (tupIncl K X r (k + 1) y) = 0 := by
    have h := LinearMap.congr_fun (tupIncl_comp_tupD K X k) y
    simp only [LinearMap.comp_apply] at h
    rw [← h, hy, map_zero]
  have hE := eAll_slotE_mem_degSub_succ K X k (tupIncl K X r (k + 1) y)
    (tupIncl_mem K X (k + 1) y)
  rw [hd, map_zero, add_zero, hE, sub_zero] at hmain
  have hS : contrOp (fun j : Fin r => slotS K X j) (fun j => slotE K X j)
      (tupIncl K X r (k + 1) y) ∈ degSub K X r (k + 1 + 1) :=
    contrOp_mem (degSub K X r) (fun j : Fin r => slotS K X j) (fun j => slotE K X j)
      (fun j m v hv => slotS_mem K X j m v hv) (fun j m v hv => slotE_mem K X j m v hv)
      (k + 1) _ (tupIncl_mem K X (k + 1) y)
  obtain ⟨z, hz⟩ := exists_tupIncl_eq K X (k + 1 + 1) _ hS
  refine ⟨z, tupIncl_injective K X (k + 1) ?_⟩
  have h := LinearMap.congr_fun (tupIncl_comp_tupD K X (k + 1)) z
  simp only [LinearMap.comp_apply] at h
  rw [h, hz]
  exact hmain

end OddPAcyclic

/-- **The acyclicity hypothesis of the tuple target on the models**: over a field, a positive-degree
cycle of the flat `r`-fold tensor power of the singular chains of a standard simplex is a boundary. -/
theorem tupD_exists_preimage_stdSimplexTop (K : Type) [Field K] (n r k : ℕ)
    (y : tupMod K (stdSimplexTop n) r (k + 1)) (hy : tupD K (stdSimplexTop n) r k y = 0) :
    ∃ z : tupMod K (stdSimplexTop n) r (k + 2), tupD K (stdSimplexTop n) r (k + 1) z = y :=
  OddPAcyclic.tupD_exists_preimage_of_ker_le_range K (stdSimplexTop n)
    (OddPAcyclic.singFreeR_ker_le_range_stdSimplexTop K n) r k y hy

/-- Over every field, every positive-degree cycle of the flat `r`-fold tensor power of the signed
singular chains of a standard simplex is a boundary. -/
def PrintedTupleAcyclicOnModels : Prop :=
  ∀ (K : Type) [Field K] (n r k : ℕ) (y : tupMod K (stdSimplexTop n) r (k + 1)),
    tupD K (stdSimplexTop n) r k y = 0 →
      ∃ z : tupMod K (stdSimplexTop n) r (k + 2), tupD K (stdSimplexTop n) r (k + 1) z = y

theorem printedTupleAcyclicOnModels : PrintedTupleAcyclicOnModels := by
  intro K _ n r k y hy
  exact tupD_exists_preimage_stdSimplexTop K n r k y hy

#audit_closed_axioms printedTupleAcyclicOnModels

end

end GroupApproximation.CharClass
