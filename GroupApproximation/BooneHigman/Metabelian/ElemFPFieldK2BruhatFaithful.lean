import GroupApproximation.BooneHigman.Metabelian.ElemFPFieldK2BruhatStatement
import GroupApproximation.Meta.AxiomGuard

/-!
# Faithful action of `St_I(F_p)`, from the big Bruhat cell

Lane `bh-met-55`.  Assume `BruhatBigCellStatement`, and let `|I| ≥ 3`.  For every finset
`K ⊆ I`, an element of `G_K = rootSpan (i ∈ K ∧ j ∈ K)` that acts trivially on `F_p^I` is
trivial (`bruhat_eq_one_of_act`).  The proof is Finset induction on `K`.

* `K = ∅` and `K = {L}`: there are no generating roots.
* `K = K' ∪ {L}` with `m ∈ K'`: the statement gives `g = u s v h_mL(c)`.
  * Reading coordinate `L` of `g e_L` gives `c = 1` (`bruhat_act_h_unitVec`, `bruhat_h_one`).
  * Then `u e_L = e_L`, so `u = 1` (`eq_one_of_col_fix_finset`).
  * Coordinate `L` of `g e_k`, for `k ≠ L`, gives `v = 1` (`eq_one_of_row_zero_finset`).
  * Finally `g = s ∈ G_{K'}`, and the induction hypothesis applies.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2

open GroupApproximation.SteinbergGroup
open GroupApproximation.SimpleKazhdanSofic.SkRows.SteinbergWeyl (h)
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittK2.FieldTwo (rootSpan act unitVec
  unitVec_apply act_mul act_apply_of_rootSpan act_eq_self_of_rootSpan
  eq_one_of_col_fix_finset eq_one_of_row_zero_finset)

/-- **Faithfulness on root spans.**  Assume the big Bruhat cell statement and `|I| ≥ 3`.  An
element of `G_K` acting trivially on `F_p^I` is trivial. -/
theorem bruhat_eq_one_of_act (hstat : BruhatBigCellStatement) (p : ℕ) [Fact p.Prime]
    (I : Type) [Fintype I] [DecidableEq I] (hI : 3 ≤ Fintype.card I) (K : Finset I) :
    ∀ g ∈ rootSpan (R := ZMod p) (fun i j => i ∈ K ∧ j ∈ K),
      (∀ w : I → ZMod p, act g w = w) → g = 1 := by
  induction K using Finset.induction_on with
  | empty =>
    intro g hg _
    exact rootSpan_induction (Q := fun g => g = 1)
      (fun i _ _ _ hp => absurd hp.1 (Finset.notMem_empty i)) rfl
      (fun g₁ g₂ _ _ h1 h2 => show g₁ * g₂ = 1 by
        rw [show g₁ = 1 from h1, show g₂ = 1 from h2, mul_one]) hg
  | insert L K hLK ih =>
    intro g hg hfix
    rcases K.eq_empty_or_nonempty with hK | ⟨m, hm⟩
    · subst hK
      exact bruhat_rootSpan_singleton_eq_one L hg
    · have hmL : m ≠ L := fun e => hLK (by rw [← e]; exact hm)
      have hLL : act g (unitVec L) L ≠ 0 := by
        rw [hfix, unitVec_apply, if_pos rfl]
        exact one_ne_zero
      obtain ⟨u, hu, s, hs, v, hv, c, rfl⟩ := hstat p I hI K L m hLK hm hmL g hg hLL
      -- Step 1: `c = 1`.
      have hz : ∀ j, j ∈ K → act (h m L hmL c) (unitVec L) j = 0 := fun j hj => by
        rw [bruhat_act_h_unitVec, if_neg (fun e : j = L => hLK (by rw [← e]; exact hj))]
      have hv' : act v (act (h m L hmL c) (unitVec L)) = act (h m L hmL c) (unitVec L) :=
        act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K) (fun _ j hp => hz j hp.2) hv
      have hs' : act s (act (h m L hmL c) (unitVec L)) = act (h m L hmL c) (unitVec L) :=
        act_eq_self_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (fun _ j hp => hz j hp.2) hs
      have hu' : act u (act (h m L hmL c) (unitVec L)) L =
          act (h m L hmL c) (unitVec L) L :=
        act_apply_of_rootSpan (p := fun i j => j = L ∧ i ∈ K) (k := L)
          (fun i _ hp hiL => hLK (by rw [← hiL]; exact hp.2)) hu _
      have hc : c = 1 := by
        have e := congrFun (hfix (unitVec L)) L
        rw [act_mul, act_mul, act_mul, hv', hs', hu', bruhat_act_h_unitVec, if_pos rfl,
          unitVec_apply, if_pos rfl] at e
        exact inv_eq_one.mp (Units.val_eq_one.mp e)
      subst hc
      rw [bruhat_h_one, mul_one] at hfix
      rw [bruhat_h_one, mul_one]
      -- Step 2: `u = 1`.
      have hu1 : u = 1 := by
        refine eq_one_of_col_fix_finset L K hLK u hu ?_
        have e := hfix (unitVec L)
        rw [act_mul, act_mul,
          act_eq_self_of_rootSpan (p := fun i j => i = L ∧ j ∈ K)
            (fun _ j hp => bruhat_unitVec_eq_zero hLK j hp.2) hv,
          act_eq_self_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K)
            (fun _ j hp => bruhat_unitVec_eq_zero hLK j hp.2) hs] at e
        exact e
      subst hu1
      rw [one_mul] at hfix
      rw [one_mul]
      -- Step 3: `v = 1`.
      have hv1 : v = 1 := by
        refine eq_one_of_row_zero_finset L K hLK v hv ?_
        intro k hk
        have e := congrFun (hfix (unitVec k)) L
        have hsL : act s (act v (unitVec k)) L = act v (unitVec k) L :=
          act_apply_of_rootSpan (p := fun i j => i ∈ K ∧ j ∈ K) (k := L)
            (fun i _ hp hiL => hLK (by rw [← hiL]; exact hp.1)) hs _
        rw [act_mul, hsL, unitVec_apply, if_neg hk.symm] at e
        exact e
      subst hv1
      rw [mul_one] at hfix
      rw [mul_one]
      -- Step 4: induction hypothesis.
      exact ih s hs hfix

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2.bruhat_eq_one_of_act

end GroupApproximation.BooneHigman.Metabelian.ElemFP.FieldK2
