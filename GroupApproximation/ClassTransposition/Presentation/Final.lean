import GroupApproximation.ClassTransposition.Presentation.RangeGe

/-!
# Kourovka 17.61: `CT_P(ℤ)` is finitely presented

Kourovka 17.61 lane (research node `ct-p-z-is-finitely-presented-by-position-shifting`).

* `swap_mem_range`: every class transposition over `P` is in the image of `evalH`;
* `range_evalH`: the image is exactly `CT_P(ℤ)` (with `range_le`);
* `kourovka1761`: `H P`, finitely presented by construction, is isomorphic to `CT_P(ℤ)`
  (`evalH_injective`), so `CT_P(ℤ)` is finitely presented.
-/

namespace GroupApproximation.ClassTransposition.Presentation

open GroupApproximation.Kourovka1759 Equiv Box

variable {P : Set ℕ}

/-- `F` lies inside `A`. -/
def SubB (A F : Box) : Prop := ∀ n, F.Mem n → A.Mem n

open Classical in
/-- The target modulus of a class mod `A.m * B.m`: refine it by `A.m` inside `A`, by `B.m` inside
`B`, and not at all elsewhere. -/
noncomputable def tgt (A B F : Box) : ℤ :=
  if SubB A F then A.m * B.m * A.m else if SubB B F then A.m * B.m * B.m else A.m * B.m

/-- `F` lies inside or outside each of `A` and `B`. -/
def QAB (A B F : Box) : Prop := (SubB A F ∨ F.Disj A) ∧ (SubB B F ∨ F.Disj B)

section Ge

variable (hpos : ∀ p ∈ P' P, 2 ≤ p) (hP2 : 2 ∉ P)
include hpos hP2

/-- Every class transposition over `P` is in the image of `evalH`. -/
theorem swap_mem_range {A B : Box} (h : A.Disj B) (hA : Adm P A) (hB : Adm P B) :
    swap A B h ∈ (evalH hpos hP2).range := by
  have hMpos : 0 < A.m * B.m := mul_pos A.m_pos B.m_pos
  obtain ⟨lM, hlM, hlMe⟩ := isPN_of_smooth hMpos (smooth_mul hA hB)
  obtain ⟨lA, hlA, hlAe⟩ := isPN_of_smooth A.m_pos hA
  obtain ⟨lB, hlB, hlBe⟩ := isPN_of_smooth B.m_pos hB
  -- all classes mod `A.m * B.m`
  obtain ⟨c1, hc1, hc1M⟩ := refine_to (P := P) (M := A.m * B.m) lM.length (comb 1)
    fun F hF => by
      rw [comb_one, List.mem_singleton] at hF
      subst hF
      exact ⟨lM, hlM, le_rfl, by rw [hlMe, show univ.m = 1 from rfl, one_mul]⟩
  -- refine the classes inside `A` by `A.m` and those inside `B` by `B.m`
  have hQ : ∀ F q X, QAB A B F → X ∈ kids F q → QAB A B X ∧ tgt A B X = tgt A B F := by
    intro F q X hQF hX
    have hsub := kids_sub X hX
    have hXr := mem_self_r X
    have hQX : QAB A B X :=
      ⟨hQF.1.imp (fun hs n hn => hs n (hsub n hn)) (fun hd n hn ha => hd n (hsub n hn) ha),
        hQF.2.imp (fun hs n hn => hs n (hsub n hn)) (fun hd n hn hb => hd n (hsub n hn) hb)⟩
    refine ⟨hQX, ?_⟩
    by_cases hA' : SubB A F
    · have : SubB A X := fun n hn => hA' n (hsub n hn)
      rw [tgt, tgt, if_pos hA', if_pos this]
    · have hdA : F.Disj A := hQF.1.resolve_left hA'
      have hXA : ¬ SubB A X := fun hs => hdA X.r (hsub _ hXr) (hs _ hXr)
      by_cases hB' : SubB B F
      · have : SubB B X := fun n hn => hB' n (hsub n hn)
        rw [tgt, tgt, if_neg hA', if_neg hXA, if_pos hB', if_pos this]
      · have hdB : F.Disj B := hQF.2.resolve_left hB'
        have hXB : ¬ SubB B X := fun hs => hdB X.r (hsub _ hXr) (hs _ hXr)
        rw [tgt, tgt, if_neg hA', if_neg hXA, if_neg hB', if_neg hXB]
  have hU : ∀ F ∈ real (comb 1) c1, QAB A B F ∧ RefTo P (tgt A B F) (lA.length + lB.length) F := by
    intro F hF
    have hFm := hc1M F hF
    have hQF : QAB A B F := ⟨sub_or_disj (by rw [hFm]; exact dvd_mul_right _ _),
      sub_or_disj (by rw [hFm]; exact dvd_mul_left _ _)⟩
    refine ⟨hQF, ?_⟩
    by_cases hA' : SubB A F
    · refine ⟨lA, hlA, by omega, ?_⟩
      rw [tgt, if_pos hA', hFm, ← hlAe]
    · by_cases hB' : SubB B F
      · refine ⟨lB, hlB, by omega, ?_⟩
        rw [tgt, if_neg hA', if_pos hB', hFm, ← hlBe]
      · refine ⟨[], by simp, Nat.zero_le _, ?_⟩
        rw [tgt, if_neg hA', if_neg hB', List.prod_nil, Nat.cast_one, mul_one]
        exact hFm.symm
  obtain ⟨c2, hc2, hc2M⟩ := refine_gen (tgt A B) (QAB A B) hQ _ _ hU
  have hl1 : levW 1 c1 = (real (comb 1) c1).length := by rw [length_real, length_comb]
  have hw : ValW P 1 (c1 ++ c2) := (valW_append P 1 c1 c2).2 ⟨hc1, by rw [hl1]; exact hc2⟩
  have hR := isPart_real (isPart_comb 1 one_pos) _ (ValW.ok hpos hw)
  have hRc : ∀ G ∈ real (comb 1) (c1 ++ c2), QAB A B G ∧ G.m = tgt A B G := by
    rw [real_append]; exact hc2M
  -- the children of `A` and `B` by `k = A.m * B.m`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = A.m * B.m := ⟨_, Int.toNat_of_nonneg hMpos.le⟩
  have hk0 : 0 < k := by omega
  have hmemA : ∀ j : Fin k, place A (child k j) ∈ real (comb 1) (c1 ++ c2) := by
    intro j
    refine mem_of_cover hR fun G hG hGm => ?_
    obtain ⟨hQG, hGT⟩ := hRc G hG
    have hAr : A.Mem (place A (child k j)).r := place_mem_of (mem_self_r _)
    have hSA : SubB A G := hQG.1.resolve_right fun hd => hd _ hGm hAr
    rw [hGT, place_m, child_m, hk, tgt, if_pos hSA]
  have hmemB : ∀ j : Fin k, place B (child k j) ∈ real (comb 1) (c1 ++ c2) := by
    intro j
    refine mem_of_cover hR fun G hG hGm => ?_
    obtain ⟨hQG, hGT⟩ := hRc G hG
    have hBr : B.Mem (place B (child k j)).r := place_mem_of (mem_self_r _)
    have hSB : SubB B G := hQG.2.resolve_right fun hd => hd _ hGm hBr
    have hSA : ¬ SubB A G := fun hs => h _ (hs _ (mem_self_r G)) (hSB _ (mem_self_r G))
    rw [hGT, place_m, child_m, hk, tgt, if_neg hSA, if_pos hSB]
  rw [← swap_split h k hk0]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact swap_mem_range_of_mem hpos hP2 hw (hmemA j) (hmemB j) (disj_place_of h)

theorem range_ge : classTranspositionGroupOver P ≤ (evalH hpos hP2).range := by
  rw [classTranspositionGroupOver, Subgroup.closure_le]
  intro g hg
  obtain ⟨A, B, h, hA, hB, rfl⟩ := IsClassTranspositionOver.eq_swap hg
  exact swap_mem_range hpos hP2 h hA hB

end Ge

theorem range_evalH (hB : BddAbove (P' P)) (hP2 : 2 ∉ P) (hpos : ∀ p ∈ P' P, 2 ≤ p)
    (hprime : ∀ p ∈ P' P, p.Prime) : (evalH hpos hP2).range = classTranspositionGroupOver P :=
  le_antisymm (range_le hB hP2 hpos hprime) (range_ge hpos hP2)

/-- **Kourovka 17.61.** For every finite set `P` of odd primes, `CT_P(ℤ)` is finitely
presented. -/
theorem kourovka1761 : kourovka1761Statement := by
  intro P hP hodd
  have hprime : ∀ p ∈ P' P, p.Prime := fun p hp => by
    rcases hp with rfl | hp
    · exact Nat.prime_two
    · exact (hodd p hp).1
  have hpos : ∀ p ∈ P' P, 2 ≤ p := fun p hp => (hprime p hp).two_le
  have hP2 : 2 ∉ P := fun h => (hodd 2 h).2 rfl
  have hfin : (P' P).Finite := hP.insert 2
  have hB : BddAbove (P' P) := hfin.bddAbove
  haveI : Finite ↥(P' P) := hfin.to_subtype
  haveI : Finite ↥P := hP.to_subtype
  haveI : Finite ↥(rels P) := (relSet_finite (P := P) (bnd P) (Inst.Valid P)).to_subtype
  haveI : Group.IsFinitelyPresented (H P) := inferInstance
  exact Group.IsFinitelyPresented.equiv ((MonoidHom.ofInjective
    (evalH_injective hB hP2 hpos hprime)).trans (MulEquiv.subgroupCongr (range_evalH hB hP2 hpos hprime)))

end GroupApproximation.ClassTransposition.Presentation
