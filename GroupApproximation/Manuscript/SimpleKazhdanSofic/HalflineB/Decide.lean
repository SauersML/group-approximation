import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Represent
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (b): deciding a table from equality in `Λ`

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline` (b), tex l.661–664 (sentence e3cd35e16e2f):

> After collecting equal ξ and equal coordinates, the word is trivial if and only if every coefficient of its
> difference from I_3 vanishes at every assignment of its finitely many variables, as Ω is the full shift.

## Proof route

* `o a b` stands for the answer to "`ξ_a = ξ_b` in `Λ`" (in the reduction, an oracle answer). From it, the atom
  `x ↦ x(δ_p) + c_p(δ_p)` of a word `p` at the point `xB B` (the indicator of the values `δ_v`, `v ∈ B`) is the
  Boolean `atomB o B p` (`b2_atomB`): `x(δ_p) = 1` iff some `v ∈ B` has `δ_v = δ_p`, compared as the words `dW v` and
  `dW p` in `Λ`, and `c_p(δ_p)` is the parity of the prefixes of `p` with value `δ_p` (`lampSum_apply`).
* Collecting equal `ξ`: `coeffB o B T a0` is the coefficient of `ξ_{a0}` of the table `T` at `xB B` (`b2_coeffB`).
* The finitely many variables: the value of a table at a point `x` only depends on the coordinates `x(δ_p)` for the
  atoms `p` of the table (`hCoeffLC_agree`), so it is its value at `xB B` for the subset `B` of atoms `p` with
  `x(δ_p) = 1` (`xB_filter`). So the table vanishes iff every coefficient vanishes at every `xB B`, `B` ranging over
  the subsets of its atoms (`tabOk_iff`), and a matrix word is trivial iff all its tables pass (`matOk_iff`,
  `wordValue_eq_one_iff_matOk`).
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic
namespace HalflineB

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.SimpleKazhdanSofic.Lamplighter

/-! ### Boolean folds -/

section Folds

variable {α : Type}

/-- Whether some element passes. -/
def anyB (l : List α) (f : α → Bool) : Bool :=
  l.foldr (fun a acc => f a || acc) false

/-- Whether every element passes. -/
def allB (l : List α) (f : α → Bool) : Bool :=
  l.foldr (fun a acc => f a && acc) true

/-- Exclusive or. -/
def bxor (b c : Bool) : Bool :=
  cond b (!c) c

/-- The parity of the passing elements. -/
def parB (l : List α) (f : α → Bool) : Bool :=
  l.foldr (fun a acc => bxor (f a) acc) false

theorem anyB_nil (f : α → Bool) : anyB [] f = false :=
  rfl

theorem anyB_cons (a : α) (l : List α) (f : α → Bool) : anyB (a :: l) f = (f a || anyB l f) :=
  rfl

theorem allB_nil (f : α → Bool) : allB [] f = true :=
  rfl

theorem allB_cons (a : α) (l : List α) (f : α → Bool) : allB (a :: l) f = (f a && allB l f) :=
  rfl

theorem parB_nil (f : α → Bool) : parB [] f = false :=
  rfl

theorem parB_cons (a : α) (l : List α) (f : α → Bool) : parB (a :: l) f = bxor (f a) (parB l f) :=
  rfl

theorem anyB_eq_true (l : List α) (f : α → Bool) : anyB l f = true ↔ ∃ a ∈ l, f a = true := by
  induction l with
  | nil => simp [anyB_nil]
  | cons a l ih => rw [anyB_cons, Bool.or_eq_true, ih, List.exists_mem_cons]

theorem allB_eq_true (l : List α) (f : α → Bool) : allB l f = true ↔ ∀ a ∈ l, f a = true := by
  induction l with
  | nil => simp [allB_nil]
  | cons a l ih => rw [allB_cons, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem parB_congr {f g : α → Bool} (l : List α) (h : ∀ a ∈ l, f a = g a) : parB l f = parB l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [parB_cons, parB_cons, h a List.mem_cons_self, ih fun b hb => h b (List.mem_cons_of_mem a hb)]

end Folds

/-! ### Parities in `ZMod 2` -/

/-- A Boolean as an element of `F₂`. -/
def b2 (b : Bool) : ZMod 2 :=
  cond b 1 0

theorem b2_true : b2 true = 1 :=
  rfl

theorem b2_false : b2 false = 0 :=
  rfl

theorem b2_bxor (b c : Bool) : b2 (bxor b c) = b2 b + b2 c := by
  cases b <;> cases c <;> decide

theorem b2_and (b c : Bool) : b2 (b && c) = b2 b * b2 c := by
  cases b <;> cases c <;> decide

theorem not_eq_true_iff_b2 (b : Bool) : (!b) = true ↔ b2 b = 0 := by
  cases b <;> decide

theorem b2_decide_eq_one (a : ZMod 2) : b2 (decide (a = 1)) = a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;> decide

theorem b2_parB {α : Type} (l : List α) (f : α → Bool) : b2 (parB l f) = (l.map fun a => b2 (f a)).sum := by
  induction l with
  | nil => rw [parB_nil, b2_false, List.map_nil, List.sum_nil]
  | cons a l ih => rw [parB_cons, b2_bxor, ih, List.map_cons, List.sum_cons]

theorem cast_length_filter {α : Type} (l : List α) (f : α → Bool) :
    ((l.filter f).length : ZMod 2) = b2 (parB l f) := by
  induction l with
  | nil => rw [List.filter_nil, List.length_nil, Nat.cast_zero, parB_nil, b2_false]
  | cons a l ih =>
    rw [parB_cons, b2_bxor, ← ih]
    cases h : f a
    · rw [List.filter_cons_of_neg (by simp [h]), b2_false, zero_add]
    · rw [List.filter_cons_of_pos h, List.length_cons, Nat.cast_succ, b2_true, add_comm]

/-! ### Subsets -/

section Subsets

variable {α : Type}

/-- All sublists of a list. -/
def subsets (U : List α) : List (List α) :=
  U.foldr (fun u Bs => Bs.flatMap fun B => [B, u :: B]) [[]]

theorem subsets_nil : subsets ([] : List α) = [[]] :=
  rfl

theorem subsets_cons (u : α) (U : List α) : subsets (u :: U) = (subsets U).flatMap fun B => [B, u :: B] :=
  rfl

theorem filter_mem_subsets (p : α → Bool) (U : List α) : U.filter p ∈ subsets U := by
  induction U with
  | nil =>
    rw [List.filter_nil, subsets_nil]
    exact List.mem_singleton_self _
  | cons u U ih =>
    rw [subsets_cons, List.mem_flatMap]
    refine ⟨U.filter p, ih, ?_⟩
    cases h : p u
    · rw [List.filter_cons_of_neg (by simp [h])]
      exact List.mem_cons_self
    · rw [List.filter_cons_of_pos h]
      exact List.mem_cons_of_mem _ List.mem_cons_self

theorem mem_subsets_sub (U : List α) : ∀ B ∈ subsets U, ∀ v ∈ B, v ∈ U := by
  induction U with
  | nil =>
    intro B hB v hv
    rw [subsets_nil, List.mem_singleton] at hB
    subst hB
    exact absurd hv List.not_mem_nil
  | cons u U ih =>
    intro B hB v hv
    rw [subsets_cons, List.mem_flatMap] at hB
    obtain ⟨B', hB', hmem⟩ := hB
    rcases List.mem_cons.1 hmem with h1 | h2
    · rw [h1] at hv
      exact List.mem_cons_of_mem u (ih _ hB' v hv)
    · rw [List.mem_singleton] at h2
      rw [h2] at hv
      rcases List.mem_cons.1 hv with h3 | h3
      · rw [h3]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem u (ih _ hB' v h3)

end Subsets

/-! ### Atoms, cylinders and coefficients from equality in `Λ` -/

variable {Δ : Type} [Group Δ] {ι : Type}

/-- The `Δ`-letters of a word, as a word in `Λ`. -/
def dW (p : LW ι) : LW ι :=
  liftD (deltaWord p)

open Classical in
/-- The point of `Ω` with `x(h) = 1` iff `h = δ_v` for some `v ∈ B`. -/
noncomputable def xB (s : ι → Δ) (B : List (LW ι)) : LampSpace Δ :=
  fun h => b2 (anyB B fun v => decide (wordValue s (deltaWord v) = h))

theorem xB_eq_b2 (s : ι → Δ) (B : List (LW ι)) (h : Δ) (c : Bool)
    (hc : c = true ↔ ∃ v ∈ B, wordValue s (deltaWord v) = h) : xB s B h = b2 c := by
  simp only [xB]
  congr 1
  refine Bool.eq_iff_iff.2 ?_
  rw [anyB_eq_true, hc]
  simp only [decide_eq_true_eq]

/-- The atom of `p` at `xB B`, from the answers `o`. -/
def atomB (o : LW ι → LW ι → Bool) (B : List (LW ι)) (p : LW ι) : Bool :=
  bxor (anyB B fun v => o (dW v) (dW p)) (parB (lampPrefixes p) fun q => o (liftD q) (dW p))

theorem b2_atomB (s : ι → Δ) {o : LW ι → LW ι → Bool} {S : List (LW ι)}
    (ho : ∀ a ∈ S, ∀ b ∈ S, o a b = true ↔ wordValue (lampGen s) a = wordValue (lampGen s) b)
    (B : List (LW ι)) (hB : ∀ v ∈ B, dW v ∈ S) (p : LW ι) (hp : dW p ∈ S)
    (hq : ∀ q ∈ lampPrefixes p, liftD q ∈ S) :
    b2 (atomB o B p) = hAtom s p (xB s B) := by
  classical
  rw [hAtom_apply, lampSum_apply, cast_length_filter, atomB, b2_bxor]
  congr 1
  · refine (xB_eq_b2 s B _ _ ?_).symm
    rw [anyB_eq_true]
    refine exists_congr fun v => and_congr_right fun hv => ?_
    rw [ho _ (hB v hv) _ hp, dW, dW, wordValue_lampGen_liftD, wordValue_lampGen_liftD,
      SemidirectProduct.inr_injective.eq_iff]
  · congr 1
    refine parB_congr _ fun q hq' => ?_
    show o (liftD q) (dW p) = decide (wordValue s q = wordValue s (deltaWord p))
    refine Bool.eq_iff_iff.2 ?_
    rw [ho _ (hq q hq') _ hp, dW, wordValue_lampGen_liftD, wordValue_lampGen_liftD,
      SemidirectProduct.inr_injective.eq_iff, decide_eq_true_eq]

/-- The atom product of `P` at `xB B`. -/
def cylB (o : LW ι → LW ι → Bool) (B : List (LW ι)) (P : List (LW ι)) : Bool :=
  allB P (atomB o B)

theorem cylB_cons (o : LW ι → LW ι → Bool) (B : List (LW ι)) (p : LW ι) (P : List (LW ι)) :
    cylB o B (p :: P) = (atomB o B p && cylB o B P) :=
  rfl

theorem b2_cylB (s : ι → Δ) {o : LW ι → LW ι → Bool} {S : List (LW ι)}
    (ho : ∀ a ∈ S, ∀ b ∈ S, o a b = true ↔ wordValue (lampGen s) a = wordValue (lampGen s) b)
    (B : List (LW ι)) (hB : ∀ v ∈ B, dW v ∈ S) (P : List (LW ι))
    (hP : ∀ p ∈ P, dW p ∈ S ∧ ∀ q ∈ lampPrefixes p, liftD q ∈ S) :
    b2 (cylB o B P) = hCyl s P (xB s B) := by
  induction P with
  | nil => simp only [cylB, allB_nil, b2_true, hCyl, LocallyConstant.one_apply]
  | cons p P ih =>
    rw [cylB_cons, b2_and, ih fun p' hp' => hP p' (List.mem_cons_of_mem p hp'),
      b2_atomB s ho B hB p (hP p List.mem_cons_self).1 (hP p List.mem_cons_self).2, hCyl,
      LocallyConstant.mul_apply]

/-- The coefficient of `ξ_{a0}` of `T` at `xB B`. -/
def coeffB (o : LW ι → LW ι → Bool) (B : List (LW ι)) (T : HTable ι) (a0 : LW ι) : Bool :=
  parB T fun m => o m.1 a0 && cylB o B m.2

theorem b2_coeffB (s : ι → Δ) {o : LW ι → LW ι → Bool} {S : List (LW ι)}
    (ho : ∀ a ∈ S, ∀ b ∈ S, o a b = true ↔ wordValue (lampGen s) a = wordValue (lampGen s) b)
    (B : List (LW ι)) (hB : ∀ v ∈ B, dW v ∈ S) (T : HTable ι) (a0 : LW ι) (ha0 : a0 ∈ S)
    (hT : ∀ m ∈ T, m.1 ∈ S ∧ ∀ p ∈ m.2, dW p ∈ S ∧ ∀ q ∈ lampPrefixes p, liftD q ∈ S) :
    b2 (coeffB o B T a0) = hCoeffLC s (wordValue (lampGen s) a0) T (xB s B) := by
  classical
  rw [coeffB, b2_parB, hCoeffLC_apply]
  congr 1
  refine List.map_congr_left fun m hm => ?_
  show b2 (o m.1 a0 && cylB o B m.2) =
    if wordValue (lampGen s) m.1 = wordValue (lampGen s) a0 then hCyl s m.2 (xB s B) else 0
  rw [b2_and, b2_cylB s ho B hB m.2 (hT m hm).2]
  by_cases h : wordValue (lampGen s) m.1 = wordValue (lampGen s) a0
  · rw [if_pos h, (ho _ (hT m hm).1 _ ha0).2 h, b2_true, one_mul]
  · rw [if_neg h, Bool.eq_false_iff.2 fun e => h ((ho _ (hT m hm).1 _ ha0).1 e), b2_false, zero_mul]

/-! ### Finitely many variables -/

theorem hCyl_agree (s : ι → Δ) (P : List (LW ι)) (x y : LampSpace Δ)
    (h : ∀ p ∈ P, hAtom s p x = hAtom s p y) : hCyl s P x = hCyl s P y := by
  rw [hCyl_apply, hCyl_apply]
  congr 1
  exact List.map_congr_left h

theorem hCoeffLC_agree (s : ι → Δ) (η : LampAffine Δ) (T : HTable ι) (x y : LampSpace Δ)
    (h : ∀ m ∈ T, hCyl s m.2 x = hCyl s m.2 y) : hCoeffLC s η T x = hCoeffLC s η T y := by
  classical
  rw [hCoeffLC_apply, hCoeffLC_apply]
  congr 1
  refine List.map_congr_left fun m hm => ?_
  show (if wordValue (lampGen s) m.1 = η then hCyl s m.2 x else 0) =
    if wordValue (lampGen s) m.1 = η then hCyl s m.2 y else 0
  rw [h m hm]

theorem xB_filter (s : ι → Δ) (U : List (LW ι)) (x : LampSpace Δ) (p : LW ι) (hp : p ∈ U) :
    xB s (U.filter fun v => decide (x (wordValue s (deltaWord v)) = 1)) (wordValue s (deltaWord p)) =
      x (wordValue s (deltaWord p)) := by
  refine (xB_eq_b2 s _ _ (decide (x (wordValue s (deltaWord p)) = 1)) ?_).trans (b2_decide_eq_one _)
  rw [decide_eq_true_eq]
  constructor
  · intro h1
    exact ⟨p, List.mem_filter.2 ⟨hp, decide_eq_true h1⟩, rfl⟩
  · rintro ⟨v, hv, hvp⟩
    rw [← hvp]
    exact of_decide_eq_true (List.mem_filter.1 hv).2

/-! ### Tables and matrices -/

/-- The atoms of a table. -/
def tabU (T : HTable ι) : List (LW ι) :=
  T.flatMap fun m => m.2

/-- The words of a table whose equalities in `Λ` are asked. -/
def tabW (T : HTable ι) : List (LW ι) :=
  T.map (fun m => m.1) ++ (tabU T).map dW ++ (tabU T).flatMap fun p => (lampPrefixes p).map liftD

/-- Whether every coefficient of `T` vanishes at every `xB B`, `B` a subset of the atoms. -/
def tabOk (o : LW ι → LW ι → Bool) (T : HTable ι) : Bool :=
  allB (subsets (tabU T)) fun B => allB T fun m0 => !coeffB o B T m0.1

/-- **A table vanishes iff it passes the check** (tex l.661–664). -/
theorem tabOk_iff (s : ι → Δ) {o : LW ι → LW ι → Bool} {S : List (LW ι)} (T : HTable ι)
    (hS : ∀ a ∈ tabW T, a ∈ S)
    (ho : ∀ a ∈ S, ∀ b ∈ S, o a b = true ↔ wordValue (lampGen s) a = wordValue (lampGen s) b) :
    tabOk o T = true ↔ hTabEval s T = 0 := by
  have hU : ∀ p ∈ tabU T, dW p ∈ S ∧ ∀ q ∈ lampPrefixes p, liftD q ∈ S := fun p hp =>
    ⟨hS _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hp))),
      fun q hq => hS _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨p, hp, List.mem_map_of_mem hq⟩))⟩
  have hT : ∀ m ∈ T, m.1 ∈ S ∧ ∀ p ∈ m.2, dW p ∈ S ∧ ∀ q ∈ lampPrefixes p, liftD q ∈ S := fun m hm =>
    ⟨hS _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hm))),
      fun p hp => hU p (List.mem_flatMap.2 ⟨m, hm, hp⟩)⟩
  have key : ∀ B ∈ subsets (tabU T), ∀ m0 ∈ T,
      b2 (coeffB o B T m0.1) = hCoeffLC s (wordValue (lampGen s) m0.1) T (xB s B) := fun B hB m0 hm0 =>
    b2_coeffB s ho B (fun v hv => (hU v (mem_subsets_sub _ B hB v hv)).1) T m0.1 (hT m0 hm0).1 hT
  rw [tabOk, allB_eq_true, hTabEval_eq_zero_iff]
  constructor
  · intro h m0 hm0 x
    have hB := filter_mem_subsets (fun v => decide (x (wordValue s (deltaWord v)) = 1)) (tabU T)
    have hc := (allB_eq_true _ _).1 (h _ hB) m0 hm0
    have hval := key _ hB m0 hm0
    rw [(not_eq_true_iff_b2 _).1 hc] at hval
    rw [hCoeffLC_agree s _ T x
      (xB s ((tabU T).filter fun v => decide (x (wordValue s (deltaWord v)) = 1))) ?_]
    · exact hval.symm
    · intro m hm
      refine hCyl_agree s m.2 _ _ fun p hp => ?_
      have hpU : p ∈ tabU T := List.mem_flatMap.2 ⟨m, hm, hp⟩
      rw [hAtom_apply, hAtom_apply, xB_filter s (tabU T) x p hpU]
  · intro h B hB
    refine (allB_eq_true _ _).2 fun m0 hm0 => ?_
    have hval := key B hB m0 hm0
    rw [h m0 hm0 (xB s B)] at hval
    exact (not_eq_true_iff_b2 _).2 hval

/-- The nine tables `M i j + I₃ i j`. -/
def matTabs (M : HMat ι) : List (HTable ι) :=
  (List.finRange 3).flatMap fun i => (List.finRange 3).map fun j => M i j ++ hMatOne i j

/-- Whether every table of a list passes. -/
def matOk (o : LW ι → LW ι → Bool) (Ts : List (HTable ι)) : Bool :=
  allB Ts (tabOk o)

/-- The words of a list of tables. -/
def matW (Ts : List (HTable ι)) : List (LW ι) :=
  Ts.flatMap tabW

theorem matOk_iff (s : ι → Δ) {o : LW ι → LW ι → Bool} {S : List (LW ι)} (M : HMat ι)
    (hS : ∀ a ∈ matW (matTabs M), a ∈ S)
    (ho : ∀ a ∈ S, ∀ b ∈ S, o a b = true ↔ wordValue (lampGen s) a = wordValue (lampGen s) b) :
    matOk o (matTabs M) = true ↔ ∀ i j : Fin 3, hTabEval s (M i j ++ hMatOne i j) = 0 := by
  have hmem : ∀ i j : Fin 3, M i j ++ hMatOne i j ∈ matTabs M := fun i j =>
    List.mem_flatMap.2 ⟨i, List.mem_finRange i,
      List.mem_map_of_mem (f := fun j => M i j ++ hMatOne i j) (List.mem_finRange j)⟩
  have hok : ∀ T ∈ matTabs M, (tabOk o T = true ↔ hTabEval s T = 0) := fun T hT =>
    tabOk_iff s T (fun a ha => hS a (List.mem_flatMap.2 ⟨T, hT, ha⟩)) ho
  rw [matOk, allB_eq_true]
  constructor
  · intro h i j
    exact (hok _ (hmem i j)).1 (h _ (hmem i j))
  · intro h T hT
    obtain ⟨i, _, hT'⟩ := List.mem_flatMap.1 hT
    obtain ⟨j, _, hj⟩ := List.mem_map.1 hT'
    rw [← hj]
    rw [← hj] at hT
    exact (hok _ hT).2 (h i j)

/-- **A word in the units `v` is trivial iff its table matrix passes the check** (tex l.657–664), for answers `o`
that decide equality in `Λ` on the words asked. -/
theorem wordValue_eq_one_iff_matOk (s : ι → Δ) {κ : Type} (v : κ → (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ)
    (L : κ × Bool → HMat ι)
    (hL : ∀ x : κ × Bool, hMatEval s (L x) =
      ((if x.2 then v x.1 else (v x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ)))
    (w : List (κ × Bool)) {o : LW ι → LW ι → Bool} {S : List (LW ι)}
    (hS : ∀ a ∈ matW (matTabs (hWordMat L w)), a ∈ S)
    (ho : ∀ a ∈ S, ∀ b ∈ S, o a b = true ↔ wordValue (lampGen s) a = wordValue (lampGen s) b) :
    wordValue v w = 1 ↔ matOk o (matTabs (hWordMat L w)) = true := by
  rw [wordValue_eq_one_iff_hTab s v L hL w, matOk_iff s _ hS ho]

end HalflineB
end SimpleKazhdanSofic
end Manuscript
end GroupApproximation

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.tabOk_iff
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.wordValue_eq_one_iff_matOk
