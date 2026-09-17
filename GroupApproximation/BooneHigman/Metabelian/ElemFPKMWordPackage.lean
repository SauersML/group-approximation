import GroupApproximation.BooneHigman.Metabelian.ElemFPKMWords
import GroupApproximation.Meta.AxiomGuard

/-!
# Commutator words in `KMGroup X d`: the Steinberg relations for monomials

Rank-`d + 5` generalisation of the second half of
`GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.WordCalculus`.  Using only the four
relator families of `KMGroup X d`, words obey the Steinberg relations for monomials:

* `word_commute_gen`, `word_commute_word`: words at non-addable index pairs commute;
* `gen_none_word`: `⁅x_{ij}(1), x_{jk}(u)⁆ = x_{ik}(u)`;
* `word_cons_eq`: the spare index in the definition of `word` may be replaced by any other index;
* `word_append`: `⁅x_{ij}(u), x_{jk}(v)⁆ = x_{ik}(u v)`.

The first four statements are proved together by induction on the word, see `word_package`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP
  (comm_assoc commute_commutatorElement_right)

noncomputable section

variable (X : Type*) (d : ℕ)

/-- The four word statements, by induction on the word. -/
theorem word_package (u : List X) :
    Cgw X d u ∧ (∀ v, Cgw X d v → Cww X d u v) ∧ A0 X d u ∧ Ins X d u := by
  induction u with
  | nil =>
      have hC : Cgw X d [] := by
        intro i j k l s hij hkl hjk hil
        rw [word_nil]
        exact gen_commute X d i j k l s none hij hkl hjk hil
      have hW : ∀ v, Cgw X d v → Cww X d [] v := by
        intro v hv i j k l hij hkl hjk hil
        rw [word_nil]
        exact hv i j k l none hij hkl hjk hil
      have hA : A0 X d [] := by
        intro i j k hij hjk hik
        rw [word_nil, word_nil]
        exact gen_adj_none X d i j k none hij hjk hik
      exact ⟨hC, hW, hA, ins_of X d [] hC hA (hW [] hC)⟩
  | cons b w ih =>
      obtain ⟨hC, hW, -, hI⟩ := ih
      have hC' : Cgw X d (b :: w) := cgw_cons X d b w hC hI
      have hW' : ∀ v, Cgw X d v → Cww X d (b :: w) v := fun v hv =>
        cww_cons X d b w v hI (hW v hv) hv
      have hA' : A0 X d (b :: w) := a0_cons X d b w hC hI hC' (hW' (b :: w) hC')
      exact ⟨hC', hW', hA', ins_of X d (b :: w) hC' hA' (hW' (b :: w) hC')⟩

theorem word_commute_gen (v : List X) (i j k l : Fin (d + 5)) (s : Option X) (hij : i ≠ j)
    (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) : Commute (gen X d i j s) (word X d v k l) :=
  (word_package X d v).1 i j k l s hij hkl hjk hil

theorem word_commute_word (u v : List X) (i j k l : Fin (d + 5)) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) : Commute (word X d u i j) (word X d v k l) :=
  (word_package X d u).2.1 v (word_package X d v).1 i j k l hij hkl hjk hil

theorem gen_none_word (v : List X) (i j k : Fin (d + 5)) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) : ⁅gen X d i j none, word X d v j k⁆ = word X d v i k :=
  (word_package X d v).2.2.1 i j k hij hjk hik

theorem word_cons_eq (a : X) (w : List X) (i j m : Fin (d + 5)) (hij : i ≠ j) (hmi : m ≠ i)
    (hmj : m ≠ j) : word X d (a :: w) i j = ⁅gen X d i m (some a), word X d w m j⁆ :=
  (word_package X d w).2.2.2 a i j m hij hmi hmj

/-- `⁅x_{ij}(u), x_{jk}(v)⁆ = x_{ik}(u v)` for words. -/
theorem word_append (u v : List X) (i j k : Fin (d + 5)) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) : ⁅word X d u i j, word X d v j k⁆ = word X d (u ++ v) i k := by
  induction u generalizing i j k with
  | nil =>
      rw [word_nil, List.nil_append]
      exact gen_none_word X d v i j k hij hjk hik
  | cons a u ih =>
      rw [List.cons_append]
      obtain ⟨l, hli, hlj, hlk, -⟩ :=
        KervaireSteinberg.fin_exists_spare_index (n := d + 5) (Nat.le_add_left 5 d) i j k k
      have e1 : word X d (a :: u) i j = ⁅gen X d i l (some a), word X d u l j⁆ :=
        word_cons_eq X d a u i j l hij hli hlj
      have e2 : word X d (a :: (u ++ v)) i k =
          ⁅gen X d i l (some a), word X d (u ++ v) l k⁆ :=
        word_cons_eq X d a (u ++ v) i k l hik hli hlk
      have hbc : ⁅word X d u l j, word X d v j k⁆ = word X d (u ++ v) l k :=
        ih l j k hlj hjk hlk
      have hxc : Commute (gen X d i l (some a)) (word X d v j k) :=
        word_commute_gen X d v i l j k (some a) (Ne.symm hli) hjk hlj hik
      have hde : Commute (word X d (a :: u) i j) (word X d (u ++ v) l k) :=
        word_commute_word X d (a :: u) (u ++ v) i j l k hij hlk (Ne.symm hlj) hik
      have heh : Commute (word X d (u ++ v) l k) ⁅word X d (a :: u) i j, word X d v j k⁆ :=
        commute_commutatorElement_right
          (word_commute_word X d (u ++ v) (a :: u) l k i j hlk hij (Ne.symm hik) hlj)
          (word_commute_word X d (u ++ v) v l k j k hlk hjk (Ne.symm hjk) hlk)
      have key : ⁅gen X d i l (some a), ⁅word X d u l j, word X d v j k⁆⁆ =
          ⁅⁅gen X d i l (some a), word X d u l j⁆, word X d v j k⁆ :=
        comm_assoc (gen X d i l (some a)) (word X d u l j) (word X d v j k) hxc
          (by rw [← e1, hbc]; exact hde) (by rw [← e1, hbc]; exact heh)
      rw [hbc, ← e2, ← e1] at key
      exact key.symm

end

end GroupApproximation.BooneHigman.Metabelian.ElemFP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.word_package
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.word_commute_gen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.word_commute_word
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.gen_none_word
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.word_cons_eq
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.word_append
