import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.FreePresentation
import GroupApproximation.Meta.AxiomGuard

/-!
# Commutator words in `KMGroup X`

The word `word X u i j` stands for the Steinberg generator `x_{ij}(u)` of the monomial `u`.  Using
only the four relator families of `KMGroup X`, this module proves that words obey the Steinberg
relations for monomials:

* `word_commute_gen`, `word_commute_word`: words at non-addable index pairs commute;
* `gen_none_word`: `⁅x_{ij}(1), x_{jk}(u)⁆ = x_{ik}(u)`;
* `word_cons_eq`: the spare index in the definition of `word` may be replaced by any other index;
* `word_append`: `⁅x_{ij}(u), x_{jk}(v)⁆ = x_{ik}(u v)`.

The first four statements are proved together by induction on the word, see `word_package`.
Every step picks a spare index; five indices always leave one index outside four given ones.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open scoped commutatorElement

noncomputable section

variable (X : Type*)

/-- Generators commute with words at non-addable index pairs. -/
def Cgw (v : List X) : Prop :=
  ∀ (i j k l : Fin 5) (s : Option X), i ≠ j → k ≠ l → j ≠ k → i ≠ l →
    Commute (gen X i j s) (word X v k l)

/-- Words commute with words at non-addable index pairs. -/
def Cww (u v : List X) : Prop :=
  ∀ i j k l : Fin 5, i ≠ j → k ≠ l → j ≠ k → i ≠ l → Commute (word X u i j) (word X v k l)

/-- The adjacent relation with unit left entry, for a word. -/
def A0 (v : List X) : Prop :=
  ∀ i j k : Fin 5, i ≠ j → j ≠ k → i ≠ k → ⁅gen X i j none, word X v j k⁆ = word X v i k

/-- Independence of the intermediate index for a word with a first letter. -/
def Ins (w : List X) : Prop :=
  ∀ (a : X) (i j m : Fin 5), i ≠ j → m ≠ i → m ≠ j →
    word X (a :: w) i j = ⁅gen X i m (some a), word X w m j⁆

theorem ins_of (w : List X) (hC : Cgw X w) (hA : A0 X w) (hW : Cww X w w) : Ins X w := by
  have claim : ∀ (a : X) (i j m l : Fin 5), i ≠ j → m ≠ i → m ≠ j → l ≠ i → l ≠ j → m ≠ l →
      ⁅gen X i m (some a), word X w m j⁆ = ⁅gen X i l (some a), word X w l j⁆ := by
    intro a i j m l hij hmi hmj hli hlj hml
    have e : word X w m j = ⁅gen X m l none, word X w l j⁆ := (hA m l j hml hlj hmj).symm
    have hr : ⁅gen X i m (some a), gen X m l none⁆ = gen X i l (some a) :=
      gen_adj_some X i m l a (Ne.symm hmi) hml (Ne.symm hli)
    have hxc : Commute (gen X i m (some a)) (word X w l j) :=
      hC i m l j (some a) (Ne.symm hmi) hlj hml hij
    have hde : Commute (gen X i l (some a)) (word X w m j) :=
      hC i l m j (some a) (Ne.symm hli) hmj (Ne.symm hml) hij
    have heh : Commute (word X w m j) ⁅gen X i l (some a), word X w l j⁆ :=
      commute_commutatorElement_right hde.symm (hW m j l j hmj hlj (Ne.symm hlj) hmj)
    rw [e, comm_assoc (gen X i m (some a)) (gen X m l none) (word X w l j) hxc
      (by rw [hr, ← e]; exact hde) (by rw [hr, ← e]; exact heh), hr]
  intro a i j m hij hmi hmj
  rw [word_cons]
  by_cases hm : m = spare i j
  · subst hm
    rfl
  · exact (claim a i j m (spare i j) hij hmi hmj (spare_ne_left i j) (spare_ne_right i j) hm).symm

theorem cgw_cons (b : X) (v : List X) (hC : Cgw X v) (hI : Ins X v) : Cgw X (b :: v) := by
  intro i j k l s hij hkl hjk hil
  obtain ⟨p, hpi, hpj, hpk, hpl⟩ :=
    KervaireSteinberg.fin_exists_spare_index (n := 5) le_rfl i j k l
  rw [hI b k l p hkl hpk hpl]
  exact commute_commutatorElement_right
    (gen_commute X i j k p s (some b) hij (Ne.symm hpk) hjk (Ne.symm hpi))
    (hC i j p l s hij hpl (Ne.symm hpj) hil)

theorem cww_cons (a : X) (u v : List X) (hI : Ins X u) (hW : Cww X u v) (hv : Cgw X v) :
    Cww X (a :: u) v := by
  intro i j k l hij hkl hjk hil
  obtain ⟨p, hpi, hpj, hpk, hpl⟩ :=
    KervaireSteinberg.fin_exists_spare_index (n := 5) le_rfl i j k l
  rw [hI a i j p hij hpi hpj]
  exact commute_commutatorElement_left (hv i p k l (some a) (Ne.symm hpi) hkl hpk hil)
    (hW p j k l hpj hkl hjk hpl)

theorem a0_cons (b : X) (w : List X) (hC : Cgw X w) (hI : Ins X w) (hC' : Cgw X (b :: w))
    (hW' : Cww X (b :: w) (b :: w)) : A0 X (b :: w) := by
  intro i j k hij hjk hik
  obtain ⟨l, hli, hlj, hlk, -⟩ :=
    KervaireSteinberg.fin_exists_spare_index (n := 5) le_rfl i j k k
  have e1 : word X (b :: w) j k = ⁅gen X j l (some b), word X w l k⁆ := hI b j k l hjk hlj hlk
  have e2 : word X (b :: w) i k = ⁅gen X i l (some b), word X w l k⁆ := hI b i k l hik hli hlk
  have hr : ⁅gen X i j none, gen X j l (some b)⁆ = gen X i l (some b) :=
    gen_adj_none X i j l (some b) hij (Ne.symm hlj) (Ne.symm hli)
  have hxc : Commute (gen X i j none) (word X w l k) := hC i j l k none hij hlk (Ne.symm hlj) hik
  have hde : Commute (gen X i l (some b)) (word X (b :: w) j k) :=
    hC' i l j k (some b) (Ne.symm hli) hjk hlj hik
  have heh : Commute (word X (b :: w) j k) (word X (b :: w) i k) :=
    hW' j k i k hjk hik (Ne.symm hik) hjk
  rw [e1, e2, comm_assoc (gen X i j none) (gen X j l (some b)) (word X w l k) hxc
    (by rw [hr, ← e1]; exact hde) (by rw [hr, ← e1, ← e2]; exact heh), hr]

/-- The four word statements, by induction on the word. -/
theorem word_package (u : List X) :
    Cgw X u ∧ (∀ v, Cgw X v → Cww X u v) ∧ A0 X u ∧ Ins X u := by
  induction u with
  | nil =>
      have hC : Cgw X [] := by
        intro i j k l s hij hkl hjk hil
        rw [word_nil]
        exact gen_commute X i j k l s none hij hkl hjk hil
      have hW : ∀ v, Cgw X v → Cww X [] v := by
        intro v hv i j k l hij hkl hjk hil
        rw [word_nil]
        exact hv i j k l none hij hkl hjk hil
      have hA : A0 X [] := by
        intro i j k hij hjk hik
        rw [word_nil, word_nil]
        exact gen_adj_none X i j k none hij hjk hik
      exact ⟨hC, hW, hA, ins_of X [] hC hA (hW [] hC)⟩
  | cons b w ih =>
      obtain ⟨hC, hW, -, hI⟩ := ih
      have hC' : Cgw X (b :: w) := cgw_cons X b w hC hI
      have hW' : ∀ v, Cgw X v → Cww X (b :: w) v := fun v hv =>
        cww_cons X b w v hI (hW v hv) hv
      have hA' : A0 X (b :: w) := a0_cons X b w hC hI hC' (hW' (b :: w) hC')
      exact ⟨hC', hW', hA', ins_of X (b :: w) hC' hA' (hW' (b :: w) hC')⟩

theorem word_commute_gen (v : List X) (i j k l : Fin 5) (s : Option X) (hij : i ≠ j)
    (hkl : k ≠ l) (hjk : j ≠ k) (hil : i ≠ l) : Commute (gen X i j s) (word X v k l) :=
  (word_package X v).1 i j k l s hij hkl hjk hil

theorem word_commute_word (u v : List X) (i j k l : Fin 5) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) : Commute (word X u i j) (word X v k l) :=
  (word_package X u).2.1 v (word_package X v).1 i j k l hij hkl hjk hil

theorem gen_none_word (v : List X) (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅gen X i j none, word X v j k⁆ = word X v i k :=
  (word_package X v).2.2.1 i j k hij hjk hik

theorem word_cons_eq (a : X) (w : List X) (i j m : Fin 5) (hij : i ≠ j) (hmi : m ≠ i)
    (hmj : m ≠ j) : word X (a :: w) i j = ⁅gen X i m (some a), word X w m j⁆ :=
  (word_package X w).2.2.2 a i j m hij hmi hmj

/-- `⁅x_{ij}(u), x_{jk}(v)⁆ = x_{ik}(u v)` for words. -/
theorem word_append (u v : List X) (i j k : Fin 5) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅word X u i j, word X v j k⁆ = word X (u ++ v) i k := by
  induction u generalizing i j k with
  | nil =>
      rw [word_nil, List.nil_append]
      exact gen_none_word X v i j k hij hjk hik
  | cons a u ih =>
      rw [List.cons_append]
      obtain ⟨l, hli, hlj, hlk, -⟩ :=
        KervaireSteinberg.fin_exists_spare_index (n := 5) le_rfl i j k k
      have e1 : word X (a :: u) i j = ⁅gen X i l (some a), word X u l j⁆ :=
        word_cons_eq X a u i j l hij hli hlj
      have e2 : word X (a :: (u ++ v)) i k = ⁅gen X i l (some a), word X (u ++ v) l k⁆ :=
        word_cons_eq X a (u ++ v) i k l hik hli hlk
      have hbc : ⁅word X u l j, word X v j k⁆ = word X (u ++ v) l k := ih l j k hlj hjk hlk
      have hxc : Commute (gen X i l (some a)) (word X v j k) :=
        word_commute_gen X v i l j k (some a) (Ne.symm hli) hjk hlj hik
      have hde : Commute (word X (a :: u) i j) (word X (u ++ v) l k) :=
        word_commute_word X (a :: u) (u ++ v) i j l k hij hlk (Ne.symm hlj) hik
      have heh : Commute (word X (u ++ v) l k) ⁅word X (a :: u) i j, word X v j k⁆ :=
        commute_commutatorElement_right
          (word_commute_word X (u ++ v) (a :: u) l k i j hlk hij (Ne.symm hik) hlj)
          (word_commute_word X (u ++ v) v l k j k hlk hjk (Ne.symm hjk) hlk)
      have key : ⁅gen X i l (some a), ⁅word X u l j, word X v j k⁆⁆ =
          ⁅⁅gen X i l (some a), word X u l j⁆, word X v j k⁆ :=
        comm_assoc (gen X i l (some a)) (word X u l j) (word X v j k) hxc
          (by rw [← e1, hbc]; exact hde) (by rw [← e1, hbc]; exact heh)
      rw [hbc, ← e2, ← e1] at key
      exact key.symm

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Cgw
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Cww
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.A0
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Ins
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.ins_of
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.cgw_cons
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.cww_cons
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.a0_cons
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.word_package
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.word_commute_gen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.word_commute_word
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.gen_none_word
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.word_cons_eq
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.word_append
