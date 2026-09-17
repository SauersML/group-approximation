import GroupApproximation.BooneHigman.Metabelian.ElemFPKMGroup
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.CommutatorCalculus
import GroupApproximation.Meta.AxiomGuard

/-!
# Commutator words in `KMGroup X d`: the inductive steps

Rank-`d + 5` generalisation of the first half of
`GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.WordCalculus`.  The word
`word X d u i j` stands for the Steinberg generator `x_{ij}(u)` of the monomial `u`.  This module
defines the four word statements `Cgw`, `Cww`, `A0`, `Ins` and proves the inductive steps
`ins_of`, `cgw_cons`, `cww_cons`, `a0_cons`.  The induction itself is in
`ElemFPKMWordPackage`.  Every step picks a spare index; at least five indices always leave one
index outside four given ones (`KervaireSteinberg.fin_exists_spare_index` with `5 ≤ d + 5`).
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement
open GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP
  (comm_assoc commute_commutatorElement_right commute_commutatorElement_left)

noncomputable section

variable (X : Type*) (d : ℕ)

/-- Generators commute with words at non-addable index pairs. -/
def Cgw (v : List X) : Prop :=
  ∀ (i j k l : Fin (d + 5)) (s : Option X), i ≠ j → k ≠ l → j ≠ k → i ≠ l →
    Commute (gen X d i j s) (word X d v k l)

/-- Words commute with words at non-addable index pairs. -/
def Cww (u v : List X) : Prop :=
  ∀ i j k l : Fin (d + 5), i ≠ j → k ≠ l → j ≠ k → i ≠ l →
    Commute (word X d u i j) (word X d v k l)

/-- The adjacent relation with unit left entry, for a word. -/
def A0 (v : List X) : Prop :=
  ∀ i j k : Fin (d + 5), i ≠ j → j ≠ k → i ≠ k →
    ⁅gen X d i j none, word X d v j k⁆ = word X d v i k

/-- Independence of the intermediate index for a word with a first letter. -/
def Ins (w : List X) : Prop :=
  ∀ (a : X) (i j m : Fin (d + 5)), i ≠ j → m ≠ i → m ≠ j →
    word X d (a :: w) i j = ⁅gen X d i m (some a), word X d w m j⁆

theorem ins_of (w : List X) (hC : Cgw X d w) (hA : A0 X d w) (hW : Cww X d w w) :
    Ins X d w := by
  have claim : ∀ (a : X) (i j m l : Fin (d + 5)), i ≠ j → m ≠ i → m ≠ j → l ≠ i → l ≠ j →
      m ≠ l →
      ⁅gen X d i m (some a), word X d w m j⁆ = ⁅gen X d i l (some a), word X d w l j⁆ := by
    intro a i j m l hij hmi hmj hli hlj hml
    have e : word X d w m j = ⁅gen X d m l none, word X d w l j⁆ :=
      (hA m l j hml hlj hmj).symm
    have hr : ⁅gen X d i m (some a), gen X d m l none⁆ = gen X d i l (some a) :=
      gen_adj_some X d i m l a (Ne.symm hmi) hml (Ne.symm hli)
    have hxc : Commute (gen X d i m (some a)) (word X d w l j) :=
      hC i m l j (some a) (Ne.symm hmi) hlj hml hij
    have hde : Commute (gen X d i l (some a)) (word X d w m j) :=
      hC i l m j (some a) (Ne.symm hli) hmj (Ne.symm hml) hij
    have heh : Commute (word X d w m j) ⁅gen X d i l (some a), word X d w l j⁆ :=
      commute_commutatorElement_right hde.symm (hW m j l j hmj hlj (Ne.symm hlj) hmj)
    rw [e, comm_assoc (gen X d i m (some a)) (gen X d m l none) (word X d w l j) hxc
      (by rw [hr, ← e]; exact hde) (by rw [hr, ← e]; exact heh), hr]
  intro a i j m hij hmi hmj
  rw [word_cons]
  by_cases hm : m = spare i j
  · subst hm
    rfl
  · exact (claim a i j m (spare i j) hij hmi hmj (spare_ne_left i j) (spare_ne_right i j)
      hm).symm

theorem cgw_cons (b : X) (v : List X) (hC : Cgw X d v) (hI : Ins X d v) :
    Cgw X d (b :: v) := by
  intro i j k l s hij hkl hjk hil
  obtain ⟨p, hpi, hpj, hpk, hpl⟩ :=
    KervaireSteinberg.fin_exists_spare_index (n := d + 5) (Nat.le_add_left 5 d) i j k l
  rw [hI b k l p hkl hpk hpl]
  exact commute_commutatorElement_right
    (gen_commute X d i j k p s (some b) hij (Ne.symm hpk) hjk (Ne.symm hpi))
    (hC i j p l s hij hpl (Ne.symm hpj) hil)

theorem cww_cons (a : X) (u v : List X) (hI : Ins X d u) (hW : Cww X d u v)
    (hv : Cgw X d v) : Cww X d (a :: u) v := by
  intro i j k l hij hkl hjk hil
  obtain ⟨p, hpi, hpj, hpk, hpl⟩ :=
    KervaireSteinberg.fin_exists_spare_index (n := d + 5) (Nat.le_add_left 5 d) i j k l
  rw [hI a i j p hij hpi hpj]
  exact commute_commutatorElement_left (hv i p k l (some a) (Ne.symm hpi) hkl hpk hil)
    (hW p j k l hpj hkl hjk hpl)

theorem a0_cons (b : X) (w : List X) (hC : Cgw X d w) (hI : Ins X d w)
    (hC' : Cgw X d (b :: w)) (hW' : Cww X d (b :: w) (b :: w)) : A0 X d (b :: w) := by
  intro i j k hij hjk hik
  obtain ⟨l, hli, hlj, hlk, -⟩ :=
    KervaireSteinberg.fin_exists_spare_index (n := d + 5) (Nat.le_add_left 5 d) i j k k
  have e1 : word X d (b :: w) j k = ⁅gen X d j l (some b), word X d w l k⁆ :=
    hI b j k l hjk hlj hlk
  have e2 : word X d (b :: w) i k = ⁅gen X d i l (some b), word X d w l k⁆ :=
    hI b i k l hik hli hlk
  have hr : ⁅gen X d i j none, gen X d j l (some b)⁆ = gen X d i l (some b) :=
    gen_adj_none X d i j l (some b) hij (Ne.symm hlj) (Ne.symm hli)
  have hxc : Commute (gen X d i j none) (word X d w l k) :=
    hC i j l k none hij hlk (Ne.symm hlj) hik
  have hde : Commute (gen X d i l (some b)) (word X d (b :: w) j k) :=
    hC' i l j k (some b) (Ne.symm hli) hjk hlj hik
  have heh : Commute (word X d (b :: w) j k) (word X d (b :: w) i k) :=
    hW' j k i k hjk hik (Ne.symm hik) hjk
  rw [e1, e2, comm_assoc (gen X d i j none) (gen X d j l (some b)) (word X d w l k) hxc
    (by rw [hr, ← e1]; exact hde) (by rw [hr, ← e1, ← e2]; exact heh), hr]

end

end GroupApproximation.BooneHigman.Metabelian.ElemFP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.Cgw
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.Cww
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.A0
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.Ins
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.ins_of
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cgw_cons
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.cww_cons
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.a0_cons
