import GroupApproximation.Manuscript.NonMFNotes.Full.Kharlampovich.KMSPresentation
import GroupApproximation.Computability.PresentationCodes
import Mathlib.Computability.Primrec.List

/-!
# Raw coded words for the Kharlampovich operations

Input for `thm:fixed-radical-membership` of `non_mf_group_notes.tex`, in the
form of the coding step for the Kharlampovich group `KMS.KhGroup M`.

A coded word is a list of signed letter indices (`PresentationCodes.wordOf`).
We define the operations `u⁻¹`, `u^g`, `[u, v]` and `f * a` of KMS Sec. 4.1
directly on coded words, show that `wordOf` turns them into `khConj`,
`khComm` and `khStar`, and show that they are primitive recursive.
-/

namespace GroupApproximation.Full.Kharlampovich

namespace KMS

open PresentationCodes

/-- The inverse of a coded word. -/
def rawInv (L : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (L.map fun q ↦ (q.1, !q.2)).reverse

/-- The coded conjugate `u^g = g⁻¹ u g`. -/
def rawConj (U G : List (ℕ × Bool)) : List (ℕ × Bool) :=
  rawInv G ++ U ++ G

/-- The coded commutator `[u, v] = u⁻¹ v⁻¹ u v`. -/
def rawComm (U V : List (ℕ × Bool)) : List (ℕ × Bool) :=
  rawInv U ++ rawInv V ++ U ++ V

/-- The coded operation `f * a = f⁻¹ f^{a} (f^{a⁻¹})⁻¹ f^{(a')⁻¹}`. -/
def rawStar (F A A' : List (ℕ × Bool)) : List (ℕ × Bool) :=
  rawInv F ++ rawConj F A ++ rawInv (rawConj F (rawInv A)) ++ rawConj F (rawInv A')

/-! ## Reading raw words in the free group -/

theorem wordOf_append (c : PresentationCode) (L₁ L₂ : List (ℕ × Bool)) :
    wordOf c (L₁ ++ L₂) = wordOf c L₁ * wordOf c L₂ := by
  simp only [wordOf, List.map_append, FreeGroup.mul_mk]

theorem wordOf_rawInv (c : PresentationCode) (L : List (ℕ × Bool)) :
    wordOf c (rawInv L) = (wordOf c L)⁻¹ := by
  induction L with
  | nil => rfl
  | cons q L ih =>
    have h1 : rawInv (q :: L) = rawInv L ++ [(q.1, !q.2)] := by
      simp only [rawInv, List.map_cons, List.reverse_cons]
    have h2 : wordOf c [(q.1, !q.2)] = (wordOf c [q])⁻¹ := rfl
    have h3 : wordOf c (q :: L) = wordOf c [q] * wordOf c L := rfl
    rw [h1, wordOf_append, ih, h2, h3, mul_inv_rev]

theorem wordOf_rawConj (c : PresentationCode) (U G : List (ℕ × Bool)) :
    wordOf c (rawConj U G) = khConj (wordOf c U) (wordOf c G) := by
  simp only [rawConj, khConj, wordOf_append, wordOf_rawInv]

theorem wordOf_rawComm (c : PresentationCode) (U V : List (ℕ × Bool)) :
    wordOf c (rawComm U V) = khComm (wordOf c U) (wordOf c V) := by
  simp only [rawComm, khComm, wordOf_append, wordOf_rawInv]

theorem wordOf_rawStar (c : PresentationCode) (F A A' : List (ℕ × Bool)) :
    wordOf c (rawStar F A A') = khStar (wordOf c F) (wordOf c A) (wordOf c A') := by
  simp only [rawStar, khStar, wordOf_append, wordOf_rawInv, wordOf_rawConj]

/-! ## Primitive recursiveness -/

theorem primrec_rawInv : Primrec rawInv := by
  have hflip : Primrec₂ fun (_ : List (ℕ × Bool)) (q : ℕ × Bool) ↦ (q.1, !q.2) :=
    Primrec₂.mk ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.not.comp (Primrec.snd.comp Primrec.snd)))
  have hmap : Primrec fun L : List (ℕ × Bool) ↦ L.map fun q ↦ (q.1, !q.2) :=
    Primrec.list_map Primrec.id hflip
  exact Primrec.list_reverse.comp hmap

theorem primrec_rawConj : Primrec₂ rawConj :=
  Primrec.list_append.comp
    (Primrec.list_append.comp (primrec_rawInv.comp Primrec.snd) Primrec.fst) Primrec.snd

theorem primrec_rawComm : Primrec₂ rawComm :=
  Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp (primrec_rawInv.comp Primrec.fst)
        (primrec_rawInv.comp Primrec.snd)) Primrec.fst) Primrec.snd

theorem primrec_rawStar {α : Type*} [Primcodable α] {F A A' : α → List (ℕ × Bool)}
    (hF : Primrec F) (hA : Primrec A) (hA' : Primrec A') :
    Primrec fun a ↦ rawStar (F a) (A a) (A' a) :=
  Primrec.list_append.comp
    (Primrec.list_append.comp
      (Primrec.list_append.comp (primrec_rawInv.comp hF) (primrec_rawConj.comp hF hA))
      (primrec_rawInv.comp (primrec_rawConj.comp hF (primrec_rawInv.comp hA))))
    (primrec_rawConj.comp hF (primrec_rawInv.comp hA'))

end KMS

end GroupApproximation.Full.Kharlampovich
