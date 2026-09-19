import GroupApproximation.Higman.TowerCert
import GroupApproximation.Higman.BlockComputable
import GroupApproximation.Higman.RelatorSearch

/-!
# The tower certificate checker is computable

`Higman.TowerCert` reduces tower membership to one unbounded search,
`towerDeriv_iff_exists_certCheck`.  This file proves the matrix computable and
closes (B2)'s per-code half, then merges the per-block searches exactly as
`Higman.BlockSearch`/`Higman.BlockComputable` did for (B1), which closes (B2).

Every ingredient was verified against the pin:

* `rawPow` is `List.flatten ∘ List.replicate`, and `List.replicate n v` is
  `(List.range n).map (fun _ ↦ v)` by `List.map_const'`, so it is
  `Primrec.list_range`, `Primrec.list_map`, `Primrec.list_flatten`.
* `invRaw` is the repository's own `Computability.RawWord.invWord`, reproved
  here from `Primrec.list_reverse` and `Primrec.dom_bool` rather than imported,
  so that this file depends only on `Higman`.
* the two quantifiers of `EntryOk` are `PrimrecRel.forall_mem_list` and
  `PrimrecRel.exists_mem_list`, which is exactly why the certificate format
  names claims by value; see `Higman.TowerCert`.
* the innermost test is `WordProblemRE.primrec_searchCheck`.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.PresentationCodes
open GroupApproximation.AdianRabinWordProblem
open GroupApproximation.WordProblemRE

/-! ## 1.  Powers and inverses of raw words -/

theorem rawPow_eq (v : RawWord) (n : ℕ) :
    rawPow v n = (List.replicate n v).flatten := by
  induction n with
  | zero => simp [rawPow]
  | succ n ih =>
      show v ++ rawPow v n = _
      rw [ih, List.replicate_succ, List.flatten_cons]

theorem primrec_rawPow : Primrec₂ fun (v : RawWord) (n : ℕ) ↦ rawPow v n := by
  have h : Primrec fun x : RawWord × ℕ ↦
      ((List.range x.2).map fun _ ↦ x.1).flatten :=
    Primrec.list_flatten.comp
      (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst).to₂)
  refine h.of_eq fun x ↦ ?_
  change ((List.range x.2).map fun _ ↦ x.1).flatten = rawPow x.1 x.2
  rw [rawPow_eq, List.map_const', List.length_range]

theorem primrec_conjWord :
    Primrec fun l : List (RawWord × RawWord × ℕ) ↦ conjWord l := by
  have hinner : Primrec₂ fun (_ : List (RawWord × RawWord × ℕ))
      (p : RawWord × RawWord × ℕ) ↦ p.1 ++ p.2.1 ++ invRaw p.1 :=
    (Primrec.list_append.comp
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (primrec_invRaw.comp (Primrec.fst.comp Primrec.snd))).to₂
  exact Primrec.list_flatten.comp (Primrec.list_map Primrec.id hinner)

/-! ## 2.  The entry check -/

local instance entryPrimcodable : Primcodable Entry := inferInstance

set_option maxSynthPendingDepth 1000 in
theorem primrecRel_entryOk :
    PrimrecRel fun (e : Entry) (y : PresentationCode × List Entry) ↦
      EntryOk y.1 y.2 e := by
  -- innermost: a candidate earlier entry matches an item
  have hmatch : PrimrecRel fun (e' : Entry)
      (z : (RawWord × RawWord × ℕ) × Entry × (PresentationCode × List Entry)) ↦
        e'.1 + 1 = z.2.1.1 ∧ e'.2.1 = rawPow z.1.2.1 z.1.2.2 := by
    refine PrimrecPred.and ?_ ?_
    · exact Primrec.eq.comp
        (Primrec.succ.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
    · refine Primrec.eq.comp
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) ?_
      exact primrec_rawPow.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have hex : PrimrecRel fun (L : List Entry)
      (z : (RawWord × RawWord × ℕ) × Entry × (PresentationCode × List Entry)) ↦
        ∃ e' ∈ L, e'.1 + 1 = z.2.1.1 ∧ e'.2.1 = rawPow z.1.2.1 z.1.2.2 :=
    PrimrecRel.exists_mem_list hmatch
  -- one item is justified
  have hitem : PrimrecRel fun (it : RawWord × RawWord × ℕ)
      (x : Entry × (PresentationCode × List Entry)) ↦
        0 < it.2.2 ∧ ∃ e' ∈ x.2.2, e'.1 + 1 = x.1.1 ∧
          e'.2.1 = rawPow it.2.1 it.2.2 := by
    refine PrimrecPred.and ?_ ?_
    · exact Primrec.nat_lt.comp (Primrec.const 0)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    · exact PrimrecRel.comp hex
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.pair Primrec.fst Primrec.snd)
  -- all items are justified
  have hall : PrimrecRel fun (l : List (RawWord × RawWord × ℕ))
      (x : Entry × (PresentationCode × List Entry)) ↦
        ∀ it ∈ l, 0 < it.2.2 ∧ ∃ e' ∈ x.2.2, e'.1 + 1 = x.1.1 ∧
          e'.2.1 = rawPow it.2.1 it.2.2 :=
    PrimrecRel.forall_mem_list hitem
  refine PrimrecPred.and ?_ ?_
  · exact PrimrecRel.comp hall
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.id
  · refine Primrec.eq.comp ?_ (Primrec.const true)
    refine primrec_searchCheck.comp ?_
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    refine Primrec.pair (Primrec.fst.comp Primrec.snd) ?_
    exact Primrec.list_append.comp
      (primrec_conjWord.comp
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (primrec_invRaw.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))

theorem primrecPred_certOk :
    PrimrecPred fun y : PresentationCode × List Entry ↦ CertOk y.1 y.2 := by
  unfold CertOk
  exact PrimrecRel.comp (PrimrecRel.forall_mem_list primrecRel_entryOk)
    Primrec.snd Primrec.id

/-! ## 3.  The search matrix -/

theorem primrec_certCheck :
    Primrec fun x : (PresentationCode × RawWord) × List Entry ↦
      certCheck x.1.1 x.1.2 x.2 := by
  have hclaim : PrimrecPred fun x : (PresentationCode × RawWord) × List Entry ↦
      ∃ e ∈ x.2, e.2.1 = x.1.2 := by
    refine PrimrecRel.comp
      (PrimrecRel.exists_mem_list
        (R := fun (e : Entry) (x : (PresentationCode × RawWord) × List Entry) ↦
          e.2.1 = x.1.2)
        (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      Primrec.snd Primrec.id
  have hcert : PrimrecPred fun x : (PresentationCode × RawWord) × List Entry ↦
      CertOk x.1.1 x.2 :=
    PrimrecPred.comp primrecPred_certOk
      (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
  haveI : DecidablePred fun x : (PresentationCode × RawWord) × List Entry ↦
      (CertOk x.1.1 x.2 ∧ ∃ e ∈ x.2, e.2.1 = x.1.2) := fun _ ↦ inferInstance
  exact (PrimrecPred.and hcert hclaim).decide.of_eq fun x ↦ by
    unfold certCheck
    exact decide_eq_decide.mpr Iff.rfl

/-! ## 4.  (B2), per code -/

theorem rePred_towerDeriv :
    REPred fun x : PresentationCode × RawWord ↦
      ∃ i : ℕ, TowerDeriv (codedGen x.1) i x.2 :=
  (rePred_exists_eq_true (g := fun (x : PresentationCode × RawWord)
      (L : List Entry) ↦ certCheck x.1 x.2 L)
    primrec_certCheck.to_comp).of_eq fun x ↦
      (towerDeriv_iff_exists_certCheck x.1 x.2).symm

end Higman
end GroupApproximation
