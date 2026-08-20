import GroupApproximation.Higman.TowerDerivation
import GroupApproximation.Higman.BlockWordProblem

/-!
# Derivations for Chiodo's tower

`Higman.TowerDerivation` puts tower membership in the form `∃ i, TowerDeriv gen
i v`, a recursion on raw words whose only atomic conditions are triviality
tests.  To make that recursively enumerable it has to become **one** existential
over a `Primcodable` type with a decidable matrix.  This file supplies the
certificate.

## The format, and why it is this one

An entry is `(i, v, l, sd)`: the claim is that `v` is derivable at stage `i`;
`l` is the list of (conjugator, base, exponent) triples; `sd` certifies the one
word-problem instance `conjWord l ++ invRaw v`.  An entry is *valid against a
list* `L` when every item of `l` has positive exponent and names a claim of `L`
at stage exactly one lower, and the word-problem certificate checks out.

Three choices make the proofs short.

* **Reference by value, not by position.**  An item names an entry of `L`
  satisfying `e'.1 + 1 = e.1`, so the check is `∀ item ∈ l, ∃ e' ∈ L, …`.  That
  is the bounded-quantifier shape `PrimrecRel.forall_mem_list` and
  `PrimrecRel.exists_mem_list` make primitive recursive, and it is why no index
  arithmetic appears anywhere below.
* **Reference the whole list, not a prefix.**  Sound because the stage drops by
  exactly one at every reference, so soundness is plain induction on the stage;
  and it makes validity *monotone* in `L`, which is what lets certificates be
  concatenated (`CertOk.append`) in the completeness proof.
* **No case split on the stage.**  Stage `0` needs no special rule: an entry
  with no items certifies `conjWord [] ++ invRaw v`, i.e. that `v` is trivial,
  and the condition `e'.1 + 1 = e.1` makes a nonempty item list *force* the
  stage to be positive on its own.

## Result

`towerDeriv_iff_exists_cert`: `(∃ i, TowerDeriv (codedGen c) i v)` holds exactly
when some certificate is valid and claims `v`.  What remains for (B2) is that
`CertOk` and the claim test are computable --- the same `Primrec` plumbing as
`Higman.BlockComputable`, over the same three lemmas.
-/

namespace GroupApproximation
namespace Higman

open GroupApproximation.PresentationCodes
open GroupApproximation.AdianRabinWordProblem
open GroupApproximation.WordProblemRE

/-- The generators of a coded group, indexed by `ℕ`. -/
def codedGen (c : PresentationCode) : ℕ → Carrier c :=
  fun k ↦ PresentedGroup.of (letterOf c k)

theorem evalRaw_codedGen_eq_one_iff (c : PresentationCode) (u : RawWord) :
    evalRaw (codedGen c) u = 1 ↔ WordProblem c u :=
  evalRaw_letterOf_eq_one_iff c u

/-! ## 1.  Entries and validity -/

/-- One line of a derivation: a stage, the word claimed at it, the conjugation
data, and a certificate for the single word-problem instance. -/
abbrev Entry : Type := ℕ × RawWord × List (RawWord × RawWord × ℕ) × SearchData

/-- An entry is valid against `L`. -/
def EntryOk (c : PresentationCode) (L : List Entry) (e : Entry) : Prop :=
  (∀ it ∈ e.2.2.1, 0 < it.2.2 ∧
      ∃ e' ∈ L, e'.1 + 1 = e.1 ∧ e'.2.1 = rawPow it.2.1 it.2.2) ∧
    searchCheck (c, conjWord e.2.2.1 ++ invRaw e.2.1) e.2.2.2 = true

/-- A certificate is valid when all its entries are. -/
def CertOk (c : PresentationCode) (L : List Entry) : Prop :=
  ∀ e ∈ L, EntryOk c L e

instance entryOk_decidable (c : PresentationCode) (L : List Entry) (e : Entry) :
    Decidable (EntryOk c L e) := by
  unfold EntryOk
  infer_instance

instance certOk_decidable (c : PresentationCode) (L : List Entry) :
    Decidable (CertOk c L) := by
  unfold CertOk
  infer_instance

/-! ## 2.  Validity is monotone, so certificates concatenate -/

theorem EntryOk.mono {c : PresentationCode} {L L' : List Entry} {e : Entry}
    (h : EntryOk c L e) (hsub : ∀ x ∈ L, x ∈ L') : EntryOk c L' e := by
  refine ⟨?_, h.2⟩
  intro it hit
  obtain ⟨hn, e', he', h1, h2⟩ := h.1 it hit
  exact ⟨hn, e', hsub e' he', h1, h2⟩

theorem CertOk.append {c : PresentationCode} {L₁ L₂ : List Entry}
    (h₁ : CertOk c L₁) (h₂ : CertOk c L₂) : CertOk c (L₁ ++ L₂) := by
  intro e he
  rcases List.mem_append.1 he with h | h
  · exact (h₁ e h).mono fun x hx => List.mem_append.2 (Or.inl hx)
  · exact (h₂ e h).mono fun x hx => List.mem_append.2 (Or.inr hx)

theorem CertOk.flatten {c : PresentationCode} :
    ∀ Ls : List (List Entry), (∀ L ∈ Ls, CertOk c L) → CertOk c Ls.flatten := by
  intro Ls
  induction Ls with
  | nil => intro _ e he; simp at he
  | cons L Ls ih =>
      intro h
      exact CertOk.append (h L (by simp))
        (ih fun M hM => h M (List.mem_cons_of_mem _ hM))

/-! ## 3.  Soundness -/

theorem certOk_sound (c : PresentationCode) {L : List Entry} (h : CertOk c L) :
    ∀ (j : ℕ) (e : Entry), e ∈ L → e.1 = j →
      TowerDeriv (codedGen c) j e.2.1 := by
  intro j
  induction j with
  | zero =>
      intro e he hj
      obtain ⟨hitems, hsd⟩ := h e he
      have hword : evalRaw (codedGen c) (conjWord e.2.2.1 ++ invRaw e.2.1) = 1 :=
        (evalRaw_codedGen_eq_one_iff c _).2
          ((wordProblemPred_iff_exists _).2 ⟨_, hsd⟩)
      have hnil : e.2.2.1 = [] := by
        by_contra hne
        obtain ⟨it, hit⟩ := List.exists_mem_of_ne_nil _ hne
        obtain ⟨-, e', -, h1, -⟩ := hitems it hit
        rw [hj] at h1
        exact Nat.succ_ne_zero _ h1
      rw [hnil] at hword
      rw [towerDeriv_zero]
      have h2 : (evalRaw (codedGen c) e.2.1)⁻¹ = 1 := by
        simpa [conjWord] using hword
      simpa using h2
  | succ i ih =>
      intro e he hj
      obtain ⟨hitems, hsd⟩ := h e he
      have hword : evalRaw (codedGen c) (conjWord e.2.2.1 ++ invRaw e.2.1) = 1 :=
        (evalRaw_codedGen_eq_one_iff c _).2
          ((wordProblemPred_iff_exists _).2 ⟨_, hsd⟩)
      rw [towerDeriv_succ_iff_triv]
      refine ⟨e.2.2.1, ?_, hword⟩
      intro p hp
      obtain ⟨hn, e', he', h1, h2⟩ := hitems p hp
      refine ⟨hn, ?_⟩
      have hstage : e'.1 = i := by omega
      have hd := ih e' he' hstage
      rwa [h2] at hd

/-! ## 4.  Completeness -/

theorem exists_cert_of_towerDeriv (c : PresentationCode) :
    ∀ (i : ℕ) (v : RawWord), TowerDeriv (codedGen c) i v →
      ∃ L : List Entry, CertOk c L ∧ ∃ e ∈ L, e.1 = i ∧ e.2.1 = v := by
  intro i
  induction i with
  | zero =>
      intro v hv
      rw [towerDeriv_zero] at hv
      have hword : evalRaw (codedGen c) (conjWord [] ++ invRaw v) = 1 := by
        simp [conjWord, hv]
      obtain ⟨sd, hsd⟩ :=
        (wordProblemPred_iff_exists (c, conjWord [] ++ invRaw v)).1
          ((evalRaw_codedGen_eq_one_iff c _).1 hword)
      refine ⟨[(0, v, [], sd)], ?_, ⟨(0, v, [], sd), by simp, rfl, rfl⟩⟩
      intro e he
      rw [List.mem_singleton] at he
      subst he
      exact ⟨by simp, hsd⟩
  | succ i ih =>
      intro v hv
      rw [towerDeriv_succ_iff_triv] at hv
      obtain ⟨l, hl, hword⟩ := hv
      obtain ⟨m, hm1, hm2⟩ :=
        list_choice
          (fun (p : RawWord × RawWord × ℕ) (L : List Entry) ↦
            CertOk c L ∧ ∃ e ∈ L, e.1 = i ∧ e.2.1 = rawPow p.2.1 p.2.2)
          l (fun p hp => ih _ (hl p hp).2)
      obtain ⟨sd, hsd⟩ :=
        (wordProblemPred_iff_exists (c, conjWord l ++ invRaw v)).1
          ((evalRaw_codedGen_eq_one_iff c _).1 hword)
      refine ⟨(m.map Prod.snd).flatten ++ [(i + 1, v, l, sd)], ?_, ?_⟩
      · refine CertOk.append (CertOk.flatten _ ?_) ?_
        · intro L hL
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hL
          exact (hm2 q hq).1
        · intro e he
          rw [List.mem_singleton] at he
          subst he
          refine ⟨?_, hsd⟩
          intro it hit
          have hit' : it ∈ m.map Prod.fst := by rw [hm1]; exact hit
          obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hit'
          obtain ⟨-, e', he', he'1, he'2⟩ := hm2 q hq
          rw [hqe] at he'2
          refine ⟨(hl it hit).1, e', ?_, by omega, he'2⟩
          exact List.mem_append.2 (Or.inl
            (List.mem_flatten.2 ⟨q.2, List.mem_map.2 ⟨q, hq, rfl⟩, he'⟩))
      · exact ⟨(i + 1, v, l, sd), by simp, rfl, rfl⟩

/-! ## 5.  Tower membership is one search over certificates -/

/-- **Derivability is exactly the existence of a certificate.** -/
theorem towerDeriv_iff_exists_cert (c : PresentationCode) (v : RawWord) :
    (∃ i : ℕ, TowerDeriv (codedGen c) i v) ↔
      ∃ L : List Entry, CertOk c L ∧ ∃ e ∈ L, e.2.1 = v := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨L, hL, e, he, -, hev⟩ := exists_cert_of_towerDeriv c i v hi
    exact ⟨L, hL, e, he, hev⟩
  · rintro ⟨L, hL, e, he, hev⟩
    refine ⟨e.1, ?_⟩
    rw [← hev]
    exact certOk_sound c hL e.1 e he rfl

/-- The matrix of the search, as a `Bool`. -/
def certCheck (c : PresentationCode) (v : RawWord) (L : List Entry) : Bool :=
  decide (CertOk c L ∧ ∃ e ∈ L, e.2.1 = v)

theorem certCheck_eq_true_iff (c : PresentationCode) (v : RawWord)
    (L : List Entry) :
    certCheck c v L = true ↔ (CertOk c L ∧ ∃ e ∈ L, e.2.1 = v) :=
  decide_eq_true_iff

/-- **Tower membership is one unbounded search with a decidable matrix.** -/
theorem towerDeriv_iff_exists_certCheck (c : PresentationCode) (v : RawWord) :
    (∃ i : ℕ, TowerDeriv (codedGen c) i v) ↔
      ∃ L : List Entry, certCheck c v L = true := by
  rw [towerDeriv_iff_exists_cert]
  exact exists_congr fun L => (certCheck_eq_true_iff c v L).symm

end Higman
end GroupApproximation
