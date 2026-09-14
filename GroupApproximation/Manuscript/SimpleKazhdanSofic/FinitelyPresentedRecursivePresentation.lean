import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFHostInstances
import GroupApproximation.Manuscript.SimpleKazhdanSofic.LEFRecursivePresentationClasses
import GroupApproximation.Computability.EnumeratedPresentationCodes
import GroupApproximation.Higman.RecursivePresentationBridge
import GroupApproximation.Meta.AxiomGuard

/-!
# Finitely presented groups are recursively presented

`simple_kazhdan_sofic_group.tex` at origin/main 8b36733d7, `cor:host` (tex l.310–313):

> So one such group contains every recursively presented finitely generated LEF group, for instance
> every finitely presented residually finite group [...]

The instance needs a finitely presented group to be recursively presented, in the form
`Higman.RecursivePresentation`. Let `φ : F(n) → Γ` be onto with kernel the normal closure of a
finite set `S`. On the countable alphabet send `x_k` to `φ(x_k)` for `k < n` and to `1` for `k ≥ n`.
The evaluation map is `φ ∘ π`, where `π : F(ℕ) → F(n)` kills the letters `k ≥ n`. Its kernel is the
normal closure of `ι(S)` and the letters `x_k` with `k ≥ n`, where `ι` is the inclusion, a section of
`π`. These relators are the values of a primitive recursive family, so the word problem is
recursively enumerable (`Higman.rePred_wordProblem_of_relators`).

* `truncateLetters n : FreeGroup ℕ →* FreeGroup (Fin n)`: the retraction `π`.
* `finiteRelator n L`: the words of `L`, then the letters `x_k` with `k ≥ n`; primitive recursive.
* `rangeRelatorCheck r`: a certificate that a raw word is `r i` or its formal inverse, as in
  `EnumeratedPresentationCodes.relatorCheck`. It is primitive recursive, and
  `freeEval_mem_symmetrize_range_iff` is its semantics.
* `finitelyPresentedRecursivePresentationStatement : FinitelyPresentedRecursivePresentationStatement`.
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic

open Higman

noncomputable section

/-! ## The retraction killing the letters `k ≥ n` -/

/-- The retraction `F(ℕ) → F(n)` fixing `x_k` for `k < n` and killing `x_k` for `k ≥ n`. -/
def truncateLetters (n : ℕ) : FreeGroup ℕ →* FreeGroup (Fin n) :=
  FreeGroup.lift fun k => if h : k < n then FreeGroup.of ⟨k, h⟩ else 1

theorem truncateLetters_of_lt {n k : ℕ} (hk : k < n) :
    truncateLetters n (FreeGroup.of k) = FreeGroup.of ⟨k, hk⟩ := by
  simp [truncateLetters, hk]

theorem truncateLetters_of_not_lt {n k : ℕ} (hk : ¬k < n) :
    truncateLetters n (FreeGroup.of k) = 1 := by
  simp [truncateLetters, hk]

theorem truncateLetters_map_val (n : ℕ) (x : FreeGroup (Fin n)) :
    truncateLetters n (FreeGroup.map (fun i : Fin n => (i : ℕ)) x) = x := by
  have h : (truncateLetters n).comp (FreeGroup.map fun i : Fin n => (i : ℕ)) = MonoidHom.id _ := by
    ext i
    simp [truncateLetters_of_lt i.isLt]
  exact DFunLike.congr_fun h x

theorem truncateLetters_surjective (n : ℕ) : Function.Surjective (truncateLetters n) :=
  fun x => ⟨FreeGroup.map (fun i : Fin n => (i : ℕ)) x, truncateLetters_map_val n x⟩

theorem freeEval_singleton (k : ℕ) : freeEval [(k, true)] = FreeGroup.of k := by
  simp [freeEval]

/-! ## The relator family -/

/-- The relators on `ℕ`: the words of `L`, then the letters `x_k` with `k ≥ n`. -/
def finiteRelator (n : ℕ) (L : List RawWord) (i : ℕ) : RawWord :=
  if i < L.length then L.getD i [] else [(i - L.length + n, true)]

theorem primrec_finiteRelator (n : ℕ) (L : List RawWord) : Primrec (finiteRelator n L) :=
  (Primrec.ite (Primrec.nat_lt.comp Primrec.id (Primrec.const L.length))
    ((Primrec.list_getD []).comp (Primrec.const L) Primrec.id)
    (Primrec.list_cons.comp
      (Primrec.pair
        (Primrec.nat_add.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const L.length))
          (Primrec.const n))
        (Primrec.const true))
      (Primrec.const []))).of_eq fun _ => rfl

/-! ## The certificate -/

/-- A certificate that a raw word is the relator `r i` or its formal inverse. The witness is
`(i, (sign, reduction steps))`, as in `EnumeratedPresentationCodes.relatorCheck`. -/
def rangeRelatorCheck (r : ℕ → RawWord) (v : RawWord) (witness : ℕ) : Bool :=
  let outer := Nat.unpair witness
  let inner := Nat.unpair outer.2
  let target := if inner.1 = 0 then r outer.1 else invRaw (r outer.1)
  decide (Computability.applySteps (v ++ invRaw target)
    (EnumeratedPresentationCodes.decodeSteps inner.2) = some [])

theorem primrec_rangeRelatorCheck {r : ℕ → RawWord} (hr : Primrec r) :
    Primrec fun z : RawWord × ℕ => rangeRelatorCheck r z.1 z.2 := by
  have hv : Primrec fun z : RawWord × ℕ => z.1 := Primrec.fst
  have ho : Primrec fun z : RawWord × ℕ => Nat.unpair z.2 := Primrec.unpair.comp Primrec.snd
  have hi : Primrec fun z : RawWord × ℕ => Nat.unpair (Nat.unpair z.2).2 :=
    Primrec.unpair.comp (Primrec.snd.comp ho)
  have haddress : Primrec fun z : RawWord × ℕ => (Nat.unpair z.2).1 := Primrec.fst.comp ho
  have hsign : Primrec fun z : RawWord × ℕ => (Nat.unpair (Nat.unpair z.2).2).1 :=
    Primrec.fst.comp hi
  have hsteps : Primrec fun z : RawWord × ℕ =>
      EnumeratedPresentationCodes.decodeSteps (Nat.unpair (Nat.unpair z.2).2).2 :=
    EnumeratedPresentationCodes.primrec_decodeSteps.comp (Primrec.snd.comp hi)
  have hrel : Primrec fun z : RawWord × ℕ => r (Nat.unpair z.2).1 := hr.comp haddress
  have htarget : Primrec fun z : RawWord × ℕ =>
      if (Nat.unpair (Nat.unpair z.2).2).1 = 0 then r (Nat.unpair z.2).1
      else invRaw (r (Nat.unpair z.2).1) :=
    Primrec.ite (Primrec.eq.comp hsign (Primrec.const 0)) hrel (primrec_invRaw.comp hrel)
  have hword : Primrec fun z : RawWord × ℕ =>
      z.1 ++ invRaw (if (Nat.unpair (Nat.unpair z.2).2).1 = 0 then r (Nat.unpair z.2).1
        else invRaw (r (Nat.unpair z.2).1)) :=
    Primrec.list_append.comp hv (primrec_invRaw.comp htarget)
  exact (Primrec.eq.comp (Computability.primrec_applySteps.comp hword hsteps)
    (Primrec.const (some []))).decide.of_eq fun _ => by
      simp only [rangeRelatorCheck]

/-- Exact certificate semantics for membership in the symmetrized range of `r`. -/
theorem freeEval_mem_symmetrize_range_iff (r : ℕ → RawWord) (v : RawWord) :
    freeEval v ∈ symmetrize (Set.range fun i => freeEval (r i)) ↔
      ∃ witness, rangeRelatorCheck r v witness = true := by
  constructor
  · rintro (hv | ⟨x, hx, hxv⟩)
    · obtain ⟨address, haddress⟩ := hv
      obtain ⟨steps, hsteps⟩ := (freeEval_eq_one_iff (v ++ invRaw (r address))).1 (by
          change evalRaw FreeGroup.of (r address) = evalRaw FreeGroup.of v at haddress
          change evalRaw FreeGroup.of (v ++ invRaw (r address)) = 1
          rw [evalRaw_append, evalRaw_invRaw, ← haddress, mul_inv_cancel])
      refine ⟨Nat.pair address (Nat.pair 0 (Encodable.encode steps)), ?_⟩
      simp [rangeRelatorCheck, EnumeratedPresentationCodes.decodeSteps, hsteps]
    · obtain ⟨address, rfl⟩ := hx
      obtain ⟨steps, hsteps⟩ := (freeEval_eq_one_iff
        (v ++ invRaw (invRaw (r address)))).1 (by
          change (evalRaw FreeGroup.of (r address))⁻¹ = evalRaw FreeGroup.of v at hxv
          change evalRaw FreeGroup.of (v ++ invRaw (invRaw (r address))) = 1
          rw [evalRaw_append, evalRaw_invRaw, evalRaw_invRaw]
          rw [← hxv]
          simp)
      refine ⟨Nat.pair address (Nat.pair 1 (Encodable.encode steps)), ?_⟩
      simp [rangeRelatorCheck, EnumeratedPresentationCodes.decodeSteps, hsteps]
  · rintro ⟨witness, hw⟩
    simp only [rangeRelatorCheck, decide_eq_true_eq] at hw
    let outer := Nat.unpair witness
    let inner := Nat.unpair outer.2
    let target := if inner.1 = 0 then r outer.1 else invRaw (r outer.1)
    have hone : freeEval (v ++ invRaw target) = 1 :=
      (freeEval_eq_one_iff _).2 ⟨EnumeratedPresentationCodes.decodeSteps inner.2, hw⟩
    have heq : freeEval v = freeEval target := by
      change evalRaw FreeGroup.of v = evalRaw FreeGroup.of target
      apply mul_inv_eq_one.mp
      change evalRaw FreeGroup.of (v ++ invRaw target) = 1 at hone
      simpa only [evalRaw_append, evalRaw_invRaw] using hone
    by_cases hsign : inner.1 = 0
    · exact Or.inl ⟨outer.1, by simpa [target, hsign] using heq.symm⟩
    · apply Or.inr
      refine ⟨freeEval (r outer.1), ⟨outer.1, rfl⟩, ?_⟩
      calc
        (freeEval (r outer.1))⁻¹ = freeEval (invRaw (r outer.1)) := by
              exact (evalRaw_invRaw FreeGroup.of _).symm
        _ = freeEval v := by simpa [target, hsign] using heq.symm

/-! ## Finitely presented groups are recursively presented -/

/-- **Finitely presented groups are recursively presented.** -/
theorem finitelyPresentedRecursivePresentationStatement :
    FinitelyPresentedRecursivePresentationStatement := by
  intro Γ _ hfp
  obtain ⟨n, φ, hsurj, S, hSfin, hS⟩ := hfp.out
  obtain ⟨L, hLS, hSL⟩ : ∃ L : List RawWord,
      (∀ w ∈ L, ∃ s ∈ S, freeEval w = FreeGroup.map (fun i : Fin n => (i : ℕ)) s) ∧
        ∀ s ∈ S, FreeGroup.toWord (FreeGroup.map (fun i : Fin n => (i : ℕ)) s) ∈ L := by
    refine ⟨hSfin.toFinset.toList.map fun s =>
      FreeGroup.toWord (FreeGroup.map (fun i : Fin n => (i : ℕ)) s), fun w hw => ?_, fun s hs => ?_⟩
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hw
      exact ⟨s, by simpa using hs, freeEval_toWord _⟩
    · exact List.mem_map_of_mem (by simpa using hs)
  obtain ⟨gen, hlift⟩ : ∃ gen : ℕ → Γ, FreeGroup.lift gen = φ.comp (truncateLetters n) :=
    ⟨fun k => φ (truncateLetters n (FreeGroup.of k)), by ext k; simp⟩
  -- the relators: `ι(S)` and the letters `x_k` with `k ≥ n`
  have hofT : ∀ k, n ≤ k → FreeGroup.of k ∈ Set.range fun i => freeEval (finiteRelator n L i) := by
    intro k hk
    refine ⟨k - n + L.length, ?_⟩
    have h1 : ¬k - n + L.length < L.length := by omega
    have h2 : k - n + L.length - L.length + n = k := by omega
    show freeEval (finiteRelator n L (k - n + L.length)) = FreeGroup.of k
    rw [finiteRelator, if_neg h1, h2, freeEval_singleton]
  have hιT : ∀ s ∈ S, FreeGroup.map (fun i : Fin n => (i : ℕ)) s ∈
      Set.range fun i => freeEval (finiteRelator n L i) := by
    intro s hs
    obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem (hSL s hs)
    refine ⟨i, ?_⟩
    show freeEval (finiteRelator n L i) = _
    rw [finiteRelator, if_pos hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some, hiw, freeEval_toWord]
  -- the kernel of the evaluation map is the normal closure of the relators
  have hTker : (Set.range fun i => freeEval (finiteRelator n L i)) ⊆ (FreeGroup.lift gen).ker := by
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show FreeGroup.lift gen (freeEval (finiteRelator n L i)) = 1
    rw [hlift, MonoidHom.comp_apply]
    by_cases hi : i < L.length
    · obtain ⟨s, hs, hsw⟩ := hLS _ (List.mem_iff_getElem.2 ⟨i, hi, rfl⟩)
      rw [finiteRelator, if_pos hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
        Option.getD_some, hsw, truncateLetters_map_val, ← MonoidHom.mem_ker, ← hS]
      exact Subgroup.subset_normalClosure hs
    · have hk : ¬i - L.length + n < n := by omega
      rw [finiteRelator, if_neg hi, freeEval_singleton, truncateLetters_of_not_lt hk, map_one]
  have hle : (FreeGroup.lift gen).ker ≤
      Subgroup.normalClosure (Set.range fun i => freeEval (finiteRelator n L i)) := by
    intro x hx
    have hq : (QuotientGroup.mk'
          (Subgroup.normalClosure (Set.range fun i => freeEval (finiteRelator n L i)))).comp
        ((FreeGroup.map fun i : Fin n => (i : ℕ)).comp (truncateLetters n)) =
        QuotientGroup.mk'
          (Subgroup.normalClosure (Set.range fun i => freeEval (finiteRelator n L i))) := by
      ext k
      by_cases hk : k < n
      · have h1 : FreeGroup.map (fun i : Fin n => (i : ℕ)) (truncateLetters n (FreeGroup.of k)) =
            FreeGroup.of k := by
          simp [truncateLetters_of_lt hk]
        simp only [MonoidHom.comp_apply, h1]
      · have h1 : FreeGroup.map (fun i : Fin n => (i : ℕ)) (truncateLetters n (FreeGroup.of k)) =
            1 := by
          rw [truncateLetters_of_not_lt hk, map_one]
        simp only [MonoidHom.comp_apply, h1, map_one]
        rw [eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.subset_normalClosure (hofT k (not_lt.1 hk))
    rw [MonoidHom.mem_ker, hlift, MonoidHom.comp_apply] at hx
    have hxS : truncateLetters n x ∈ Subgroup.normalClosure S := by
      rw [hS, MonoidHom.mem_ker]
      exact hx
    have hSle : Subgroup.normalClosure S ≤
        (Subgroup.normalClosure (Set.range fun i => freeEval (finiteRelator n L i))).comap
          (FreeGroup.map fun i : Fin n => (i : ℕ)) :=
      Subgroup.normalClosure_le_normal fun s hs => Subgroup.subset_normalClosure (hιT s hs)
    have h1 : ((FreeGroup.map (fun i : Fin n => (i : ℕ)) (truncateLetters n x) : FreeGroup ℕ) :
          FreeGroup ℕ ⧸
            Subgroup.normalClosure (Set.range fun i => freeEval (finiteRelator n L i))) =
        (x : FreeGroup ℕ ⧸
          Subgroup.normalClosure (Set.range fun i => freeEval (finiteRelator n L i))) :=
      DFunLike.congr_fun hq x
    rw [← QuotientGroup.eq_one_iff, ← h1, QuotientGroup.eq_one_iff]
    exact hSle hxS
  have hker : (FreeGroup.lift gen).ker =
      Subgroup.normalClosure (Set.range fun i => freeEval (finiteRelator n L i)) :=
    le_antisymm hle (Subgroup.normalClosure_le_normal hTker)
  have hpres : ∀ w : RawWord, evalRaw gen w = 1 ↔
      freeEval w ∈ Subgroup.normalClosure (Set.range fun i => freeEval (finiteRelator n L i)) := by
    intro w
    rw [← hker, MonoidHom.mem_ker, Higman.lift_freeEval]
  have hspans : Subgroup.closure (Set.range gen) = ⊤ := by
    rw [← Higman.range_lift gen, MonoidHom.range_eq_top, hlift]
    exact hsurj.comp (truncateLetters_surjective n)
  exact ⟨{ gen := gen
           spans := hspans
           re := rePred_wordProblem_of_relators (rangeRelatorCheck (finiteRelator n L)) gen _ hpres
             (primrec_rangeRelatorCheck (primrec_finiteRelator n L)).to₂
             (freeEval_mem_symmetrize_range_iff (finiteRelator n L)) }⟩

end

end SimpleKazhdanSofic
end GroupApproximation

#audit_axioms GroupApproximation.SimpleKazhdanSofic.truncateLetters_map_val
#audit_axioms GroupApproximation.SimpleKazhdanSofic.primrec_finiteRelator
#audit_axioms GroupApproximation.SimpleKazhdanSofic.primrec_rangeRelatorCheck
#audit_axioms GroupApproximation.SimpleKazhdanSofic.freeEval_mem_symmetrize_range_iff
#audit_closed_axioms GroupApproximation.SimpleKazhdanSofic.finitelyPresentedRecursivePresentationStatement
