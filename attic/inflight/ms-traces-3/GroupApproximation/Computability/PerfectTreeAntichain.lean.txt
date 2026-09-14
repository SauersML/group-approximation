import GroupApproximation.Computability.FiniteExtensionStep
import Mathlib.SetTheory.Cardinal.Continuum
import GroupApproximation.Meta.AxiomGuard

/-!
# A continuum antichain of Turing degrees

For corollary `cor:wp` of `simple_kazhdan_sofic_group.tex`: "The Turing degrees contain an antichain
of size continuum [Odifreddi, Chapter V]".

A perfect tree of strings is built stage by stage.
* Stage `s + 1` starts from the strings of stage `s`, copied to both children.
* It then applies the finite-extension step `exists_diag` to every requirement `(ρ, ρ', e)`, where
  `ρ ≠ ρ'` have length `s + 1` and `e ≤ s`.  The requirement says: program number `e`, with any
  oracle extending the string at `ρ'`, computes no set extending the string at `ρ`.
* Extensions only lengthen strings, so requirements persist.

Each path `f` gives the set `branchSet f`, which extends its strings.  Distinct paths give Turing
incomparable sets, and the paths indexed by `Set ℕ` give continuum many.

* `stage`, `stage_prefix_succ`, `stage_diag`;
* `extends_branchSet`, `not_turingReducible_branchSet`;
* `exists_turing_antichain_continuum`.
-/

namespace GroupApproximation
namespace OracleUse

open Classical

instance : Nonempty OCode := ⟨.zero⟩

/-- An enumeration of oracle programs. -/
noncomputable def codeEnum : ℕ → OCode :=
  Classical.choose (exists_surjective_nat OCode)

theorem codeEnum_surjective : Function.Surjective codeEnum :=
  Classical.choose_spec (exists_surjective_nat OCode)

/-- A pair of strings extending `σ` and `τ` that satisfies the requirement for `c`. -/
noncomputable def diagPair (c : OCode) (σ τ : List Bool) : List Bool × List Bool :=
  (Classical.choose (exists_diag c σ τ),
    Classical.choose (Classical.choose_spec (exists_diag c σ τ)))

theorem diagPair_spec (c : OCode) (σ τ : List Bool) :
    σ <+: (diagPair c σ τ).1 ∧ τ <+: (diagPair c σ τ).2 ∧
      Diag c (diagPair c σ τ).1 (diagPair c σ τ).2 :=
  Classical.choose_spec (Classical.choose_spec (exists_diag c σ τ))

/-- A requirement: two nodes and a program number. -/
abbrev Req : Type := List Bool × List Bool × ℕ

/-- Apply the finite-extension step to one requirement. -/
noncomputable def extTree (T : List Bool → List Bool) (r : Req) (ρ : List Bool) : List Bool :=
  if ρ = r.2.1 then (diagPair (codeEnum r.2.2) (T r.1) (T r.2.1)).2
  else if ρ = r.1 then (diagPair (codeEnum r.2.2) (T r.1) (T r.2.1)).1
  else T ρ

theorem extTree_prefix (T : List Bool → List Bool) (r : Req) (ρ : List Bool) :
    T ρ <+: extTree T r ρ := by
  unfold extTree
  by_cases h2 : ρ = r.2.1
  · rw [if_pos h2, h2]
    exact (diagPair_spec _ _ _).2.1
  · rw [if_neg h2]
    by_cases h1 : ρ = r.1
    · rw [if_pos h1, h1]
      exact (diagPair_spec _ _ _).1
    · rw [if_neg h1]

theorem extTree_diag (T : List Bool → List Bool) (r : Req) (h : r.1 ≠ r.2.1) :
    Diag (codeEnum r.2.2) (extTree T r r.1) (extTree T r r.2.1) := by
  have e1 : extTree T r r.1 = (diagPair (codeEnum r.2.2) (T r.1) (T r.2.1)).1 := by
    unfold extTree
    rw [if_neg h, if_pos rfl]
  have e2 : extTree T r r.2.1 = (diagPair (codeEnum r.2.2) (T r.1) (T r.2.1)).2 := by
    unfold extTree
    rw [if_pos rfl]
  rw [e1, e2]
  exact (diagPair_spec _ _ _).2.2

theorem foldl_extTree_prefix (L : List Req) (T : List Bool → List Bool) (ρ : List Bool) :
    T ρ <+: L.foldl extTree T ρ := by
  induction L generalizing T with
  | nil => exact List.prefix_refl _
  | cons r L ih => exact (extTree_prefix T r ρ).trans (ih (extTree T r))

theorem foldl_extTree_diag (L : List Req) (hL : ∀ r ∈ L, r.1 ≠ r.2.1)
    (T : List Bool → List Bool) :
    ∀ r ∈ L, Diag (codeEnum r.2.2) (L.foldl extTree T r.1) (L.foldl extTree T r.2.1) := by
  induction L generalizing T with
  | nil => exact fun r hr => nomatch hr
  | cons r L ih =>
    intro r' hr'
    rcases List.mem_cons.1 hr' with h | h
    · subst h
      exact (extTree_diag T r' (hL r' (List.mem_cons.2 (Or.inl rfl)))).mono
        (foldl_extTree_prefix L (extTree T r') r'.1) (foldl_extTree_prefix L (extTree T r') r'.2.1)
    · exact ih (fun r'' hr'' => hL r'' (List.mem_cons.2 (Or.inr hr''))) (extTree T r) r' h

/-- All strings of bits of length `n`. -/
def bitStrings : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (bitStrings n).flatMap fun v => [false, true].map fun b => v ++ [b]

theorem mem_bitStrings {n : ℕ} {v : List Bool} : v ∈ bitStrings n ↔ v.length = n := by
  have hall : ∀ b : Bool, b ∈ [false, true] := by decide
  induction n generalizing v with
  | zero =>
    simp only [bitStrings, List.mem_singleton]
    exact List.length_eq_zero_iff.symm
  | succ n ih =>
    simp only [bitStrings, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨u, hu, a, -, rfl⟩
      rw [List.length_append, ih.1 hu, List.length_singleton]
    · intro hv
      have hne : v ≠ [] := fun e => by rw [e, List.length_nil] at hv; omega
      exact ⟨v.dropLast, ih.2 (by rw [List.length_dropLast, hv]; rfl), v.getLast hne, hall _,
        List.dropLast_append_getLast hne⟩

/-- The requirements of stage `s + 1`. -/
def reqs (s : ℕ) : List Req :=
  (bitStrings (s + 1)).flatMap fun ρ => (bitStrings (s + 1)).flatMap fun ρ' =>
    if ρ = ρ' then [] else (List.range (s + 1)).map fun e => (ρ, ρ', e)

theorem reqs_ne {s : ℕ} {r : Req} (hr : r ∈ reqs s) : r.1 ≠ r.2.1 := by
  simp only [reqs, List.mem_flatMap] at hr
  obtain ⟨ρ, -, ρ', -, hr⟩ := hr
  by_cases h : ρ = ρ'
  · rw [if_pos h] at hr
    exact nomatch hr
  · rw [if_neg h, List.mem_map] at hr
    obtain ⟨e, -, rfl⟩ := hr
    exact h

theorem mem_reqs {s : ℕ} {ρ ρ' : List Bool} {e : ℕ} (hρ : ρ.length = s + 1)
    (hρ' : ρ'.length = s + 1) (h : ρ ≠ ρ') (he : e ≤ s) : ((ρ, ρ', e) : Req) ∈ reqs s := by
  simp only [reqs, List.mem_flatMap]
  refine ⟨ρ, mem_bitStrings.2 hρ, ρ', mem_bitStrings.2 hρ', ?_⟩
  rw [if_neg h, List.mem_map]
  exact ⟨e, List.mem_range.2 (Nat.lt_succ_of_le he), rfl⟩

/-- The strings of the perfect tree at stage `s`, at the nodes of length `s`. -/
noncomputable def stage : ℕ → List Bool → List Bool
  | 0 => fun _ => []
  | s + 1 => (reqs s).foldl extTree fun ρ => stage s ρ.dropLast

theorem stage_prefix_succ (s : ℕ) (ρ : List Bool) : stage s ρ.dropLast <+: stage (s + 1) ρ :=
  foldl_extTree_prefix (reqs s) (fun ρ => stage s ρ.dropLast) ρ

/-- **Every requirement of stage `s + 1` holds at stage `s + 1`.** -/
theorem stage_diag (s : ℕ) {ρ ρ' : List Bool} {e : ℕ} (hρ : ρ.length = s + 1)
    (hρ' : ρ'.length = s + 1) (h : ρ ≠ ρ') (he : e ≤ s) :
    Diag (codeEnum e) (stage (s + 1) ρ) (stage (s + 1) ρ') :=
  foldl_extTree_diag (reqs s) (fun _ hr => reqs_ne hr) (fun ρ => stage s ρ.dropLast)
    ((ρ, ρ', e) : Req) (mem_reqs hρ hρ' h he)

/-- The first `s` bits of a path. -/
def path (f : ℕ → Bool) : ℕ → List Bool
  | 0 => []
  | s + 1 => path f s ++ [f s]

theorem length_path (f : ℕ → Bool) (s : ℕ) : (path f s).length = s := by
  induction s with
  | zero => rfl
  | succ s ih => rw [path, List.length_append, ih, List.length_singleton]

theorem path_getElem? (f : ℕ → Bool) {i s : ℕ} (h : i < s) : (path f s)[i]? = some (f i) := by
  induction s with
  | zero => exact absurd h (Nat.not_lt_zero i)
  | succ s ih =>
    rw [path]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 h) with h' | h'
    · rw [List.getElem?_append_left (lt_of_lt_of_eq h' (length_path f s).symm), ih h']
    · subst h'
      rw [List.getElem?_append_right (le_of_eq (length_path f i)), length_path, Nat.sub_self,
        List.getElem?_cons_zero]

theorem path_dropLast (f : ℕ → Bool) (s : ℕ) : (path f (s + 1)).dropLast = path f s := by
  rw [path, List.dropLast_concat]

theorem stage_path_prefix (f : ℕ → Bool) {s t : ℕ} (h : s ≤ t) :
    stage s (path f s) <+: stage t (path f t) := by
  induction t with
  | zero =>
    rw [Nat.le_zero.1 h]
  | succ t ih =>
    rcases lt_or_eq_of_le h with h' | h'
    · have hs := stage_prefix_succ t (path f (t + 1))
      rw [path_dropLast] at hs
      exact (ih (Nat.lt_succ_iff.1 h')).trans hs
    · rw [h']

theorem getElem?_eq_of_prefix {σ σ' : List Bool} (hp : σ <+: σ') {m : ℕ} (hm : m < σ.length) :
    σ[m]? = σ'[m]? := by
  rw [List.prefix_iff_eq_take.1 hp, List.getElem?_take_of_lt hm]

/-- The set of a path: the union of its strings. -/
def branchSet (f : ℕ → Bool) : Set ℕ :=
  {m | ∃ s, (stage s (path f s))[m]? = some true}

/-- **The set of a path extends every string on the path.** -/
theorem extends_branchSet (f : ℕ → Bool) (s : ℕ) :
    Extends (stage s (path f s)) (branchSet f) := by
  intro m hm
  obtain ⟨b, hb⟩ : ∃ b, (stage s (path f s))[m]? = some b := ⟨_, List.getElem?_eq_getElem hm⟩
  rw [hb]
  congr 1
  have key : m ∈ branchSet f ↔ b = true := by
    constructor
    · rintro ⟨t, ht⟩
      rcases le_total s t with hst | hts
      · have e := getElem?_eq_of_prefix (stage_path_prefix f hst) hm
        rw [hb, ht] at e
        exact Option.some.inj e
      · have hmt : m < (stage t (path f t)).length := by
          by_contra hn
          rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at ht
          exact nomatch ht
        have e := getElem?_eq_of_prefix (stage_path_prefix f hts) hmt
        rw [hb, ht] at e
        exact (Option.some.inj e).symm
    · intro hbt
      exact ⟨s, by rw [hb, hbt]⟩
  cases b
  · exact (decide_eq_false fun h => absurd (key.1 h) (by decide)).symm
  · exact (decide_eq_true (key.2 rfl)).symm

/-- **Distinct paths give Turing incomparable sets.** -/
theorem not_turingReducible_branchSet {f f' : ℕ → Bool} (hff : f ≠ f') :
    ¬ TuringReducible (setOracle (branchSet f)) (setOracle (branchSet f')) := by
  intro h
  obtain ⟨c, hc⟩ := exists_eval_eq (RecursiveIn.iff_nat.1 h)
  obtain ⟨e, rfl⟩ := codeEnum_surjective c
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ f' i := Function.ne_iff.1 hff
  have hne : path f (max e i + 1) ≠ path f' (max e i + 1) := by
    intro heq
    have h1 := path_getElem? f (Nat.lt_succ_of_le (le_max_right e i))
    have h2 := path_getElem? f' (Nat.lt_succ_of_le (le_max_right e i))
    rw [heq, h2] at h1
    exact hi (Option.some.inj h1).symm
  exact stage_diag (max e i) (length_path f _) (length_path f' _) hne (le_max_left e i)
    (branchSet f) (branchSet f') (extends_branchSet f _) (extends_branchSet f' _) hc

theorem branchSet_injective : Function.Injective branchSet := by
  intro f f' h
  by_contra hff
  have hred : TuringReducible (setOracle (branchSet f)) (setOracle (branchSet f')) := by
    rw [h]
    exact TuringReducible.refl _
  exact not_turingReducible_branchSet hff hred

/-- **A continuum antichain of Turing degrees.** -/
theorem exists_turing_antichain_continuum :
    ∃ F : Set (Set ℕ), Cardinal.mk F = Cardinal.continuum ∧
      ∀ B ∈ F, ∀ C ∈ F, TuringReducible (setOracle B) (setOracle C) → B = C := by
  have hφ : Function.Injective fun X : Set ℕ => branchSet fun m => decide (m ∈ X) := by
    intro X Y h
    have e := branchSet_injective h
    ext m
    simpa using congrFun e m
  refine ⟨Set.range fun X : Set ℕ => branchSet fun m => decide (m ∈ X), ?_, ?_⟩
  · rw [Cardinal.mk_range_eq _ hφ, Cardinal.mk_set_nat]
  · rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩ h
    by_contra hne
    have hff : (fun m => decide (m ∈ X)) ≠ (fun m => decide (m ∈ Y)) :=
      fun e => hne (congrArg branchSet e)
    exact not_turingReducible_branchSet hff h

end OracleUse
end GroupApproximation

#audit_axioms GroupApproximation.OracleUse.stage_diag
#audit_axioms GroupApproximation.OracleUse.extends_branchSet
#audit_axioms GroupApproximation.OracleUse.not_turingReducible_branchSet
#audit_axioms GroupApproximation.OracleUse.exists_turing_antichain_continuum
