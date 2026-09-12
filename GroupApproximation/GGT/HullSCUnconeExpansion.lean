import GroupApproximation.GGT.HullSCCyclicPeripheralRemoval
import GroupApproximation.GGT.OsinGeodesicWord
import GroupApproximation.Meta.AxiomGuard

/-!
# Un-coning cyclic peripherals, step 1: the expanded geodesics

`GGT/HullSCCyclicPeripheralRemoval.lean` reduces Osin's Lemma 8.2 at infinite cyclic members to
the hyperbolicity of the un-coned relative Cayley graph `Γ(Q, S')`, where
`S' = (J.base ∪ ⋃ᵢ {gᵢ, gᵢ⁻¹}) ∪ ⋃_λ H_λ` is the alphabet of `removeCyclicPeripherals J g`.  The
proof applies Bowditch's guessing-geodesics criterion (`OsinEnlargement.guessingGeodesics`) to the
following paths: take a geodesic word of `J` from `x` to `y` and expand every component letter of a
cyclic member, `gᵢᵗ`, into `|t|` steps `gᵢ^{±1}` along its coset; every other letter is already a
letter of `S'`.

This module builds those paths and proves the three conditions of the criterion that involve no
geometry:

* `guessPath_zero`, `guessPath_len` — the path starts at `x` and ends at `y`;
* `wordDist_guessPath_succ` — consecutive points are adjacent in `Γ(Q, S')`;
* `guessPath_short` — when `x` and `y` are adjacent the path has bounded diameter.  An adjacent pair
  is spelled by one letter of `J`; if it is a cyclic letter `gᵢᵗ`, either `gᵢᵗ = gᵢ^{±1}`, or its
  value is a base letter, an original peripheral letter, or a letter of another cyclic member, and
  in the second case the one-letter word avoids the `i`-th component, so `gᵢᵗ` lies in the relative
  ball of radius one of the `i`-th member, which is finite (`exists_expo_bound`).

The thin-triangle condition is the geometric content and is proved in the following modules.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v w

namespace Uncone

section Expansion

variable {Q : Type u} [Group Q] {Lambda : Type w} {I : Type v}

/-! ## Exponents along a cyclic member -/

/-- **An exponent of `e` along `gᵢ`**: a chosen `t` with `gᵢᵗ = e` when `e ∈ ⟨gᵢ⟩`, and `0`
otherwise.  For an element of infinite order it is the exponent (`expo_zpow`). -/
noncomputable def expo (g : I → Q) (i : I) (e : Q) : ℤ :=
  if h : e ∈ Subgroup.zpowers (g i) then Classical.choose (Subgroup.mem_zpowers_iff.mp h)
  else 0

theorem expo_spec (g : I → Q) (i : I) {e : Q} (h : e ∈ Subgroup.zpowers (g i)) :
    g i ^ expo g i e = e := by
  unfold expo
  rw [dif_pos h]
  exact Classical.choose_spec (Subgroup.mem_zpowers_iff.mp h)

/-- For an element of infinite order the chosen exponent is the exponent. -/
theorem expo_zpow (g : I → Q) (i : I) (hinf : ¬ IsOfFinOrder (g i)) (t : ℤ) :
    expo g i (g i ^ t) = t := by
  have hmem : g i ^ t ∈ Subgroup.zpowers (g i) := Subgroup.mem_zpowers_iff.mpr ⟨t, rfl⟩
  exact injective_zpow_iff_not_isOfFinOrder.mpr hinf (expo_spec g i hmem)

/-! ## Expanding a word -/

/-- **The expansion of one letter of `J`**: a base or original peripheral letter is kept, and a
letter `gᵢᵗ` of a cyclic member becomes `|t|` copies of `gᵢ^{±1}`. -/
noncomputable def expLetters (g : I → Q) : RelLetter Q (Sum Lambda I) → List Q
  | RelLetter.base b => [b]
  | RelLetter.comp (Sum.inl _) h => [h]
  | RelLetter.comp (Sum.inr i) e =>
      List.replicate (expo g i e).natAbs (if 0 ≤ expo g i e then g i else (g i)⁻¹)

/-- **The expansion of a word of `J`**, letter by letter. -/
noncomputable def expWord (g : I → Q) : List (RelLetter Q (Sum Lambda I)) → List Q
  | [] => []
  | a :: t => expLetters g a ++ expWord g t

theorem expWord_nil (g : I → Q) : expWord g ([] : List (RelLetter Q (Sum Lambda I))) = [] := rfl

theorem expWord_cons (g : I → Q) (a : RelLetter Q (Sum Lambda I))
    (t : List (RelLetter Q (Sum Lambda I))) :
    expWord g (a :: t) = expLetters g a ++ expWord g t := rfl

theorem expWord_append (g : I → Q) :
    ∀ w₁ w₂ : List (RelLetter Q (Sum Lambda I)),
      expWord g (w₁ ++ w₂) = expWord g w₁ ++ expWord g w₂ := by
  intro w₁
  induction w₁ with
  | nil => intro w₂; rfl
  | cons a t ih =>
      intro w₂
      rw [List.cons_append, expWord_cons, expWord_cons, ih, List.append_assoc]

/-- The expansion of a legal letter spells its value. -/
theorem prod_expLetters (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    {a : RelLetter Q (Sum Lambda I)} (ha : J.IsLetter a) :
    (expLetters g a).prod = a.val := by
  cases a with
  | base b => simp [expLetters, RelLetter.val]
  | comp s h =>
      cases s with
      | inl lam => simp [expLetters, RelLetter.val]
      | inr i =>
          have hmem : h ∈ Subgroup.zpowers (g i) := by
            rw [← hg i]
            exact ha
          have hspec := expo_spec g i hmem
          simp only [expLetters, RelLetter.val, List.prod_replicate]
          split_ifs with hnn
          · rw [← zpow_natCast]
            calc g i ^ ((expo g i h).natAbs : ℤ) = g i ^ expo g i h := by
                  congr 1
                  omega
              _ = h := hspec
          · rw [inv_pow, ← zpow_natCast, ← zpow_neg]
            calc g i ^ (-((expo g i h).natAbs : ℤ)) = g i ^ expo g i h := by
                  congr 1
                  omega
              _ = h := hspec

/-- The expansion of a legal word spells its value. -/
theorem prod_expWord (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) :
    ∀ w : List (RelLetter Q (Sum Lambda I)), (∀ a ∈ w, J.IsLetter a) →
      (expWord g w).prod = RelLetter.listVal w := by
  intro w
  induction w with
  | nil => intro _; rfl
  | cons a t ih =>
      intro hletters
      rw [expWord_cons, List.prod_append, prod_expLetters J g hg (hletters a (by simp)),
        ih (fun b hb => hletters b (List.mem_cons_of_mem a hb)),
        OsinComponents.listVal_cons]

/-- Every letter of the removed structure is a letter of `J`. -/
theorem removeCyclicPeripherals_alphabet_subset (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) :
    (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier ⊆ J.alphabet.carrier := by
  rintro x ((hx | hx) | hx)
  · exact Or.inl hx
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    refine Or.inr (Set.mem_iUnion.mpr ⟨Sum.inr i, ?_⟩)
    show x ∈ J.fam (Sum.inr i)
    rw [hg i]
    rcases hi with rfl | hi
    · exact Subgroup.mem_zpowers _
    · rw [Set.mem_singleton_iff] at hi
      rw [hi]
      exact (Subgroup.zpowers (g i)).inv_mem (Subgroup.mem_zpowers _)
  · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hx
    exact Or.inr (Set.mem_iUnion.mpr ⟨Sum.inl lam, hlam⟩)

/-- Every letter of the expansion of a legal letter is a letter of the removed structure. -/
theorem mem_expLetters (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) {a : RelLetter Q (Sum Lambda I)}
    (ha : J.IsLetter a) :
    ∀ x ∈ expLetters g a, x ∈ (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier := by
  intro x hx
  cases a with
  | base b =>
      have hxb : x = b := List.eq_of_mem_singleton hx
      rw [hxb]
      exact Or.inl (Or.inl ha)
  | comp s h =>
      cases s with
      | inl lam =>
          have hxh : x = h := List.eq_of_mem_singleton hx
          rw [hxh]
          exact Or.inr (Set.mem_iUnion.mpr ⟨lam, ha⟩)
      | inr i =>
          have hxg := List.eq_of_mem_replicate hx
          refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩))
          rw [hxg]
          split_ifs
          · exact Or.inl rfl
          · exact Or.inr rfl

/-- Every letter of the expansion of a legal word is a letter of the removed structure. -/
theorem mem_expWord (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) :
    ∀ w : List (RelLetter Q (Sum Lambda I)), (∀ a ∈ w, J.IsLetter a) →
      ∀ x ∈ expWord g w, x ∈ (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier := by
  intro w
  induction w with
  | nil => intro _ x hx; simp [expWord] at hx
  | cons a t ih =>
      intro hletters x hx
      rw [expWord_cons] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact mem_expLetters J g hg hbaseInv (hletters a (by simp)) x hx
      · exact ih (fun b hb => hletters b (List.mem_cons_of_mem a hb)) x hx

/-! ## The guessed paths -/

/-- A chosen geodesic word of `J` from `x` to `y`. -/
noncomputable def geodWord (J : RelGenSet Q (Sum Lambda I)) (x y : Q) :
    List (RelLetter Q (Sum Lambda I)) :=
  Classical.choose (OsinComponents.existsGeodesicWord J x y)

theorem geodWord_spec (J : RelGenSet Q (Sum Lambda I)) (x y : Q) :
    OsinComponents.IsGeodesicWord J x y (geodWord J x y) :=
  Classical.choose_spec (OsinComponents.existsGeodesicWord J x y)

/-- The expanded geodesic from `x` to `y`, as a word of `S'`. -/
noncomputable def guessWord (J : RelGenSet Q (Sum Lambda I)) (g : I → Q) (x y : Q) : List Q :=
  expWord g (geodWord J x y)

/-- The number of steps of the guessed path. -/
noncomputable def guessLen (J : RelGenSet Q (Sum Lambda I)) (g : I → Q) (x y : Q) : ℕ :=
  (guessWord J g x y).length

/-- **The guessed path from `x` to `y`**: the prefix products of the expanded geodesic. -/
noncomputable def guessPath (J : RelGenSet Q (Sum Lambda I)) (g : I → Q) (x y : Q) (j : ℕ) : Q :=
  x * ((guessWord J g x y).take j).prod

theorem guessPath_zero (J : RelGenSet Q (Sum Lambda I)) (g : I → Q) (x y : Q) :
    guessPath J g x y 0 = x := by
  simp [guessPath]

theorem guessPath_len (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i)) (x y : Q) :
    guessPath J g x y (guessLen J g x y) = y := by
  rw [guessPath, guessLen, List.take_length, guessWord,
    prod_expWord J g hg _ (geodWord_spec J x y).1]
  exact (geodWord_spec J x y).2.1

/-- **Consecutive points of a guessed path are adjacent in `Γ(Q, S')`.** -/
theorem wordDist_guessPath_succ (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (x y : Q) {j : ℕ}
    (hj : j < guessLen J g x y) :
    wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
      (guessPath J g x y j) (guessPath J g x y (j + 1)) ≤ 1 := by
  have hj' : j < (guessWord J g x y).length := hj
  have hmem := mem_expWord J g hg hbaseInv (geodWord J x y) (geodWord_spec J x y).1 _
    (List.getElem_mem hj')
  have h : (guessPath J g x y j)⁻¹ * guessPath J g x y (j + 1) = (guessWord J g x y)[j] := by
    unfold guessPath
    rw [List.prod_take_succ _ _ hj']
    group
  unfold wordDist
  rw [h]
  exact wordNorm_le_one_of_mem hmem

/-- **A guessed path is `1`-Lipschitz in its index.** -/
theorem wordDist_guessPath_le (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (x y : Q) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ guessLen J g x y) :
    wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
      (guessPath J g x y i) (guessPath J g x y j) ≤ j - i := by
  have hS := (removeCyclicPeripherals J g hg hbaseInv).alphabet.symmetricGenerating
  induction j, hij using Nat.le_induction with
  | base =>
      rw [wordDist_self]
      omega
  | succ n hin ih =>
      have hn : n < guessLen J g x y := by omega
      have hstep := wordDist_guessPath_succ J g hg hbaseInv x y hn
      have htri := wordDist_triangle hS (guessPath J g x y i) (guessPath J g x y n)
        (guessPath J g x y (n + 1))
      have hih := ih (by omega)
      omega

/-! ## The finite relative balls bound the exponents -/

/-- **Finitely many exponents occur in a relative ball of a cyclic member.**  The relative balls
of `J` are finite, and there are finitely many members. -/
theorem exists_expo_bound [Finite I] (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hJ : J.IsHyperbolicallyEmbedded) (n : ℕ) :
    ∃ T : ℕ, ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) n → (expo g i e).natAbs ≤ T := by
  have hfin : (⋃ i : I, (fun e => (expo g i e).natAbs) '' J.relBall (Sum.inr i) n).Finite :=
    Set.finite_iUnion (fun i => (hJ.locallyFinite (Sum.inr i) n).image _)
  obtain ⟨T, hT⟩ := hfin.bddAbove
  exact ⟨T, fun i e he => hT (Set.mem_iUnion.mpr ⟨i, ⟨e, he, rfl⟩⟩)⟩

/-- A one-letter word that is not a letter of the `i`-th member lies in its relative ball of
radius one. -/
theorem mem_relBall_inr_one_of_letter (J : RelGenSet Q (Sum Lambda I)) {i : I} {e : Q}
    (he : e ∈ J.fam (Sum.inr i)) (b : RelLetter Q (Sum Lambda I)) (hb : J.IsLetter b)
    (hbval : b.val = e) (hnot : ¬ RelLetter.IsCompOf (Sum.inr i) b) :
    e ∈ J.relBall (Sum.inr i) 1 := by
  refine ⟨he, [b], ?_, ?_, ?_, by simp⟩
  · intro a ha
    rw [List.eq_of_mem_singleton ha]
    exact hb
  · simp [RelLetter.listVal, hbval]
  · exact ⟨fun h => hnot h.1, trivial⟩

/-- **Adjacent endpoints give a short guessed path.** -/
theorem guessLen_le_of_wordDist_le_one (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hinf : ∀ i : I, ¬ IsOfFinOrder (g i))
    {T : ℕ} (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) 1 → (expo g i e).natAbs ≤ T)
    {x y : Q}
    (hxy : wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier x y ≤ 1) :
    guessLen J g x y ≤ max T 1 := by
  have hS' := (removeCyclicPeripherals J g hg hbaseInv).alphabet.symmetricGenerating
  have hw := geodWord_spec J x y
  have hdd : wordDist J.alphabet.carrier x y ≤ 1 :=
    le_trans (wordNorm_mono (removeCyclicPeripherals_alphabet_subset J g hg hbaseInv)
      (wordLengths_nonempty hS' _)) hxy
  have hlen : (geodWord J x y).length ≤ 1 := by
    rw [hw.2.2]
    exact hdd
  unfold guessLen guessWord
  rcases hcase : geodWord J x y with _ | ⟨a, t⟩
  · simp [expWord]
  · have ht : t = [] := by
      rw [hcase] at hlen
      simp only [List.length_cons] at hlen
      exact List.length_eq_zero_iff.mp (by omega)
    subst ht
    have ha : J.IsLetter a := hw.1 a (by rw [hcase]; simp)
    have hval : x * a.val = y := by
      have h := hw.2.1
      rw [hcase] at h
      simpa [RelLetter.listVal] using h
    rw [expWord_cons, expWord_nil, List.append_nil]
    cases a with
    | base b => simp [expLetters]
    | comp s e =>
        cases s with
        | inl lam => simp [expLetters]
        | inr i =>
            simp only [expLetters, List.length_replicate]
            have he : e ∈ J.fam (Sum.inr i) := ha
            have heval : x⁻¹ * y = e := by
              rw [← hval]
              simp [RelLetter.val]
            have hnorm : wordNorm (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier e
                ≤ 1 := by
              have h := hxy
              unfold wordDist at h
              rwa [heval] at h
            obtain ⟨l, hl, hllen⟩ := exists_isWord_length_eq hS' e
            rcases hl' : l with _ | ⟨b, l'⟩
            · have he1 : e = 1 := by
                have h := hl.prod_eq
                rw [hl'] at h
                simpa using h.symm
              have h0 : expo g i e = 0 := by
                rw [he1, ← zpow_zero (g i)]
                exact expo_zpow g i (hinf i) 0
              rw [h0]
              omega
            · have hl'nil : l' = [] := by
                rw [hl'] at hllen
                simp only [List.length_cons] at hllen
                exact List.length_eq_zero_iff.mp (by omega)
              subst hl'nil
              have heb : e = b := by
                have h := hl.prod_eq
                rw [hl'] at h
                simpa using h.symm
              have hbS : b ∈ (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier :=
                hl.letters b (by rw [hl']; simp)
              rw [← heb] at hbS
              rcases hbS with (hbase | hcyc) | hperiph
              · exact le_trans (hT i e (mem_relBall_inr_one_of_letter J he (RelLetter.base e)
                  hbase rfl (fun h => h))) (le_max_left _ _)
              · obtain ⟨i', hi'⟩ := Set.mem_iUnion.mp hcyc
                by_cases hii : i' = i
                · subst hii
                  rcases hi' with rfl | hi'
                  · have h1 : expo g i' (g i') = 1 := by
                      have := expo_zpow g i' (hinf i') 1
                      rwa [zpow_one] at this
                    rw [h1]
                    omega
                  · rw [Set.mem_singleton_iff] at hi'
                    have hm1 : expo g i' e = -1 := by
                      rw [hi', ← zpow_neg_one]
                      exact expo_zpow g i' (hinf i') (-1)
                    rw [hm1]
                    omega
                · have he' : e ∈ J.fam (Sum.inr i') := by
                    rw [hg i']
                    rcases hi' with rfl | hi'
                    · exact Subgroup.mem_zpowers _
                    · rw [Set.mem_singleton_iff] at hi'
                      rw [hi']
                      exact (Subgroup.zpowers (g i')).inv_mem (Subgroup.mem_zpowers _)
                  refine le_trans (hT i e (mem_relBall_inr_one_of_letter J he
                    (RelLetter.comp (Sum.inr i') e) he' rfl ?_)) (le_max_left _ _)
                  intro hc
                  exact hii (Sum.inr_injective hc)
              · obtain ⟨lam, hlam⟩ := Set.mem_iUnion.mp hperiph
                refine le_trans (hT i e (mem_relBall_inr_one_of_letter J he
                  (RelLetter.comp (Sum.inl lam) e) hlam rfl ?_)) (le_max_left _ _)
                intro hc
                exact Sum.inl_ne_inr hc

/-- **The short-path condition of the guessing criterion.** -/
theorem guessPath_short (J : RelGenSet Q (Sum Lambda I)) (g : I → Q)
    (hg : ∀ i : I, J.fam (Sum.inr i) = Subgroup.zpowers (g i))
    (hbaseInv : ∀ x ∈ J.base, x⁻¹ ∈ J.base) (hinf : ∀ i : I, ¬ IsOfFinOrder (g i))
    {T : ℕ} (hT : ∀ (i : I) (e : Q), e ∈ J.relBall (Sum.inr i) 1 → (expo g i e).natAbs ≤ T)
    (x y : Q)
    (hxy : wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier x y ≤ 1)
    (i : ℕ) (hi : i ≤ guessLen J g x y) (j : ℕ) (hj : j ≤ guessLen J g x y) :
    wordDist (removeCyclicPeripherals J g hg hbaseInv).alphabet.carrier
      (guessPath J g x y i) (guessPath J g x y j) ≤ max T 1 := by
  have hS' := (removeCyclicPeripherals J g hg hbaseInv).alphabet.symmetricGenerating
  have hlen := guessLen_le_of_wordDist_le_one J g hg hbaseInv hinf hT hxy
  rcases le_total i j with hij | hji
  · have h := wordDist_guessPath_le J g hg hbaseInv x y hij hj
    omega
  · have h := wordDist_guessPath_le J g hg hbaseInv x y hji hi
    rw [wordDist_comm hS'] at h
    omega

end Expansion

end Uncone

end GGT
end GroupApproximation

#audit_axioms GroupApproximation.GGT.Uncone.expo_zpow
#audit_axioms GroupApproximation.GGT.Uncone.prod_expWord
#audit_axioms GroupApproximation.GGT.Uncone.mem_expWord
#audit_axioms GroupApproximation.GGT.Uncone.guessPath_len
#audit_axioms GroupApproximation.GGT.Uncone.wordDist_guessPath_succ
#audit_axioms GroupApproximation.GGT.Uncone.wordDist_guessPath_le
#audit_axioms GroupApproximation.GGT.Uncone.exists_expo_bound
#audit_axioms GroupApproximation.GGT.Uncone.guessPath_short
