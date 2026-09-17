import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Primrec
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Endpoints
import GroupApproximation.Computability.OracleTruthTable
import GroupApproximation.Leavitt.ElementaryGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# `lem:halfline` (b): the word problem of `G_Δ` reduces to that of `Δ`

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline` (b):

* tex l.657–661, sentence 7bfa078c0bed:
  > A word in the generators of G_Δ multiplies out to a matrix with entries Σ_ξ p_ξ u_ξ, where each p_ξ is a
  > polynomial over F_2 in finitely many coordinates x(δ), as u_ξ e_U u_ξ^{-1} is the indicator of
  > {x : x(δ) = 1 + c(δ)} for ξ : x ↦ δx + c.
* tex l.661–664, sentence e3cd35e16e2f:
  > After collecting equal ξ and equal coordinates, the word is trivial if and only if every coefficient of its
  > difference from I_3 vanishes at every assignment of its finitely many variables, as Ω is the full shift.
* tex l.665, sentence dfa561ecfaa5:
  > So the word problem of G_Δ is Turing reducible to that of Δ.

## Proof route

* Every entry of every generator matrix is the value of a table `Σ (a, [p₁, …, pₙ])` of monomials
  `(e_U ∘ ξ_{p₁}⁻¹) ⋯ (e_U ∘ ξ_{pₙ}⁻¹) u_{ξ_a}` (`exists_hMat_eq`), and a word multiplies out to the product table
  matrix (`hMatEval_hWordMat`). The atom `e_U ∘ ξ_p⁻¹ = u_{ξ_p} e_U u_{ξ_p}⁻¹` is `x ↦ x(δ) + c(δ)` (`hAtom_apply`).
* A word is trivial iff each entry of its table matrix plus `I₃` vanishes (`wordValue_eq_one_iff_hTab`), iff every
  collected coefficient vanishes at every point (`hTabEval_eq_zero_iff`), iff it vanishes at the finitely many points
  `xB B` for subsets `B` of the atoms (`hTabEval_eq_zero_iff_subsets`).
* The check only asks equalities `ξ_a = ξ_b` in `Λ`, which are the queries `a⁻¹ b` to the word problem of `Λ`
  (`look_iff`). This is a truth-table reduction (`hostOracle_eq`, `primrec_hostQ`, `primrec_hostD`), composed with
  the reduction of `Λ` to `Δ` (`manuscriptSentence_halflineLambdaWordProblem`).
-/

namespace GroupApproximation
namespace Manuscript
namespace SimpleKazhdanSofic
namespace HalflineB

open GroupApproximation.SimpleKazhdanSofic GroupApproximation.SimpleKazhdanSofic.Lamplighter
open Encodable
open SkewMonoidAlgebra (single)

/-! ### Looking up recorded answers -/

theorem getD_map_of_lt (g : ℕ → ℕ) (Q : List ℕ) (k : ℕ) (hk : k < Q.length) :
    (Q.map g).getD k 0 = g (Q.getD k 0) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some,
    Option.getD_some]

theorem exists_getD_eq (n : ℕ) (Q : List ℕ) (hn : n ∈ Q) : ∃ k, k < Q.length ∧ Q.getD k 0 = n := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hn
  exact ⟨k, hk, by simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]⟩

/-- The recorded answer to a query `n` of `Q`, with answers `g`, is `g n`. -/
theorem lookL_map (g : ℕ → ℕ) (Q : List ℕ) (n : ℕ) (hn : n ∈ Q) : lookL Q (Q.map g) n = decide (g n = 1) := by
  refine Bool.eq_iff_iff.2 ?_
  simp only [lookL, anyB_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, hk1, hk2⟩
    rw [getD_map_of_lt g Q k (List.mem_range.1 hk), hk1] at hk2
    exact hk2
  · intro h
    obtain ⟨k, hk, hkn⟩ := exists_getD_eq n Q hn
    exact ⟨k, List.mem_range.2 hk, hkn, by rw [getD_map_of_lt g Q k hk, hkn]; exact h⟩

/-- **The answers to the pair queries decide equality in `Λ`** (tex l.654–657): the word problem of `Λ` on `a⁻¹ b`
decides `ξ_a = ξ_b`. -/
theorem look_iff {Δ : Type} [Group Δ] {ι : Type} [Primcodable ι] (s : ι → Δ) (S : List (LW ι)) :
    ∀ a ∈ S, ∀ b ∈ S, look (pairCodes S, (pairCodes S).map (deltaAnswer (lampGen s))) a b = true ↔
      wordValue (lampGen s) a = wordValue (lampGen s) b := by
  classical
  intro a ha b hb
  have hmem : encode (wordInv a ++ b) ∈ pairCodes S := by
    show encode (wordInv a ++ b) ∈ S.flatMap fun a => S.map fun b => encode (wordInv a ++ b)
    exact List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem (f := fun b => encode (wordInv a ++ b)) hb⟩
  show lookL (pairCodes S) ((pairCodes S).map (deltaAnswer (lampGen s))) (encode (wordInv a ++ b)) = true ↔ _
  rw [lookL_map _ _ _ hmem, decide_eq_true_eq, deltaAnswer_encode]
  have key : wordValue (lampGen s) (wordInv a ++ b) = 1 ↔ wordValue (lampGen s) a = wordValue (lampGen s) b := by
    rw [wordValue_append, wordValue_wordInv, inv_mul_eq_one]
  by_cases h : wordValue (lampGen s) (wordInv a ++ b) = 1
  · rw [if_pos h]
    exact ⟨fun _ => key.1 h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun e => absurd e Nat.zero_ne_one, fun e => absurd (key.2 e) h⟩

/-! ### The truth-table reduction -/

/-- **The oracle of a word problem in units is the truth table `hostD` on the queries `hostQ`**, answered by the
word problem of `Λ`. -/
theorem hostOracle_eq {Δ : Type} [Group Δ] {ι : Type} [Primcodable ι] (s : ι → Δ) {κ : Type} [Primcodable κ]
    (v : κ → (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) (L : κ × Bool → HMat ι)
    (hL : ∀ x : κ × Bool, hMatEval s (L x) =
      ((if x.2 then v x.1 else (v x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ)))
    (n : ℕ) :
    wordProblemOracle v n = Part.some (hostD L n ((hostQ L n).map (deltaAnswer (lampGen s)))) := by
  classical
  cases hd : decode (α := List (κ × Bool)) n with
  | none =>
    have hex : ¬ ∃ w' : List (κ × Bool), Encodable.decode n = some w' ∧ wordValue v w' = 1 := by
      rintro ⟨w', hw', -⟩
      rw [hd] at hw'
      cases hw'
    simp only [wordProblemOracle]
    rw [if_neg hex]
    simp only [hostD, hd, Option.isSome_none, Bool.false_and, cond_false]
  | some w =>
    have hQ : hostQ L n = pairCodes (matW (matTabs (hWordMat L w))) := by
      simp only [hostQ, hd, Option.getD_some]
    have hD : hostD L n ((hostQ L n).map (deltaAnswer (lampGen s))) =
        cond (matOk (look (pairCodes (matW (matTabs (hWordMat L w))),
            (pairCodes (matW (matTabs (hWordMat L w)))).map (deltaAnswer (lampGen s))))
          (matTabs (hWordMat L w))) 1 0 := by
      simp only [hostD, hQ, hd, Option.isSome_some, Option.getD_some, Bool.true_and]
    have key := wordValue_eq_one_iff_matOk s v L hL w (S := matW (matTabs (hWordMat L w)))
      (o := look (pairCodes (matW (matTabs (hWordMat L w))),
        (pairCodes (matW (matTabs (hWordMat L w)))).map (deltaAnswer (lampGen s))))
      (fun a ha => ha) (look_iff s (matW (matTabs (hWordMat L w))))
    rw [hD]
    by_cases h : wordValue v w = 1
    · rw [key.1 h, cond_true]
      have hex : ∃ w' : List (κ × Bool), Encodable.decode n = some w' ∧ wordValue v w' = 1 := ⟨w, hd, h⟩
      simp only [wordProblemOracle]
      rw [if_pos hex]
    · rw [Bool.eq_false_iff.2 fun e => h (key.2 e), cond_false]
      have hex : ¬ ∃ w' : List (κ × Bool), Encodable.decode n = some w' ∧ wordValue v w' = 1 := by
        rintro ⟨w', hw', h'⟩
        rw [hd, Option.some_inj] at hw'
        subst hw'
        exact h h'
      simp only [wordProblemOracle]
      rw [if_neg hex]

/-- The word problem of units with table matrices `L` reduces to the word problem of `Λ`. -/
theorem turingReducible_units {Δ : Type} [Group Δ] {ι : Type} [Primcodable ι] [Finite ι] (s : ι → Δ)
    {κ : Type} [Primcodable κ] [Finite κ] (v : κ → (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ)
    (L : κ × Bool → HMat ι)
    (hL : ∀ x : κ × Bool, hMatEval s (L x) =
      ((if x.2 then v x.1 else (v x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ))) :
    TuringReducible (wordProblemOracle v) (wordProblemOracle (lampGen s)) :=
  OracleTruthTable.turingReducible_of_truthTable (gt := deltaAnswer (lampGen s)) (fun _ => rfl)
    (primrec_hostQ L) (primrec_hostD L) (hostOracle_eq s v L hL)

/-! ### Atoms and finitely many assignments -/

/-- The atom of the empty word is `e_U`, the coordinate at `1`. -/
theorem hAtom_nil {Δ : Type} [Group Δ] {ι : Type} (s : ι → Δ) : hAtom s ([] : LW ι) = coord Δ 1 := by
  have h := hAtom_liftD s ([] : List (ι × Bool))
  rw [wordValue_nil] at h
  exact h

theorem zmod_two_add_eq_one_iff (a c : ZMod 2) : a + c = 1 ↔ a = 1 + c := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl <;> rcases zmod_two_eq_zero_or_one c with rfl | rfl <;> decide

/-- `u_{ξ_p} e_U u_{ξ_p}⁻¹` is the atom of `p`, as monomials. -/
theorem hMonoEval_conj {Δ : Type} [Group Δ] {ι : Type} (s : ι → Δ) (p : LW ι) :
    hMonoEval s (p, []) * hMonoEval s ([], [[]]) * hMonoEval s (wordInv p, []) = hMonoEval s ([], [p]) := by
  rw [hMonoEval_mul, hMonoEval_mul]
  simp only [hMonoMul, List.append_nil, List.nil_append, List.map_cons, List.map_nil, hMonoEval, wordValue_append,
    wordValue_wordInv, mul_inv_cancel, wordValue_nil]

/-- **A table vanishes iff its collected coefficients vanish at the finitely many assignments** `xB B`, `B` a subset
of its atoms. -/
theorem hTabEval_eq_zero_iff_subsets {Δ : Type} [Group Δ] {ι : Type} (s : ι → Δ) (T : HTable ι) :
    hTabEval s T = 0 ↔
      ∀ m0 ∈ T, ∀ B ∈ subsets (tabU T), hCoeffLC s (wordValue (lampGen s) m0.1) T (xB s B) = 0 := by
  rw [hTabEval_eq_zero_iff]
  constructor
  · intro h m0 hm0 B _
    exact h m0 hm0 (xB s B)
  · intro h m0 hm0 x
    have hB := filter_mem_subsets (fun v => decide (x (wordValue s (deltaWord v)) = 1)) (tabU T)
    rw [hCoeffLC_agree s _ T x
      (xB s ((tabU T).filter fun v => decide (x (wordValue s (deltaWord v)) = 1))) ?_]
    · exact h m0 hm0 _ hB
    · intro m hm
      refine hCyl_agree s m.2 _ _ fun p hp => ?_
      have hpU : p ∈ tabU T := List.mem_flatMap.2 ⟨m, hm, hp⟩
      rw [hAtom_apply, hAtom_apply, xB_filter s (tabU T) x p hpU]

/-! ### Endpoints -/

/-- **A word multiplies out** (tex l.657–661). For a generating family `s` of `Δ` and any family `u` of
`G_Δ = EL_3(R_Δ)`, there are table matrices `L` of the letters such that every word `w` in `u` is the value of the
table matrix `hWordMat L w`. The value of a table is `Σ_(a, P) p_P u_{ξ_a}`, with `p_P` the product of the atoms
of `P`, a polynomial in the coordinates `x(δ_p)`. The atom of `p` is `u_{ξ_p} e_U u_{ξ_p}⁻¹` (monomials `(p, [])`
are `u_{ξ_p}`, the monomial `([], [[]])` is `e_U`), and for `ξ_p = inl c · inr δ` it is the indicator of
`{x : x(δ) = 1 + c(δ)}`. -/
theorem manuscriptSentence_hostWordMultipliesOut {Δ : Type} [Group Δ] {ι : Type} (s : ι → Δ)
    (hs : Subgroup.closure (Set.range s) = ⊤) {κ : Type}
    (u : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))) :
    (∃ L : κ × Bool → HMat ι, ∀ w : List (κ × Bool),
      hMatEval s (hWordMat L w) =
        (((wordValue u w : ↥(elementaryGroup (Fin 3) (LampRing Δ))) : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
          Matrix (Fin 3) (Fin 3) (LampRing Δ))) ∧
    (∀ T : HTable ι, hTabEval s T =
      (T.map fun m => single (wordValue (lampGen s) m.1)
        (ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (hCyl s m.2))).sum) ∧
    (∀ (P : List (LW ι)) (x : LampSpace Δ), hCyl s P x = (P.map fun p => hAtom s p x).prod) ∧
    hAtom s ([] : LW ι) = coord Δ 1 ∧
    (∀ p : LW ι,
      hMonoEval s (p, []) * hMonoEval s ([], [[]]) * hMonoEval s (wordInv p, []) = hMonoEval s ([], [p])) ∧
    ∀ (p : LW ι) (x : LampSpace Δ),
      wordValue (lampGen s) p = SemidirectProduct.inl (Multiplicative.ofAdd (lampSum s p)) *
        SemidirectProduct.inr (wordValue s (deltaWord p)) ∧
      (hAtom s p x = 1 ↔ x (wordValue s (deltaWord p)) = 1 + lampSum s p (wordValue s (deltaWord p))) := by
  choose L hL using fun x : κ × Bool => exists_hMat_eq s hs
    ((if x.2 then ((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) x.1
      else (((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ))
  refine ⟨⟨L, fun w => ?_⟩, fun T => rfl, hCyl_apply s, hAtom_nil s, hMonoEval_conj s,
    fun p x => ⟨wordValue_lampGen s p, ?_⟩⟩
  · rw [hMatEval_hWordMat s ((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) L hL w,
      wordValue_map u (elementaryGroup (Fin 3) (LampRing Δ)).subtype w, Subgroup.coe_subtype]
  · rw [hAtom_apply]
    exact zmod_two_add_eq_one_iff _ _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_hostWordMultipliesOut

/-- **The triviality criterion** (tex l.661–664). Collecting equal `ξ`, the coefficient of `u_η` of a table is the
sum `hCoeffLC` of the atom products of its monomials with value `η`. With table matrices `L` of the letters, a word
`w` in a family `u` of `G_Δ` is trivial iff every coefficient of every entry of its difference from `I₃` (the entry
table plus `I₃`, in characteristic two) vanishes at every point of `Ω`, and iff it vanishes at the finitely many
assignments `xB B` of the variables, `B` a subset of the atoms. -/
theorem manuscriptSentence_hostTrivialityCriterion {Δ : Type} [Group Δ] {ι : Type} (s : ι → Δ)
    (hs : Subgroup.closure (Set.range s) = ⊤) {κ : Type}
    (u : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))) :
    (∀ (T : HTable ι) (η : LampAffine Δ), SkewMonoidAlgebra.coeff (hTabEval s T) η =
      ClopenGroupCoeff.of (LampAffine Δ) (LampSpace Δ) (ZMod 2) (hCoeffLC s η T)) ∧
    ∃ L : κ × Bool → HMat ι, ∀ w : List (κ × Bool),
      hMatEval s (hWordMat L w) =
        (((wordValue u w : ↥(elementaryGroup (Fin 3) (LampRing Δ))) : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
          Matrix (Fin 3) (Fin 3) (LampRing Δ)) ∧
      (∀ i j : Fin 3, hTabEval s (hWordMat L w i j ++ hMatOne i j) = (hMatEval s (hWordMat L w) - 1) i j) ∧
      (wordValue u w = 1 ↔ ∀ i j : Fin 3, ∀ m0 ∈ hWordMat L w i j ++ hMatOne i j, ∀ x : LampSpace Δ,
        hCoeffLC s (wordValue (lampGen s) m0.1) (hWordMat L w i j ++ hMatOne i j) x = 0) ∧
      (wordValue u w = 1 ↔ ∀ i j : Fin 3, ∀ m0 ∈ hWordMat L w i j ++ hMatOne i j,
        ∀ B ∈ subsets (tabU (hWordMat L w i j ++ hMatOne i j)),
          hCoeffLC s (wordValue (lampGen s) m0.1) (hWordMat L w i j ++ hMatOne i j) (xB s B) = 0) := by
  choose L hL using fun x : κ × Bool => exists_hMat_eq s hs
    ((if x.2 then ((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) x.1
      else (((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ))
  refine ⟨coeff_hTabEval s, L, fun w => ?_⟩
  have hsub : wordValue u w = 1 ↔ wordValue ((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) w = 1 := by
    rw [wordValue_map u (elementaryGroup (Fin 3) (LampRing Δ)).subtype w, Subgroup.coe_subtype]
    exact Subtype.val_injective.eq_iff.symm
  refine ⟨?_, fun i j => ?_, ?_, ?_⟩
  · rw [hMatEval_hWordMat s ((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) L hL w,
      wordValue_map u (elementaryGroup (Fin 3) (LampRing Δ)).subtype w, Subgroup.coe_subtype]
  · rw [hTabEval_append, Matrix.sub_apply, ← hMatEval_hMatOne s, hMatEval_apply, hMatEval_apply, sub_eq_add_neg,
      neg_eq_of_add_eq_zero_right (lampRing_add_self (hTabEval s (hMatOne i j)))]
  · rw [hsub, wordValue_eq_one_iff_hTab s _ L hL w]
    exact forall_congr' fun i => forall_congr' fun j => hTabEval_eq_zero_iff s _
  · rw [hsub, wordValue_eq_one_iff_hTab s _ L hL w]
    exact forall_congr' fun i => forall_congr' fun j => hTabEval_eq_zero_iff_subsets s _

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_hostTrivialityCriterion

/-- **So the word problem of `G_Δ` is Turing reducible to that of `Δ`** (tex l.665): for a finite generating family
`s` of `Δ` and any finite family `u` of `G_Δ = EL_3(R_Δ)`, the word problem in `u` is Turing reducible to the word
problem of `Δ` in `s`. -/
theorem manuscriptSentence_hostWordProblemReduction {Δ : Type} [Group Δ] {ι : Type} [Primcodable ι] [Finite ι]
    (s : ι → Δ) (hs : Subgroup.closure (Set.range s) = ⊤) {κ : Type} [Primcodable κ] [Finite κ]
    (u : κ → ↥(elementaryGroup (Fin 3) (LampRing Δ))) :
    TuringReducible (wordProblemOracle u) (wordProblemOracle s) := by
  rw [← wordProblemOracle_comp_injective u (elementaryGroup (Fin 3) (LampRing Δ)).subtype Subtype.val_injective]
  choose L hL using fun x : κ × Bool => exists_hMat_eq s hs
    ((if x.2 then ((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) x.1
      else (((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ))
  exact TuringReducible.trans (turingReducible_units s ((elementaryGroup (Fin 3) (LampRing Δ)).subtype ∘ u) L hL)
    (manuscriptSentence_halflineLambdaWordProblem s).2.2

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_hostWordProblemReduction

end HalflineB
end SimpleKazhdanSofic
end Manuscript
end GroupApproximation
