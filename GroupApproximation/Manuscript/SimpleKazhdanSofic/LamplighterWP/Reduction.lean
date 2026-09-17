import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Primrec
import GroupApproximation.Manuscript.SimpleKazhdanSofic.HalflineB.Endpoints
import GroupApproximation.Computability.OracleTruthTable
import GroupApproximation.Meta.AxiomGuard

/-!
# The truth-table reduction of the word problem of `(M₃(R_Δ))ˣ` to that of `Δ`

`simple_kazhdan_sofic_group.tex`, proof of `lem:halfline` (b), l.657–665:

> A word in the generators of $G_\Delta$ multiplies out to a matrix with entries $\sum_\xi p_\xi u_\xi$, where each
> $p_\xi$ is a polynomial over $\F_2$ in finitely many coordinates $x(\delta)$ … After collecting equal $\xi$ and
> equal coordinates, the word is trivial if and only if every coefficient of its difference from $I_3$ vanishes at
> every assignment of its finitely many variables, as $\Omega$ is the full shift. So the word problem of $G_\Delta$
> is Turing reducible to that of $\Delta$.

## Proof route

Let `v : κ → (M₃(R_Δ))ˣ` be a finite family and `t` a finite generating family of `Δ`. Choose tables
`L x : HMat ι` representing the letters `v^{±1}` (`HalflineB.exists_hMat_eq`). For the word coded by `n`,
`HalflineB.hostQ L n` lists the codes of the words `a⁻¹ b` for all pairs of words `a, b` of the tables of the
product `hWordMat L w`, and `HalflineB.hostD L n ans` runs the Boolean decision `matOk` with the answers `ans` looked
up by `look`. Both are primitive recursive (`primrec_hostQ`, `primrec_hostD`). When the answers are those of the
word problem of `Λ` in `lampGen t`, a looked-up answer is `true` iff `ξ_a = ξ_b` (`lookL_map_iff`,
`oracleVal_encode`, `wordValue_wordInv_append`), so `hostD` answers "the word is trivial"
(`HalflineB.wordValue_eq_one_iff_matOk`). This is a truth-table reduction `WP(v) ≤_T WP(Λ)`, and
`WP(Λ) ≤_T WP(Δ)` (`HalflineB.manuscriptSentence_halflineLambdaWordProblem`).
-/

namespace GroupApproximation
namespace SimpleKazhdanSofic
namespace LamplighterWP

open Encodable Lamplighter
open Manuscript.SimpleKazhdanSofic.HalflineB (LW HMat hMatEval hWordMat matTabs matW matOk lookL look pairCodes
  hostQ hostD anyB_eq_true exists_hMat_eq wordValue_eq_one_iff_matOk primrec_hostQ primrec_hostD)

/-- The value of the word problem oracle at a code. -/
noncomputable def oracleVal {ι H : Type} [Group H] [Primcodable ι] (s : ι → H) (q : ℕ) : ℕ :=
  (wordProblemOracle s q).get trivial

theorem oracleVal_encode {ι H : Type} [Group H] [Primcodable ι] (s : ι → H) (x : List (ι × Bool)) :
    oracleVal s (encode x) = 1 ↔ wordValue s x = 1 := by
  simp only [oracleVal, wordProblemOracle, Part.get_some]
  split_ifs with h
  · obtain ⟨w, hw, hw1⟩ := h
    rw [Encodable.encodek, Option.some_inj] at hw
    subst hw
    exact ⟨fun _ => hw1, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 zero_ne_one, fun hx => absurd ⟨x, Encodable.encodek x, hx⟩ h⟩

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.oracleVal_encode

open Classical in
theorem wordProblemOracle_eq_cond {ι H : Type} [Group H] [Primcodable ι] (s : ι → H) (n : ℕ) (b : Bool)
    (h : (∃ w : List (ι × Bool), decode n = some w ∧ wordValue s w = 1) ↔ b = true) :
    wordProblemOracle s n = Part.some (cond b 1 0) := by
  cases b
  · have hn : ¬ ∃ w : List (ι × Bool), decode n = some w ∧ wordValue s w = 1 := fun hw => nomatch h.1 hw
    exact congrArg Part.some (if_neg hn)
  · exact congrArg Part.some (if_pos (h.2 rfl))

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.wordProblemOracle_eq_cond

theorem wordValue_wordInv_append {ι H : Type} [Group H] (s : ι → H) (a b : List (ι × Bool)) :
    wordValue s (wordInv a ++ b) = 1 ↔ wordValue s a = wordValue s b := by
  rw [wordValue_append, wordValue_wordInv, inv_mul_eq_one]

/-- A looked-up answer is the recorded value of the oracle. -/
theorem lookL_map_iff (Q : List ℕ) (g : ℕ → ℕ) {m : ℕ} (hm : m ∈ Q) :
    lookL Q (Q.map g) m = true ↔ g m = 1 := by
  rw [lookL, anyB_eq_true]
  constructor
  · rintro ⟨k, hk, h⟩
    have hk' : k < Q.length := List.mem_range.1 hk
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk', Option.map_some,
      Option.getD_some, Option.getD_some] at h
    rw [← h.1]
    exact h.2
  · intro h
    obtain ⟨k, hk, hkm⟩ := List.getElem_of_mem hm
    refine ⟨k, List.mem_range.2 hk, ?_⟩
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk, Option.map_some,
      Option.getD_some, Option.getD_some, hkm]
    exact ⟨rfl, h⟩

theorem mem_pairCodes {ι : Type} [Primcodable ι] {W : List (LW ι)} {a b : LW ι} (ha : a ∈ W) (hb : b ∈ W) :
    encode (wordInv a ++ b) ∈ pairCodes W :=
  List.mem_flatMap.2 ⟨a, ha, List.mem_map.2 ⟨b, hb, rfl⟩⟩

variable {Δ : Type} [Group Δ] {ι : Type} [Primcodable ι] [Finite ι] {κ : Type} [Primcodable κ] [Finite κ]

/-- The truth table answers the word problem of `v`. -/
theorem hostKey (t : ι → Δ) (v : κ → (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) (L : κ × Bool → HMat ι)
    (hL : ∀ x : κ × Bool, hMatEval t (L x) =
      ((if x.2 then v x.1 else (v x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
        Matrix (Fin 3) (Fin 3) (LampRing Δ))) (n : ℕ) :
    (∃ w : List (κ × Bool), decode n = some w ∧ wordValue v w = 1) ↔
      ((decode (α := List (κ × Bool)) n).isSome &&
        matOk (look (hostQ L n, (hostQ L n).map (oracleVal (lampGen t))))
          (matTabs (hWordMat L ((decode (α := List (κ × Bool)) n).getD [])))) = true := by
  rcases hdec : decode (α := List (κ × Bool)) n with _ | w
  · refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨_, hw, _⟩ := h
      simp at hw
    · simp at h
  · have hQ : hostQ L n = pairCodes (matW (matTabs (hWordMat L w))) := by
      rw [hostQ, hdec, Option.getD_some]
    show _ ↔ matOk (look (hostQ L n, (hostQ L n).map (oracleVal (lampGen t)))) (matTabs (hWordMat L w)) = true
    rw [hQ]
    refine Iff.trans ?_ (wordValue_eq_one_iff_matOk t v L hL w (S := matW (matTabs (hWordMat L w)))
      (fun _ h => h) fun a ha b hb => ?_)
    · exact ⟨fun ⟨w', hw', h1⟩ => by rw [Option.some_inj.1 hw']; exact h1, fun h1 => ⟨w, rfl, h1⟩⟩
    · exact (lookL_map_iff _ (oracleVal (lampGen t)) (mem_pairCodes ha hb)).trans
        ((oracleVal_encode (lampGen t) (wordInv a ++ b)).trans (wordValue_wordInv_append (lampGen t) a b))

/-- **The word problem of a finite family of units of `M₃(R_Δ)` is Turing reducible to that of `Δ`.** -/
theorem unitsReduction (t : ι → Δ) (ht : Subgroup.closure (Set.range t) = ⊤)
    (v : κ → (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
    TuringReducible (wordProblemOracle v) (wordProblemOracle t) := by
  choose L hL using fun x : κ × Bool => exists_hMat_eq t ht
    ((if x.2 then v x.1 else (v x.1)⁻¹ : (Matrix (Fin 3) (Fin 3) (LampRing Δ))ˣ) :
      Matrix (Fin 3) (Fin 3) (LampRing Δ))
  refine TuringReducible.trans ?_
    (Manuscript.SimpleKazhdanSofic.HalflineB.manuscriptSentence_halflineLambdaWordProblem t).2.2
  exact OracleTruthTable.turingReducible_of_truthTable (gt := oracleVal (lampGen t)) (fun _ => rfl)
    (primrec_hostQ L) (primrec_hostD L) fun n => wordProblemOracle_eq_cond v n _ (hostKey t v L hL n)

#audit_axioms GroupApproximation.SimpleKazhdanSofic.LamplighterWP.unitsReduction

end LamplighterWP
end SimpleKazhdanSofic
end GroupApproximation
