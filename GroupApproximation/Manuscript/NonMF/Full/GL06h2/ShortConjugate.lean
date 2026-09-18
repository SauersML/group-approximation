import GroupApproximation.Manuscript.NonMF.Full.GL06h2.Statement
import GroupApproximation.Manuscript.NonMF.Full.GL06h2.Progress
import GroupApproximation.Manuscript.NonMF.Full.GL06h2.Conjugate
import GroupApproximation.Manuscript.NonMF.Full.GL06h2.QuasiGeodesicWord

/-!
# GL06h2: a short word is never a conjugate of a relator value

Osin, arXiv:math/0411039v3, §9, proof of Lemma 9.7(b).  Infrastructure for `thm:hull`
(non_mf_groups_exist.tex ~2121, Hull's small cancellation theorem, through Osin's Lemma 9.7).

Let `word ∈ W` have length `n ≥ ρ`, split at `h = n/2`, and put `x = [word]`,
`a = [word.take h]`.  Both halves are long by the quasi-geodesic clause.  The Morse lemma
(`GGT.exists_chainAt_hausdorff_bound`) on `word` bounds the excess of `a` between `1` and `x`, and
on the rotation `word.rotate h ∈ W` (translated by `a`) the excess of `x` between `a` and `x a`.
`progress_halfChain` then gives `|x^m| ≥ m (2ε + 2)`, which excludes a conjugate of norm `≤ 2ε`
(`false_of_linear_progress_of_conj`).

* `shortWord_ne_conj_relator`: the theorem, with the hypothesis list of GL06e.
* `shortWordNeConjRelatorStatement_holds`: the Prop of `Full/GL06h2/Statement`.
-/

namespace GroupApproximation.Full.GL06h2

universe u w

open GroupApproximation.WordMetric
open GroupApproximation.GGT
open GroupApproximation.GGT.VanKampen

/-- **A short word is not a conjugate of a relator value** (Osin, proof of Lemma 9.7(b);
`thm:hull`, non_mf_groups_exist.tex ~2121).  Beyond the thresholds, no word of length at most
`ε + ε` over the symmetric label alphabet spells a conjugate of the value of a relator. -/
theorem shortWord_ne_conj_relator {G : Type u} [Group G] {Lambda : Type w}
    (D : RelGenSet G Lambda)
    (hD : ∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lambda c mu : ℝ) (hlam : 0 < lambda) (_hlam1 : lambda ≤ 1) (_hc : 0 ≤ c) (_hmu : 0 < mu)
    (_hmu16 : mu ≤ 1 / 16) :
    ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps →
      ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
        ∀ (W : Set (List (RelLetter G Lambda))),
          OsinCCondition D W eps mu lambda c rho →
            ∀ word ∈ W, RelLetter.listVal word ≠ 1 →
              ∀ (g : G) (u : List (RelLetter G Lambda)),
                (∀ x ∈ u, (symmetricLabelAlphabet D).IsLetter x) →
                u.length ≤ eps + eps →
                  RelLetter.listVal u ≠ g * RelLetter.listVal word * g⁻¹ := by
  obtain ⟨delta, hdelta⟩ := hD
  have hS : IsSymmetricGeneratingSet D.alphabet.carrier := D.alphabet.symmetricGenerating
  obtain ⟨R, hR⟩ := exists_chainAt_hausdorff_bound D.alphabet.carrier (1 / lambda) ⌈c⌉₊ delta
    (one_div_pos.mpr hlam)
  refine ⟨0, fun eps _heps => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = 2 * R + 2 * delta + eps + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈((L : ℝ) + c) / lambda⌉₊ := ⟨_, rfl⟩
  have hKc : ((L : ℝ) + c) / lambda ≤ K := by
    rw [hK]
    exact Nat.le_ceil _
  refine ⟨2 * K + 2, by omega, fun rho hrho W hW word hword _hne g u hu hulen heq => ?_⟩
  have hmorse : ∀ v ∈ W, ∀ i : ℕ, i ≤ v.length →
      wordDist D.alphabet.carrier 1 (OsinComponents.vertex 1 v i) +
          wordDist D.alphabet.carrier (OsinComponents.vertex 1 v i) (RelLetter.listVal v) ≤
        wordDist D.alphabet.carrier 1 (RelLetter.listVal v) + 2 * R := by
    intro v hv i hi
    have hchain := chainAt_of_quasiGeodesicWord D (hW.quasiGeodesic v hv)
    obtain ⟨p, hp, hpR⟩ := (hR (OsinComponents.vertex 1 v) v.length hS hdelta hchain).1 i hi
    rw [OsinComponents.vertex_zero, vertex_length_eq_listVal] at hp
    exact local_of_between hS hp hpR
  have hlong : 2 * K + 2 ≤ word.length := le_trans hrho (hW.long word hword)
  obtain ⟨half, hhalf⟩ : ∃ half : ℕ, half = word.length / 2 := ⟨_, rfl⟩
  have hhn : half ≤ word.length := by omega
  have hq := hW.quasiGeodesic word hword
  obtain ⟨x, hx⟩ : ∃ x : G, x = RelLetter.listVal word := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : G, a = RelLetter.listVal (word.take half) := ⟨_, rfl⟩
  have hva : OsinComponents.vertex 1 word half = a := by
    rw [OsinComponents.vertex_eq_mul_listVal_take word 1 half, one_mul, ha]
  have hvx : OsinComponents.vertex 1 word word.length = x := by
    rw [vertex_length_eq_listVal, hx]
  have hedge1 : L ≤ wordDist D.alphabet.carrier 1 a := by
    have hK1 : K ≤ half - 0 := by omega
    have h1 := long_vertexDist_of_quasiGeodesic D hlam hq hKc (Nat.zero_le half) hhn hK1
    rw [OsinComponents.vertex_zero, hva] at h1
    exact h1
  have hedge2 : L ≤ wordDist D.alphabet.carrier a x := by
    have hK2 : K ≤ word.length - half := by omega
    have h1 := long_vertexDist_of_quasiGeodesic D hlam hq hKc hhn le_rfl hK2
    rw [hva, hvx] at h1
    exact h1
  have hloc1 : wordDist D.alphabet.carrier 1 a + wordDist D.alphabet.carrier a x ≤
      wordDist D.alphabet.carrier 1 x + 2 * R := by
    have h1 := hmorse word hword half hhn
    rw [hva, ← hx] at h1
    exact h1
  have hrot : word.rotate half ∈ W := hW.rotate_mem word hword half
  have hbi : word.length - half ≤ (word.rotate half).length := by
    rw [List.length_rotate]
    exact Nat.sub_le _ _
  have hdropval : RelLetter.listVal (word.drop half) = a⁻¹ * x := by
    have hsplit : a * RelLetter.listVal (word.drop half) = x := by
      rw [ha, hx, ← HullSC.RelWord.listVal_append, List.take_append_drop]
    rw [← hsplit, inv_mul_cancel_left]
  have hvb : OsinComponents.vertex 1 (word.rotate half) (word.length - half) = a⁻¹ * x := by
    have hlen : (word.drop half).length = word.length - half := List.length_drop
    rw [OsinComponents.vertex_eq_mul_listVal_take, one_mul,
      List.rotate_eq_drop_append_take hhn, ← hlen, List.take_append_of_le_length le_rfl,
      List.take_length, hdropval]
  have hval' : RelLetter.listVal (word.rotate half) = a⁻¹ * x * a := by
    rw [HullSC.RelWord.listVal_rotate word hhn, ← ha, ← hx]
  have e1 : wordDist D.alphabet.carrier 1 (a⁻¹ * x) = wordDist D.alphabet.carrier a x := by
    have h1 := wordDist_left_invariant D.alphabet.carrier a 1 (a⁻¹ * x)
    rw [mul_one, mul_inv_cancel_left] at h1
    exact h1.symm
  have e2 : wordDist D.alphabet.carrier (a⁻¹ * x) (a⁻¹ * x * a) =
      wordDist D.alphabet.carrier 1 a := by
    have h1 := wordDist_left_invariant D.alphabet.carrier (a⁻¹ * x) 1 a
    rw [mul_one] at h1
    exact h1
  have e3 : wordDist D.alphabet.carrier 1 (a⁻¹ * x * a) =
      wordDist D.alphabet.carrier a (x * a) := by
    have h1 := wordDist_left_invariant D.alphabet.carrier a 1 (a⁻¹ * x * a)
    have hxa : a * (a⁻¹ * x * a) = x * a := by group
    rw [mul_one, hxa] at h1
    exact h1.symm
  have hloc2 : wordDist D.alphabet.carrier a x + wordDist D.alphabet.carrier 1 a ≤
      wordDist D.alphabet.carrier a (x * a) + 2 * R := by
    have h1 := hmorse (word.rotate half) hrot (word.length - half) hbi
    rw [hvb, hval', e1, e2, e3] at h1
    exact h1
  have hgap : 2 * (R + delta) < L := by omega
  have hprog : ∀ m : ℕ, m * (eps + eps + 1) ≤ wordNorm D.alphabet.carrier (x ^ m) := by
    intro m
    have h1 := progress_halfChain D.alphabet hdelta hedge1 hedge2 hloc1 hloc2 hgap m
    have hsub : L - 2 * (R + delta) = eps + 1 := by omega
    rw [hsub] at h1
    calc m * (eps + eps + 1) ≤ m * (eps + eps + 1) + m := Nat.le_add_right _ _
      _ = 2 * m * (eps + 1) := by ring
      _ ≤ wordNorm D.alphabet.carrier (x ^ m) := h1
  have hshort : wordNorm D.alphabet.carrier (RelLetter.listVal u) < eps + eps + 1 := by
    have h1 := wordNorm_listVal_le_of_symmetricLabel D u hu
    omega
  rw [← hx] at heq
  exact false_of_linear_progress_of_conj hS hprog hshort heq

/-- The Prop `ShortWordNeConjRelatorStatement` holds (Osin, proof of Lemma 9.7(b); `thm:hull`,
non_mf_groups_exist.tex ~2121). -/
theorem shortWordNeConjRelatorStatement_holds : ShortWordNeConjRelatorStatement.{u, w} := by
  intro G _ Lambda D hD lambda c mu hlam hlam1 hc hmu hmu16
  exact shortWord_ne_conj_relator D hD lambda c mu hlam hlam1 hc hmu hmu16

end GroupApproximation.Full.GL06h2
