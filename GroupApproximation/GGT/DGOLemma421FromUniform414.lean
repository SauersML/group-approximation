import GroupApproximation.GGT.DGOLemma421ForwardMatches
import GroupApproximation.GGT.DGOLemma421MatchedBlock

/-!
# DGO Lemma 4.21(b) from uniform Proposition 4.14

The counting argument supplies matches in two quantitatively separated
windows. Initial endpoint closeness and quasi-geodesicity put their targets
in forward order. The minimal-gap quadrilateral fills the intervening ranks
consecutively, giving the literal start-coset conclusion of Lemma 4.21(b).
The one depth threshold is chosen before epsilon and the requested block size.
-/

namespace GroupApproximation.GGT.OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric

universe u w

/-- **Dahmani--Guirardel--Osin Lemma 4.21(b), reduced entirely to uniform
Proposition 4.14.** Both original path basepoints, consecutive maximal
components, and both base-edge-or-trivial separators are retained. -/
theorem dgoLemma421b_of_uniform414
    (h : DGOProposition414Uniform.{u, w}) : DGOLemma421b.{u, w} := by
  intro G _ Lambda D hhyper hbase
  obtain ⟨Ccount, hcount⟩ := dgoLemma421b_locatedAbsorption_of_uniform414 h G Lambda D hhyper hbase
  obtain ⟨CA, hA⟩ := dgoLemma421a_of_uniform414 h G Lambda D hhyper hbase
  obtain ⟨C11, hC11, hsum11, _⟩ := h G Lambda D hhyper hbase 1 1 (by norm_num) (by norm_num)
  obtain ⟨C414, _, _, hproj⟩ := h G Lambda D hhyper hbase 4 1 (by norm_num) (by norm_num)
  let Cgeom := max (50 * C11) (C414 * 4)
  let C := max Ccount (max CA Cgeom)
  have hcountLe : Ccount ≤ C := Nat.le_max_left _ _
  have hALe : CA ≤ C := (Nat.le_max_left CA Cgeom).trans (Nat.le_max_right _ _)
  have hgeomLe : Cgeom ≤ C := (Nat.le_max_right CA Cgeom).trans (Nat.le_max_right _ _)
  have hweak : ∀ {word : List (RelLetter G Lambda)} {R : ℕ}, R ≤ C →
      WWord.IsWTwo D C word → WWord.IsWTwo D R word := by
    intro word R hR hW2 i nu g hread hmem
    exact hW2 i nu g hread (relBall_mono_radius D nu hR hmem)
  refine ⟨C, ?_⟩
  intro eps K heps _hK
  let E := ⌈eps⌉₊
  let M := 2 * E
  let B := 32 * M + 20 * E + K + 89 + M + 1
  have hB : 0 < B := by dsimp [B]; omega
  obtain ⟨R, hR, hall⟩ := hcount eps B heps hB
  refine ⟨R, hR, ?_⟩
  intro vp vq P Q hletP hletQ hW1P hW2P hW3P hW1Q hW2Q hW3Q hRlen hstart hend
  obtain ⟨cert, hpre⟩ := hall vp vq P Q hletP hletQ hW1P (hweak hcountLe hW2P) hW3P
    hW1Q (hweak hcountLe hW2Q) hW3Q hRlen hstart hend
  have hqg : ∀ (v : G) (word : List (RelLetter G Lambda)),
      (∀ letter ∈ word, D.IsLetter letter) → WWord.IsWOne word → WWord.IsWTwo D C word →
      WWord.IsWThree D word → ∀ i j : ℕ, i ≤ j → j ≤ word.length →
        ((j - i : ℕ) : ℝ) / 4 - 1 ≤
          (wordDist D.alphabet.carrier (vertex v word i) (vertex v word j) : ℝ) := by
    intro v word hlet hW1 hW2 hW3 i j hij hj
    have hn := hA v word hlet hW1 (hweak hALe hW2) hW3 i j hij hj
    have hr : ((j - i : ℕ) : ℝ) ≤
        4 * (wordDist D.alphabet.carrier (vertex v word i) (vertex v word j) : ℝ) + 4 := by
      exact_mod_cast hn
    linarith
  have hqgP := hqg vp P hletP hW1P hW2P hW3P
  have hqgQ := hqg vq Q hletQ hW1Q hW2Q hW3Q
  have hsize : 32 * M + 20 * E + K + 89 + M < B * (M + 1) := by
    have hle : B ≤ B * (M + 1) := by
      calc B = B * 1 := by omega
           _ ≤ B * (M + 1) := Nat.mul_le_mul_left B (by omega)
    dsimp [B] at hle ⊢
    omega
  obtain ⟨s, t, a, b, hst, hab, hgap, hlabelA, hlabelB, hmatchA, hmatchB⟩ :=
    cert.exists_forward_matches (E := E) (K := K) hpre hletP hletQ hW1P
      (hstart.trans (Nat.le_ceil eps)) hqgP hqgQ hsize
  obtain ⟨block⟩ := orderedBlockPayload_of_forward_matches_of_uniformBounds hC11 hsum11 hproj
    hbase hletP hletQ hW1P hW1Q (hweak hgeomLe hW2P) (hweak hgeomLe hW2Q)
    hW3P hW3Q hqgP hqgQ hst hab hlabelA hlabelB hmatchA hmatchB hgap
  exact block.toStartCosetWitness

end GroupApproximation.GGT.OsinComponents

#audit_axioms GroupApproximation.GGT.OsinComponents.dgoLemma421b_of_uniform414
