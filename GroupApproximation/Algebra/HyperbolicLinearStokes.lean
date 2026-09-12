import GroupApproximation.Algebra.BowditchSlim
import GroupApproximation.Algebra.HyperbolicSlimFourPoint

/-!
# Hyperbolic Cayley graphs satisfy the linear Stokes inequality

The converse direction of Gromov's theorem, in the discrete-integral form used by
this development: if the word metric of a symmetric generating set has `δ`-slim
triangles, the integral of `φ dψ` along a closed path of letters is at most
`4 k² ℓ`, `k = 6 (δ + 1)`, for all functions moving by at most one along every letter.

The proof is Drutu and Kapovich's short-loop induction (*Geometric group theory*,
Proposition 11.147 and Theorem 11.146).  A closed path of length `ℓ > 2 k` either has
a stretch of `k` letters whose endpoints are closer than `k`, or every such stretch is
geodesic.

* In the first case replace the stretch by a geodesic.  The integral splits as the
  integral along the shorter closed path plus the integral along the short loop
  formed by the stretch and the geodesic read backwards (`wordSum_trueLetters_revList`).
  The short loop has length below `2 k`, so its integral is at most `4 k²`.
* In the second case let `v` be a vertex furthest from the base point `v₀`.  It is at
  least `k / 2` letters from both ends, the stretch of `k` letters centred at `v` is
  geodesic, and a point of the opposite side within `δ` of `v` produces a vertex
  further from `v₀` than `v`.
-/

namespace GroupApproximation
namespace DiscreteStokes

open WordMetric

universe v

variable {Q : Type v} [Group Q]

/-- **The integral along a path read backwards is the negative.** -/
theorem wordSum_trueLetters_revList (φ ψ : Q → ℤ) :
    ∀ (b : Q) (p : List Q),
      wordSum (id : Q → Q) φ ψ (b * p.prod) (trueLetters (revList p)) =
        -wordSum (id : Q → Q) φ ψ b (trueLetters p)
  | b, [] => by simp [trueLetters]
  | b, x :: p => by
      have ih := wordSum_trueLetters_revList φ ψ (b * x) p
      have hnil : trueLetters ([] : List Q) = [] := rfl
      have e₁ : b * (x :: p).prod = b * x * p.prod := by
        rw [List.prod_cons, mul_assoc]
      have e₂ : b * x * p.prod * wordVal (id : Q → Q) (trueLetters (revList p)) = b * x := by
        rw [wordVal_trueLetters, prod_revList]
        group
      rw [revList_cons, trueLetters_append, wordSum_append, e₁, ih, e₂]
      simp only [trueLetters_cons, hnil, wordSum_cons, wordSum_nil, letterVal_true, id_eq,
        add_zero]
      rw [mul_inv_cancel_right, edgeTerm_swap φ ψ b (b * x)]
      ring

/-- The square bound along a closed path, for functions Lipschitz along every letter. -/
theorem abs_wordSum_trueLetters_le_of_closed {S : Set Q} {φ ψ : Q → ℤ}
    (hφ : ∀ (g s : Q), s ∈ S → |φ (g * s) - φ g| ≤ 1)
    (hψ : ∀ (g s : Q), s ∈ S → |ψ (g * s) - ψ g| ≤ 1) {l : List Q} (hl : ∀ x ∈ l, x ∈ S)
    (b : Q) (hprod : l.prod = 1) :
    |wordSum (id : Q → Q) φ ψ b (trueLetters l)| ≤ (l.length : ℤ) ^ 2 := by
  have hφ' : LipschitzAlong (id : Q → Q) φ (trueLetters l) := by
    intro x hx g
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact hφ g s (hl s hs)
  have hψ' : LipschitzAlong (id : Q → Q) ψ (trueLetters l) := by
    intro x hx g
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact hψ g s (hl s hs)
  have h := abs_wordSum_le_of_closed (id : Q → Q) (trueLetters l) hφ' hψ' b
    (by rw [wordVal_trueLetters]; exact hprod)
  simpa [trueLetters] using h

/-- Vertices of a path of letters are at most their index difference apart. -/
theorem wordDist_take_le {S : Set Q} {l : List Q} (hl : ∀ x ∈ l, x ∈ S) (b : Q) {i j : ℕ}
    (hij : i ≤ j) : wordDist S (b * (l.take i).prod) (b * (l.take j).prod) ≤ j - i := by
  have hsplit : l.take j = l.take i ++ (l.drop i).take (j - i) := by
    rw [← List.take_add]
    congr 1
    omega
  have e : (b * (l.take i).prod)⁻¹ * (b * (l.take j).prod) = ((l.drop i).take (j - i)).prod := by
    rw [hsplit, List.prod_append]
    group
  unfold wordDist
  rw [e]
  calc wordNorm S ((l.drop i).take (j - i)).prod ≤ ((l.drop i).take (j - i)).length :=
        wordNorm_le_length ⟨fun x hx => hl x (List.mem_of_mem_drop (List.mem_of_mem_take hx)), rfl⟩
    _ ≤ j - i := by
        rw [List.length_take]
        omega

/-- The arithmetic of one shortcut. -/
theorem abs_add_le_of_shortcut {x y : ℤ} {m s n k : ℕ}
    (hx : |x| ≤ ((4 * k ^ 2 : ℕ) : ℤ) * (m : ℤ)) (hy : |y| ≤ (s : ℤ) ^ 2) (hm : m + 1 ≤ n)
    (hs : s ≤ 2 * k) : |x + y| ≤ ((4 * k ^ 2 : ℕ) : ℤ) * (n : ℤ) := by
  have h1 := abs_add_le x y
  have hm' : (m : ℤ) + 1 ≤ n := by exact_mod_cast hm
  have hs' : (s : ℤ) ≤ 2 * k := by exact_mod_cast hs
  have hs0 : (0 : ℤ) ≤ s := Nat.cast_nonneg s
  have hsq : (s : ℤ) ^ 2 ≤ 4 * (k : ℤ) ^ 2 := by nlinarith
  have hmul : 4 * (k : ℤ) ^ 2 * ((m : ℤ) + 1) ≤ 4 * (k : ℤ) ^ 2 * n :=
    mul_le_mul_of_nonneg_left hm' (by positivity)
  push_cast at hx ⊢
  nlinarith

/-- **Slim triangles give the linear Stokes inequality**, at constant `4 k²` with
`k = 6 (δ + 1)`. -/
theorem linearStokes_of_isSlimTriangles {S : Set Q} (hS : IsSymmetricGeneratingSet S) {δ : ℕ}
    (hslim : Hyperbolic.IsSlimTriangles S δ) : LinearStokes S (4 * (6 * (δ + 1)) ^ 2) := by
  intro φ ψ hφ hψ
  have hmain : ∀ (n : ℕ) (l : List Q), l.length = n → (∀ x ∈ l, x ∈ S) → ∀ b : Q,
      l.prod = 1 →
        |wordSum (id : Q → Q) φ ψ b (trueLetters l)| ≤
          ((4 * (6 * (δ + 1)) ^ 2 : ℕ) : ℤ) * (l.length : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro l hlen hl b hprod
    have hclosed := abs_wordSum_trueLetters_le_of_closed hφ hψ hl b hprod
    by_cases hsmall : n ≤ 2 * (6 * (δ + 1))
    · -- a short loop
      have hn0 : (0 : ℤ) ≤ n := Nat.cast_nonneg n
      have h2k : (n : ℤ) ≤ 2 * (6 * ((δ : ℤ) + 1)) := by exact_mod_cast hsmall
      have hδ0 : (0 : ℤ) ≤ δ := Nat.cast_nonneg δ
      rw [hlen] at hclosed ⊢
      push_cast
      have hx : (6 : ℤ) ≤ 6 * ((δ : ℤ) + 1) := by linarith
      have hx2 : 6 * ((δ : ℤ) + 1) ≤ (6 * ((δ : ℤ) + 1)) ^ 2 := by nlinarith
      have hk4 : (n : ℤ) ≤ 4 * (6 * ((δ : ℤ) + 1)) ^ 2 := by linarith
      have hsq : (n : ℤ) ^ 2 ≤ 4 * (6 * ((δ : ℤ) + 1)) ^ 2 * n := by
        rw [sq]
        exact mul_le_mul_of_nonneg_right hk4 hn0
      exact le_trans hclosed hsq
    have hnk : 2 * (6 * (δ + 1)) < n := not_le.mp hsmall
    have hTn : l.take n = l := by
      rw [← hlen, List.take_length]
    by_cases hA : ∃ i, i + 6 * (δ + 1) ≤ n ∧
        wordDist S (b * (l.take i).prod) (b * (l.take (i + 6 * (δ + 1))).prod) < 6 * (δ + 1)
    · -- a stretch that is not geodesic: shortcut it
      obtain ⟨i, hik, hd⟩ := hA
      obtain ⟨p, hp⟩ := exists_isGeodesicWord hS
        ((b * (l.take i).prod)⁻¹ * (b * (l.take (i + 6 * (δ + 1))).prod))
      have hpletters : ∀ x ∈ p, x ∈ S := hp.isWord.letters
      have hplen : p.length < 6 * (δ + 1) := by
        rw [hp.length_eq]
        exact hd
      have hsplit : l = l.take i ++ (l.drop i).take (6 * (δ + 1)) ++ l.drop (i + 6 * (δ + 1)) := by
        rw [← List.take_add, List.take_append_drop]
      have hμprod : b * (l.take i).prod * ((l.drop i).take (6 * (δ + 1))).prod =
          b * (l.take (i + 6 * (δ + 1))).prod := by
        rw [List.take_add, List.prod_append, mul_assoc]
      have hpprod : b * (l.take i).prod * p.prod = b * (l.take (i + 6 * (δ + 1))).prod := by
        rw [hp.isWord.prod_eq]
        group
      have hMp : p.prod = ((l.drop i).take (6 * (δ + 1))).prod :=
        (mul_left_cancel (hμprod.trans hpprod.symm)).symm
      have hl'letters : ∀ x ∈ l.take i ++ p ++ l.drop (i + 6 * (δ + 1)), x ∈ S := by
        intro x hx
        simp only [List.mem_append] at hx
        rcases hx with (hx | hx) | hx
        · exact hl x (List.mem_of_mem_take hx)
        · exact hpletters x hx
        · exact hl x (List.mem_of_mem_drop hx)
      have hl'prod : (l.take i ++ p ++ l.drop (i + 6 * (δ + 1))).prod = 1 := by
        rw [List.prod_append, List.prod_append, hMp, ← List.prod_append, ← List.prod_append,
          ← hsplit]
        exact hprod
      have hσletters : ∀ x ∈ (l.drop i).take (6 * (δ + 1)) ++ revList p, x ∈ S := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hl x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
        · exact letters_revList hS hpletters x hx
      have hσprod : ((l.drop i).take (6 * (δ + 1)) ++ revList p).prod = 1 := by
        rw [List.prod_append, prod_revList, ← hMp, mul_inv_cancel]
      have hsum_l : wordSum (id : Q → Q) φ ψ b (trueLetters l) =
          wordSum (id : Q → Q) φ ψ b (trueLetters (l.take i)) +
            wordSum (id : Q → Q) φ ψ (b * (l.take i).prod)
              (trueLetters ((l.drop i).take (6 * (δ + 1)))) +
            wordSum (id : Q → Q) φ ψ (b * (l.take (i + 6 * (δ + 1))).prod)
              (trueLetters (l.drop (i + 6 * (δ + 1)))) := by
        conv_lhs => rw [hsplit]
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, trueLetters_append,
          wordSum_append, wordVal_trueLetters, List.prod_append, ← mul_assoc, hμprod]
      have hsum_l' : wordSum (id : Q → Q) φ ψ b
          (trueLetters (l.take i ++ p ++ l.drop (i + 6 * (δ + 1)))) =
          wordSum (id : Q → Q) φ ψ b (trueLetters (l.take i)) +
            wordSum (id : Q → Q) φ ψ (b * (l.take i).prod) (trueLetters p) +
            wordSum (id : Q → Q) φ ψ (b * (l.take (i + 6 * (δ + 1))).prod)
              (trueLetters (l.drop (i + 6 * (δ + 1)))) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, trueLetters_append,
          wordSum_append, wordVal_trueLetters, List.prod_append, ← mul_assoc, hpprod]
      have hsum_σ : wordSum (id : Q → Q) φ ψ (b * (l.take i).prod)
          (trueLetters ((l.drop i).take (6 * (δ + 1)) ++ revList p)) =
          wordSum (id : Q → Q) φ ψ (b * (l.take i).prod)
              (trueLetters ((l.drop i).take (6 * (δ + 1)))) -
            wordSum (id : Q → Q) φ ψ (b * (l.take i).prod) (trueLetters p) := by
        rw [trueLetters_append, wordSum_append, wordVal_trueLetters, ← hMp,
          wordSum_trueLetters_revList, sub_eq_add_neg]
      have hsplit_sum : wordSum (id : Q → Q) φ ψ b (trueLetters l) =
          wordSum (id : Q → Q) φ ψ b (trueLetters (l.take i ++ p ++ l.drop (i + 6 * (δ + 1)))) +
            wordSum (id : Q → Q) φ ψ (b * (l.take i).prod)
              (trueLetters ((l.drop i).take (6 * (δ + 1)) ++ revList p)) := by
        rw [hsum_l, hsum_l', hsum_σ]
        ring
      have hl'len : (l.take i ++ p ++ l.drop (i + 6 * (δ + 1))).length + 1 ≤ n := by
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
      have hσlen : ((l.drop i).take (6 * (δ + 1)) ++ revList p).length ≤ 2 * (6 * (δ + 1)) := by
        simp only [List.length_append, List.length_take, List.length_drop, length_revList]
        omega
      have hIH := ih _ (by omega) (l.take i ++ p ++ l.drop (i + 6 * (δ + 1))) rfl hl'letters b
        hl'prod
      have hσ := abs_wordSum_trueLetters_le_of_closed hφ hψ hσletters (b * (l.take i).prod)
        hσprod
      rw [hsplit_sum, hlen]
      exact abs_add_le_of_shortcut hIH hσ hl'len hσlen
    · -- every stretch of `k` letters is geodesic: impossible
      exfalso
      have hgeo : ∀ i, i + 6 * (δ + 1) ≤ n →
          wordDist S (b * (l.take i).prod) (b * (l.take (i + 6 * (δ + 1))).prod) =
            6 * (δ + 1) := by
        intro i hik
        have h1 := not_lt.mp (fun h => hA ⟨i, hik, h⟩)
        have h2 := wordDist_take_le hl b (show i ≤ i + 6 * (δ + 1) by omega)
        omega
      obtain ⟨t, ht, htmax⟩ := Finset.exists_max_image (Finset.range (n + 1))
        (fun t => wordDist S b (b * (l.take t).prod)) ⟨0, by simp⟩
      rw [Finset.mem_range] at ht
      have hmax : ∀ s, s ≤ n →
          wordDist S b (b * (l.take s).prod) ≤ wordDist S b (b * (l.take t).prod) :=
        fun s hs => htmax s (Finset.mem_range.mpr (by omega))
      -- the furthest vertex is far from both ends
      have hk0 := hgeo 0 (by omega)
      simp only [List.take_zero, List.prod_nil, mul_one, zero_add] at hk0
      have hkn := hgeo (n - 6 * (δ + 1)) (by omega)
      have e₁ : n - 6 * (δ + 1) + 6 * (δ + 1) = n := by omega
      rw [e₁, hTn, hprod, mul_one, wordDist_comm hS] at hkn
      have hmaxk := hmax (6 * (δ + 1)) (by omega)
      have hmaxnk := hmax (n - 6 * (δ + 1)) (by omega)
      have hstart : wordDist S b (b * (l.take t).prod) ≤ t := by
        have h := wordDist_take_le hl b (Nat.zero_le t)
        simpa using h
      have hend : wordDist S b (b * (l.take t).prod) ≤ n - t := by
        have h := wordDist_take_le hl b (show t ≤ n by omega)
        rw [hTn, hprod, mul_one, wordDist_comm hS] at h
        exact h
      have ht₁ : 3 * (δ + 1) ≤ t := by omega
      have ht₂ : t + 3 * (δ + 1) ≤ n := by omega
      -- the geodesic stretch centred at the furthest vertex
      have hg := hgeo (t - 3 * (δ + 1)) (by omega)
      have e₂ : t - 3 * (δ + 1) + 6 * (δ + 1) = t + 3 * (δ + 1) := by omega
      rw [e₂] at hg
      have hd₁ := wordDist_take_le hl b (show t - 3 * (δ + 1) ≤ t by omega)
      have hd₂ := wordDist_take_le hl b (show t ≤ t + 3 * (δ + 1) by omega)
      have htri := wordDist_triangle hS (b * (l.take (t - 3 * (δ + 1))).prod)
        (b * (l.take t).prod) (b * (l.take (t + 3 * (δ + 1))).prod)
      have hbetween : Hyperbolic.IsBetween S (b * (l.take (t - 3 * (δ + 1))).prod)
          (b * (l.take t).prod) (b * (l.take (t + 3 * (δ + 1))).prod) := by
        unfold Hyperbolic.IsBetween
        omega
      have hmaxm := hmax (t - 3 * (δ + 1)) (by omega)
      have hmaxp := hmax (t + 3 * (δ + 1)) ht₂
      rcases hslim _ _ b _ hbetween with ⟨q, hq, hqd⟩ | ⟨q, hq, hqd⟩
      · unfold Hyperbolic.IsBetween at hq
        have h1 := wordDist_triangle hS b q (b * (l.take t).prod)
        have h2 := wordDist_comm hS q (b * (l.take t).prod)
        have h3 := wordDist_triangle hS (b * (l.take (t - 3 * (δ + 1))).prod) q
          (b * (l.take t).prod)
        have h4 := wordDist_comm hS q b
        have h5 := wordDist_comm hS b (b * (l.take (t - 3 * (δ + 1))).prod)
        omega
      · unfold Hyperbolic.IsBetween at hq
        have h1 := wordDist_triangle hS b q (b * (l.take t).prod)
        have h2 := wordDist_comm hS q (b * (l.take t).prod)
        have h3 := wordDist_triangle hS (b * (l.take t).prod) q
          (b * (l.take (t + 3 * (δ + 1))).prod)
        omega
  intro l hl b hprod
  exact hmain l.length l rfl hl b hprod

/-- **Four-point hyperbolicity gives the linear Stokes inequality.** -/
theorem linearStokes_of_isFourPointHyperbolic {S : Set Q} (hS : IsSymmetricGeneratingSet S)
    {δ : ℕ} (hδ : Hyperbolic.IsFourPointHyperbolic S δ) :
    LinearStokes S (4 * (6 * (4 * δ + 1)) ^ 2) :=
  linearStokes_of_isSlimTriangles hS (Hyperbolic.isSlimTriangles_of_isFourPointHyperbolic hS hδ)

end DiscreteStokes
end GroupApproximation

#audit_axioms GroupApproximation.DiscreteStokes.wordSum_trueLetters_revList
#audit_axioms GroupApproximation.DiscreteStokes.wordDist_take_le
#audit_axioms GroupApproximation.DiscreteStokes.linearStokes_of_isSlimTriangles
#audit_axioms GroupApproximation.DiscreteStokes.linearStokes_of_isFourPointHyperbolic
