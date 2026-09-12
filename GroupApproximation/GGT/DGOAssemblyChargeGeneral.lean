import GroupApproximation.GGT.DGOAssemblyCharge

/-!
# General quasi-geodesic estimates on auxiliary cycles

Restriction, coordinate changes and geodesic chords preserve the original
parameters. All connector edges belong to the distinguished target set.
The additive parameter of the path record is only bookkeeping.
-/

namespace GroupApproximation.GGT.DGOPolygonCut

open GroupApproximation.GGT.OsinComponents
open GroupApproximation.WordMetric

universe u w
variable {G : Type u} [Group G] {Λ : Type w}

/-- Restrict the genuine estimate to a named inherited subarc. -/
theorem IsCutPath.arcWord_quasi_at {D : RelGenSet G Λ} {b : ℝ} {n : ℕ} {v : G}
    {w : List (RelLetter G Λ)} {c : ℕ → ℕ}
    (P : IsCutPath D b n v w c) (mu err : ℝ) (parentTarget : Finset ℕ)
    (hquasi : ∀ s : ℕ, s < n → s ∉ parentTarget →
      ∀ i j : ℕ, c s ≤ i → i ≤ j → j ≤ c (s + 1) →
      ((j - i : ℕ) : ℝ) / mu - err ≤
        ((wordDist D.alphabet.carrier (vertex v w i) (vertex v w j) : ℕ) : ℝ))
    {a z leftLength : ℕ} (haz : a ≤ z) (hzn : z ≤ n)
    (localTarget : Finset ℕ)
    (hreflect : ∀ r : ℕ, r < z - a → a + r ∈ parentTarget →
      leftLength + r ∈ localTarget) :
    ∀ r : ℕ, r < z - a → leftLength + r ∉ localTarget →
      ∀ i j : ℕ,
      c (a + r) - c a ≤ i → i ≤ j → j ≤ c (a + (r + 1)) - c a →
      ((j - i : ℕ) : ℝ) / mu - err ≤
        ((wordDist D.alphabet.carrier
          (vertex (vertex v w (c a)) (DGOPolygonCut.arcWord w c a z) i)
          (vertex (vertex v w (c a)) (DGOPolygonCut.arcWord w c a z) j) : ℕ) : ℝ) := by
  intro r hr hrTarget i j hi hij hj
  have har : a + r < n := by omega
  have hnotParent : a + r ∉ parentTarget := by
    intro hmem
    exact hrTarget (hreflect r hr hmem)
  have hca : c a ≤ c (a + r) := P.cut.mono_le (by omega)
  have hca1 : c a ≤ c (a + (r + 1)) := P.cut.mono_le (by omega)
  have hi' : c (a + r) ≤ c a + i := by omega
  have hj' : c a + j ≤ c ((a + r) + 1) := by
    have heq : a + (r + 1) = (a + r) + 1 := by omega
    rw [← heq]
    omega
  have hq := hquasi (a + r) har hnotParent (c a + i) (c a + j)
    hi' (by omega) hj'
  have hcz : c (a + (r + 1)) ≤ c z :=
    P.cut.mono_le (by omega)
  have hiLen : i ≤ c z - c a := by omega
  have hjLen : j ≤ c z - c a := by omega
  rw [vertex_arcWord w v c hiLen, vertex_arcWord w v c hjLen]
  have hdiff : c a + j - (c a + i) = j - i := by omega
  simpa only [hdiff] using hq

/-- Auxiliary cycles retain the genuine general quasi-geodesic estimate. -/
theorem quasi_auxiliaryCycleWord_at (D : RelGenSet G Λ) {b : ℝ}
    (mu err : ℝ) (hmu : 1 ≤ mu) (herr : 0 ≤ err)
    (v : G) (left arc right chord : List (RelLetter G Λ)) {nArc : ℕ}
    {arcCut : ℕ → ℕ}
    (harc : IsCutPath D b nArc
      (v * RelLetter.listVal (revWord left)) arc arcCut)
    {g : G} (hchord : IsGeodesicWord D
      (v * RelLetter.listVal ((revWord left ++ arc) ++ right)) g chord)
    (Target : Finset ℕ)
    (harcQuasi : ∀ r : ℕ, r < nArc → left.length + r ∉ Target →
      ∀ p q : ℕ, arcCut r ≤ p → p ≤ q → q ≤ arcCut (r + 1) →
      ((q - p : ℕ) : ℝ) / mu - err ≤
        ((wordDist D.alphabet.carrier
          (vertex (v * RelLetter.listVal (revWord left)) arc p)
          (vertex (v * RelLetter.listVal (revWord left)) arc q) : ℕ) : ℝ))
    (hleft : ∀ r : ℕ, r < left.length → r ∈ Target)
    (hright : ∀ r : ℕ, r < right.length →
      left.length + nArc + r ∈ Target) :
    ∀ s : ℕ, s < left.length + nArc + right.length + chord.length →
      s ∉ Target → ∀ p q : ℕ,
      auxiliaryCycleCut left nArc arcCut right s ≤ p →
      p ≤ q →
      q ≤ auxiliaryCycleCut left nArc arcCut right (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - err ≤
        ((wordDist D.alphabet.carrier
          (vertex v (auxiliaryCycleWord left arc right chord) p)
          (vertex v (auxiliaryCycleWord left arc right chord) q) : ℕ) : ℝ) := by
  intro s hs hsTarget p q hp hpq hq
  by_cases hsLeft : s < left.length
  · exact False.elim (hsTarget (hleft s hsLeft))
  by_cases hsArc : s < left.length + nArc
  · let r := s - left.length
    have hr : r < nArc := by dsimp [r]; omega
    have hsEq : s = left.length + r := by dsimp [r]; omega
    have hs1Eq : s + 1 = left.length + (r + 1) := by omega
    have hcut0 := auxiliaryCycleCut_arc left right harc.cut (le_of_lt hr)
    have hcut1 := auxiliaryCycleCut_arc left right harc.cut (by omega : r + 1 ≤ nArc)
    rw [hsEq, hcut0] at hp
    rw [hs1Eq, hcut1] at hq
    have hpArc : arcCut r ≤ p - left.length := by omega
    have hpqArc : p - left.length ≤ q - left.length := by omega
    have hqArc : q - left.length ≤ arcCut (r + 1) := by omega
    have hpLen : p - left.length ≤ arc.length := by
      have := harc.cut.le_length (by omega : r + 1 ≤ nArc)
      omega
    have hqLen : q - left.length ≤ arc.length := by
      have := harc.cut.le_length (by omega : r + 1 ≤ nArc)
      omega
    have hpEq : left.length + (p - left.length) = p := by omega
    have hqEq : left.length + (q - left.length) = q := by omega
    have hdiff : q - left.length - (p - left.length) = q - p := by omega
    have hrTarget : left.length + r ∉ Target := by
      simpa only [hsEq] using hsTarget
    have hqa := harcQuasi r hr hrTarget (p - left.length)
      (q - left.length) hpArc hpqArc hqArc
    rw [hdiff] at hqa
    have hvp :
        vertex v (auxiliaryCycleWord left arc right chord) p =
          vertex (v * RelLetter.listVal (revWord left)) arc
            (p - left.length) := by
      conv_lhs => rw [← hpEq]
      rw [vertex_auxiliaryCycle_arc v left arc right chord hpLen]
    have hvq :
        vertex v (auxiliaryCycleWord left arc right chord) q =
          vertex (v * RelLetter.listVal (revWord left)) arc
            (q - left.length) := by
      conv_lhs => rw [← hqEq]
      rw [vertex_auxiliaryCycle_arc v left arc right chord hqLen]
    rw [hvp, hvq]
    exact hqa
  by_cases hsRight : s < left.length + nArc + right.length
  · let r := s - (left.length + nArc)
    have hr : r < right.length := by dsimp [r]; omega
    have hsEq : left.length + nArc + r = s := by dsimp [r]; omega
    have ht := hright r hr
    rw [hsEq] at ht
    exact False.elim (hsTarget ht)
  · let r := s - (left.length + nArc + right.length)
    have hr : r < chord.length := by dsimp [r]; omega
    have hsEq : s = left.length + nArc + right.length + r := by dsimp [r]; omega
    have hs1Eq : s + 1 = left.length + nArc + right.length + (r + 1) := by omega
    have hcut0 := auxiliaryCycleCut_chord left right harc.cut (r := r)
    have hcut1 := auxiliaryCycleCut_chord left right harc.cut (r := r + 1)
    rw [hsEq, hcut0] at hp
    rw [hs1Eq, hcut1] at hq
    let off := left.length + arc.length + right.length
    have hpqChord : p - off ≤ q - off := by omega
    have hqLen : q - off ≤ chord.length := by omega
    have hpEq : off + (p - off) = p := by dsimp [off]; omega
    have hqEq : off + (q - off) = q := by dsimp [off]; omega
    have hdiff : q - off - (p - off) = q - p := by omega
    have hgeo := sub_le_wordDist_vertex D hchord (p - off) (q - off)
      hpqChord hqLen
    have hgeoR : (((q - p : ℕ) : ℝ)) ≤
        ((wordDist D.alphabet.carrier
          (vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right))
            chord (p - off))
          (vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right))
            chord (q - off)) : ℕ) : ℝ) := by
      rw [← hdiff]
      exact_mod_cast hgeo
    have hvp :
        vertex v (auxiliaryCycleWord left arc right chord) p =
          vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right))
            chord (p - off) := by
      conv_lhs => rw [← hpEq]
      simp only [off]
      rw [vertex_auxiliaryCycle_chord]
    have hvq :
        vertex v (auxiliaryCycleWord left arc right chord) q =
          vertex (v * RelLetter.listVal ((revWord left ++ arc) ++ right))
            chord (q - off) := by
      conv_lhs => rw [← hqEq]
      simp only [off]
      rw [vertex_auxiliaryCycle_chord]
    rw [hvp, hvq]
    have hdivide : ((q - p : ℕ) : ℝ) / mu ≤ ((q - p : ℕ) : ℝ) :=
      div_le_self (Nat.cast_nonneg _) hmu
    linarith

end GroupApproximation.GGT.DGOPolygonCut

#audit_axioms GroupApproximation.GGT.DGOPolygonCut.IsCutPath.arcWord_quasi_at
#audit_axioms GroupApproximation.GGT.DGOPolygonCut.quasi_auxiliaryCycleWord_at
