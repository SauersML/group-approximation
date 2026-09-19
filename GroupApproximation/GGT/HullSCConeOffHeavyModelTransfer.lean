import GroupApproximation.GGT.HullSCConeOffHeavyLemma67
import GroupApproximation.GGT.HullSCConeOffHeavyModelPoint

/-!
# B2's leaf, moved into the geodesic model

`GGT/HullSCConeOffHeavyLemma67.lean` reduced B2 to `MatchedPowersForceCommonPower`,
a word-metric statement about a whole family.  `GGT/HullSCConeOffHeavyModelPoint.lean`
named the geometric statement that should replace it,
`UniformCommonZpowThreshold`, which mentions no family, no alphabet and no word
metric.  This module proves the first from the second.

What that buys is a change of audience.  The remaining leaf is now a statement
about a hyperbolic geodesic space, two elements and a point, with the threshold
in front of all three — dischargeable by whoever owns the fellow-travel core,
with no knowledge of Hull's construction, elementary closures or cone-offs.

## The translation

Everything is normalised by `(g μ)^{-i}`, so that the first orbit starts at the
identity vertex and the model basepoint is fixed once and for all.  Write
`t' = (g μ)^{-i} t`.  The four points become

* the first orbit, `1` and `(g μ)^{j-i}`, at the basepoint `z = modelPoint A 1`;
* the second, `t' (g λ)^k` and `t' (g λ)^l`, which is the orbit of
  `b = t' (g λ) t'⁻¹` based at `w = modelPoint A (t' (g λ)^k)`.

`z` and `w` are within `B + 1`, and that single bound carries the whole
argument.  It is why `b` may be measured at `z` rather than at `w`: every
quantity that a naive reading fears is unbounded in `t` — the displacement
`dist z (b • z)`, the additive loxodromy constant of `b` at `z` — is bounded by
its value at `w`, which is conjugation-invariant, plus twice `dist z w`.  That
comparison is `dist_shift_of_close_basepoint` below, and it is used three times.

## The constants

`b`'s data at `z` is `(l, B_g + 2B + 3, D_g + 2B + 3)` against `g λ`'s
`(l, B_g, D_g)`, and the first orbit's is `(l, B_g + 1, D_g + 1)`: one for the
distortion of the vertex map, two more for the basepoint shift, and the rest for
the `B` the matching hypothesis allows.  The separation needed is
`⌈T⌉₊ + 4B + 4`; the `4B` is spent twice, once pulling the second orbit's own
length down to the first's and once shifting its basepoint.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G]

/-- **Displacement at a nearby basepoint.**  Moving the basepoint by `D` costs
`2D` in the displacement of any element, in either direction.  This is what
makes conjugation-invariant data usable at a basepoint that is not on the
element's own axis. -/
theorem dist_shift_of_close_basepoint {X : Type u} [PseudoMetricSpace X]
    [MulAction G X] (hiso : IsIsometricAction G X) {D : ℝ} {z w : X}
    (hzw : dist z w ≤ D) (c : G) :
    dist w (c • w) - 2 * D ≤ dist z (c • z) := by
  have h1 := dist_triangle4 w z (c • z) (c • w)
  have h2 : dist (c • z) (c • w) = dist z w := hiso c z w
  have h3 : dist w z = dist z w := dist_comm _ _
  rw [h2, h3] at h1
  linarith

/-- **The word-metric leaf follows from the geometric one.** -/
theorem matchedPowersForceCommonPower_of_uniformThreshold {Λ : Type w}
    (A : Alphabet G) (g : Λ → G) (hulox : UniformlyLoxodromic A g)
    (hunif : UniformCommonZpowThreshold G (CayleyGeodesicModel.PointQuot A)) :
    MatchedPowersForceCommonPower A g := by
  obtain ⟨la, Ba, Da, hla0, -, -, hdata⟩ := hulox
  intro B
  obtain ⟨T, hT⟩ := hunif (2 * (B : ℝ) + 2) la (Ba + 1) (Da + 1) la
    (Ba + 2 * (B : ℝ) + 3) (Da + 2 * (B : ℝ) + 3) hla0 hla0
  refine ⟨⌈T⌉₊ + 4 * B + 4, ?_⟩
  intro t lam mu i j k l hsep hik hjl
  have hisoW := CayleyGeodesicModel.isIsometricAction_pointQuot A
  have hB0 : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hTceil : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
  obtain ⟨tt, htt⟩ : ∃ s : G, s = (g mu) ^ (-i) * t := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ s : G, s = tt * (g lam) * tt⁻¹ := ⟨_, rfl⟩
  -- exponent bookkeeping
  have hmuinv : ∀ q : ℤ, (g mu) ^ (-i) * (g mu) ^ q = (g mu) ^ (q - i) := by
    intro q; rw [← zpow_add]; congr 1; ring
  have hlaminv : ∀ q : ℤ, (g lam) ^ (-k) * (g lam) ^ q = (g lam) ^ (q - k) := by
    intro q; rw [← zpow_add]; congr 1; ring
  -- the four word-metric identities of the normalisation
  have hW1 : wordDist A.carrier 1 ((g mu) ^ (j - i))
      = wordDist A.carrier ((g mu) ^ i) ((g mu) ^ j) := by
    have h := wordDist_left_invariant A.carrier ((g mu) ^ (-i)) ((g mu) ^ i)
      ((g mu) ^ j)
    rw [hmuinv i, hmuinv j] at h
    simpa using h
  have hW2 : wordDist A.carrier 1 (tt * (g lam) ^ k)
      = wordDist A.carrier ((g mu) ^ i) (t * (g lam) ^ k) := by
    have h := wordDist_left_invariant A.carrier ((g mu) ^ (-i)) ((g mu) ^ i)
      (t * (g lam) ^ k)
    rw [hmuinv i, ← mul_assoc, ← htt] at h
    simpa using h
  have hW3 : wordDist A.carrier ((g mu) ^ (j - i)) (tt * (g lam) ^ l)
      = wordDist A.carrier ((g mu) ^ j) (t * (g lam) ^ l) := by
    have h := wordDist_left_invariant A.carrier ((g mu) ^ (-i)) ((g mu) ^ j)
      (t * (g lam) ^ l)
    rw [hmuinv j, ← mul_assoc, ← htt] at h
    exact h
  have hW4 : ∀ q : ℤ,
      wordDist A.carrier (tt * (g lam) ^ k) (tt * (g lam) ^ (k + q))
        = wordDist A.carrier 1 ((g lam) ^ q) := by
    intro q
    rw [wordDist_left_invariant]
    have h := wordDist_left_invariant A.carrier ((g lam) ^ (-k)) ((g lam) ^ k)
      ((g lam) ^ (k + q))
    rw [hlaminv k, hlaminv (k + q)] at h
    simp only [sub_self, zpow_zero, add_sub_cancel_left] at h
    exact h.symm
  -- the two orbits in the model
  have horba : ∀ q : ℤ,
      ((g mu) ^ q) • modelPoint A 1 = modelPoint A ((g mu) ^ q) := by
    intro q; rw [smul_modelPoint, mul_one]
  have horbaN : ∀ n : ℕ,
      ((g mu) ^ n) • modelPoint A 1 = modelPoint A ((g mu) ^ n) := by
    intro n; rw [smul_modelPoint, mul_one]
  have horbb : ∀ q : ℤ, (b ^ q) • modelPoint A (tt * (g lam) ^ k)
      = modelPoint A (tt * (g lam) ^ (k + q)) := by
    intro q
    rw [smul_modelPoint]
    congr 1
    rw [hb, conj_zpow, mul_assoc, inv_mul_cancel_left, mul_assoc, ← zpow_add,
      add_comm q k]
  -- the one bound that carries the argument
  have hzw : dist (modelPoint A 1) (modelPoint A (tt * (g lam) ^ k))
      ≤ (B : ℝ) + 1 := by
    have h1 := dist_modelPoint_le A 1 (tt * (g lam) ^ k)
    have h2 : (wordDist A.carrier 1 (tt * (g lam) ^ k) : ℝ) ≤ (B : ℝ) := by
      rw [hW2]; exact_mod_cast hik
    linarith
  have hshift := dist_shift_of_close_basepoint hisoW hzw
  -- loxodromy data for the first orbit
  have hloxa : ∀ n : ℕ, la * n - (Ba + 1)
      ≤ dist (modelPoint A 1) (((g mu) ^ n) • modelPoint A 1) := by
    intro n
    rw [horbaN n]
    have h := le_dist_modelPoint A 1 ((g mu) ^ n)
    linarith [(hdata mu).1 n]
  have hdispa : dist (modelPoint A 1) ((g mu) • modelPoint A 1) ≤ Da + 1 := by
    have hpt : (g mu) • modelPoint A 1 = modelPoint A (g mu) := by
      rw [smul_modelPoint, mul_one]
    rw [hpt]
    have h := dist_modelPoint_le A 1 (g mu)
    linarith [(hdata mu).2]
  -- loxodromy data for the second orbit, at the first orbit's basepoint
  have hloxb : ∀ n : ℕ, la * n - (Ba + 2 * (B : ℝ) + 3)
      ≤ dist (modelPoint A 1) ((b ^ n) • modelPoint A 1) := by
    intro n
    have hw := hshift (b ^ (n : ℤ))
    rw [horbb (n : ℤ)] at hw
    have hlow := le_dist_modelPoint A (tt * (g lam) ^ k)
      (tt * (g lam) ^ (k + (n : ℤ)))
    rw [hW4 (n : ℤ), zpow_natCast] at hlow
    rw [← zpow_natCast b n]
    linarith [(hdata lam).1 n]
  have hdispb : dist (modelPoint A 1) (b • modelPoint A 1)
      ≤ Da + 2 * (B : ℝ) + 3 := by
    have hb1 : b • modelPoint A (tt * (g lam) ^ k)
        = modelPoint A (tt * (g lam) ^ (k + 1)) := by
      have h := horbb 1
      rwa [zpow_one] at h
    have h1 := dist_triangle4 (modelPoint A 1) (modelPoint A (tt * (g lam) ^ k))
      (b • modelPoint A (tt * (g lam) ^ k)) (b • modelPoint A 1)
    have h2 : dist (b • modelPoint A (tt * (g lam) ^ k)) (b • modelPoint A 1)
        = dist (modelPoint A (tt * (g lam) ^ k)) (modelPoint A 1) := hisoW b _ _
    have h3 : dist (modelPoint A (tt * (g lam) ^ k)) (modelPoint A 1)
        = dist (modelPoint A 1) (modelPoint A (tt * (g lam) ^ k)) := dist_comm _ _
    rw [h2, h3, hb1] at h1
    have hup := dist_modelPoint_le A (tt * (g lam) ^ k) (tt * (g lam) ^ (k + 1))
    rw [hW4 1, zpow_one] at hup
    linarith [(hdata lam).2]
  -- the two length hypotheses and the endpoint bound
  have hcastsep : ((⌈T⌉₊ : ℝ) + 4 * (B : ℝ) + 4)
      ≤ (wordDist A.carrier ((g mu) ^ i) ((g mu) ^ j) : ℝ) := by
    exact_mod_cast hsep
  have h5 : T ≤ dist (modelPoint A 1) (((g mu) ^ (j - i)) • modelPoint A 1) := by
    rw [horba (j - i)]
    have h := le_dist_modelPoint A 1 ((g mu) ^ (j - i))
    rw [hW1] at h
    linarith
  have hsepbN : ⌈T⌉₊ + 2 * B + 4
      ≤ wordDist A.carrier (tt * (g lam) ^ k) (tt * (g lam) ^ l) := by
    have t1 := wordDist_triangle A.symmetricGenerating 1 (tt * (g lam) ^ k)
      ((g mu) ^ (j - i))
    have t2 := wordDist_triangle A.symmetricGenerating (tt * (g lam) ^ k)
      (tt * (g lam) ^ l) ((g mu) ^ (j - i))
    have e1 : wordDist A.carrier 1 (tt * (g lam) ^ k) ≤ B := by
      rw [hW2]; exact hik
    have e2 : wordDist A.carrier (tt * (g lam) ^ l) ((g mu) ^ (j - i)) ≤ B := by
      rw [wordDist_comm A.symmetricGenerating, hW3]; exact hjl
    have e3 : ⌈T⌉₊ + 4 * B + 4 ≤ wordDist A.carrier 1 ((g mu) ^ (j - i)) := by
      rw [hW1]; exact hsep
    omega
  have hkl : k + (l - k) = l := by ring
  have h6 : T ≤ dist (modelPoint A 1) ((b ^ (l - k)) • modelPoint A 1) := by
    have hw := hshift (b ^ (l - k))
    rw [horbb (l - k), hkl] at hw
    have hlow := le_dist_modelPoint A (tt * (g lam) ^ k) (tt * (g lam) ^ l)
    have hcast : ((⌈T⌉₊ : ℝ) + 2 * (B : ℝ) + 4)
        ≤ (wordDist A.carrier (tt * (g lam) ^ k) (tt * (g lam) ^ l) : ℝ) := by
      exact_mod_cast hsepbN
    linarith
  have h7 : dist (((g mu) ^ (j - i)) • modelPoint A 1)
      ((b ^ (l - k)) • modelPoint A 1) ≤ 2 * (B : ℝ) + 2 := by
    rw [horba (j - i)]
    have h3 : (b ^ (l - k)) • modelPoint A (tt * (g lam) ^ k)
        = modelPoint A (tt * (g lam) ^ l) := by rw [horbb (l - k), hkl]
    have h1 := dist_triangle (modelPoint A ((g mu) ^ (j - i)))
      ((b ^ (l - k)) • modelPoint A (tt * (g lam) ^ k))
      ((b ^ (l - k)) • modelPoint A 1)
    have h2 : dist ((b ^ (l - k)) • modelPoint A (tt * (g lam) ^ k))
        ((b ^ (l - k)) • modelPoint A 1)
        = dist (modelPoint A (tt * (g lam) ^ k)) (modelPoint A 1) := hisoW _ _ _
    have hcomm : dist (modelPoint A (tt * (g lam) ^ k)) (modelPoint A 1)
        = dist (modelPoint A 1) (modelPoint A (tt * (g lam) ^ k)) := dist_comm _ _
    rw [h2, hcomm, h3] at h1
    have hup := dist_modelPoint_le A ((g mu) ^ (j - i)) (tt * (g lam) ^ l)
    rw [hW3] at hup
    have hjlR : (wordDist A.carrier ((g mu) ^ j) (t * (g lam) ^ l) : ℝ)
        ≤ (B : ℝ) := by exact_mod_cast hjl
    linarith
  -- the geometric leaf, and the return to the original conjugator
  obtain ⟨p, r, hp, hr, hpr⟩ := hT (g mu) b (modelPoint A 1) hloxa hdispa hloxb
    hdispb (j - i) (l - k) h5 h6 h7
  refine ⟨r, p, hr, hp, ?_⟩
  rw [hb, conj_zpow, htt] at hpr
  have hX : (g mu) ^ i * ((g mu) ^ p) * (g mu) ^ (-i) = t * (g lam) ^ r * t⁻¹ := by
    rw [hpr]; group
  have hpow : (g mu) ^ i * ((g mu) ^ p) * (g mu) ^ (-i) = (g mu) ^ p := by
    rw [← zpow_add, ← zpow_add]; congr 1; ring
  exact hX.symm.trans hpow

end HullSC
end GroupApproximation
