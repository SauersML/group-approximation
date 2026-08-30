import GroupApproximation.Algebra.MorseLemma
import GroupApproximation.GGT.HyperbolicFreeGroupAH

/-!
# The power orbit of a loxodromic element is a quasi-geodesic

`Hyperbolic.IsQuasiGeodesic S K C n p` asks for two bounds on `d(p i, p j)`:
above by `K (j - i) + C`, and below in the form `j - i ≤ K (d(p i, p j) + C)`.
For `p i = g ^ i` in the word metric of `A` both come straight out of the
definition of loxodromy, and this module supplies the constants.

* **Above.**  `d(g^i, g^j) = |g^{j-i}|_A ≤ (j - i) · |g|_A` by iterated
  subadditivity (`wordNorm_pow_le_mul`).  So `|g|_A` serves as `K`, with `C = 0`.
* **Below.**  Loxodromy says `l·k - B ≤ d(1, g^k · 1)`, and the displacement of
  the basepoint of a Cayley graph *is* the word length
  (`GGT.dist_base_smul`), so `l·k ≤ |g^k|_A + B` and `k ≤ (1/l)(|g^k|_A + B)`.
  Rounding both constants up gives `⌈1/l⌉₊` and `⌈B⌉₊`.

One `K` has to serve both bounds, so the constant returned is
`max |g|_A ⌈1/l⌉₊`, with `C = ⌈B⌉₊`.

## Why this is the shape wanted

`Hyperbolic.MorseLemma` is stated against `IsQuasiGeodesic`, and
`GGT/HullSCConeOffHeavyChordChain.lean` derives from it that every point between
`p 0` and `p n` is near some `p m`.  Composed with this module, the prefixes of
an `A`-geodesic word for `g ^ n` are uniformly near `⟨g⟩`, which is the
quasiconvexity that `GGT/HullSCConeOffHeavyHyperbolic.lean` feeds to
`GGT.OsinEnlargement.osinLemma55`.

The constants are uniform in `n`: the same `K` and `C` work for every length,
which is what lets a single `σ` serve the quasiconvexity predicate.

## Degenerate cases

At `k = 0` both bounds read `0 ≤ C` and `0 ≤ K · C`, so nothing is asserted; the
content is at `k ≥ 1`.  The hypothesis is genuinely used: an elliptic `g` has
`|g^k|_A` bounded, and then no `K, C` can satisfy the lower bound, which is why
`l > 0` appears in the denominator rather than as a side condition.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u

/-! ## Powers grow at most linearly -/

/-- **Iterated subadditivity.**  A `k`-th power has word length at most `k`
times the word length of the base.  `GGT.wordNorm_pow_le` is the special case of
a letter, where `|g|_A ≤ 1`. -/
theorem wordNorm_pow_le_mul {G : Type u} [Group G] {S : Set G}
    (hS : IsSymmetricGeneratingSet S) (g : G) (k : ℕ) :
    wordNorm S (g ^ k) ≤ k * wordNorm S g := by
  induction k with
  | zero =>
      have h0 : wordNorm S (g ^ 0) = 0 := by rw [pow_zero, wordNorm_one]
      omega
  | succ k ih =>
      have hstep : wordNorm S (g ^ (k + 1)) ≤ wordNorm S (g ^ k) + wordNorm S g := by
        rw [pow_succ]
        exact wordNorm_mul_le hS (g ^ k) g
      have hring : (k + 1) * wordNorm S g = k * wordNorm S g + wordNorm S g := by
        ring
      omega

/-! ## The power orbit -/

/-- **The power orbit of a loxodromic element is a quasi-geodesic**, with
constants uniform in the length.

See the module header for where the two constants come from.  The upper bound is
`wordNorm_pow_le_mul`; the lower bound is loxodromy read through
`GGT.dist_base_smul`, which turns the displacement of the basepoint into a word
length so that the real inequality can be cast back to `ℕ`. -/
theorem exists_isQuasiGeodesic_pow_of_isLoxodromic {G : Type u} [Group G]
    (A : Alphabet G) {g : G} (hlox : IsLoxodromic g (Cayley.base A)) :
    ∃ K C : ℕ, ∀ n : ℕ,
      Hyperbolic.IsQuasiGeodesic A.carrier K C n (fun i => g ^ i) := by
  obtain ⟨l, hl, B, hB, hlin⟩ := hlox
  refine ⟨wordNorm A.carrier g + ⌈1 / l⌉₊, ⌈B⌉₊, ?_⟩
  intro n i _hi j _hj hij
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  have hsub : i + k - i = k := by omega
  have hval : wordDist A.carrier (g ^ i) (g ^ (i + k))
      = wordNorm A.carrier (g ^ k) := by
    show wordNorm A.carrier ((g ^ i)⁻¹ * g ^ (i + k)) = wordNorm A.carrier (g ^ k)
    rw [pow_add, inv_mul_cancel_left]
  rw [hsub, hval]
  constructor
  · have hup := wordNorm_pow_le_mul A.symmetricGenerating g k
    have hmax : wordNorm A.carrier g ≤ wordNorm A.carrier g + ⌈1 / l⌉₊ :=
      Nat.le_add_right _ _
    have hmul : k * wordNorm A.carrier g
        ≤ (wordNorm A.carrier g + ⌈1 / l⌉₊) * k := by
      rw [Nat.mul_comm k]
      exact Nat.mul_le_mul_right k hmax
    omega
  · have hd : dist (Cayley.base A) ((g ^ k) • Cayley.base A)
        = ((wordNorm A.carrier (g ^ k) : ℕ) : ℝ) := GGT.dist_base_smul A (g ^ k)
    have hlk := hlin k
    rw [hd] at hlk
    have hw0 : (0 : ℝ) ≤ ((wordNorm A.carrier (g ^ k) : ℕ) : ℝ) := by positivity
    have hceil1 : 1 / l ≤ ((⌈1 / l⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hceilB : B ≤ ((⌈B⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hstep1 : (k : ℝ)
        ≤ (1 / l) * (((wordNorm A.carrier (g ^ k) : ℕ) : ℝ) + B) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl]
      have hcomm : (k : ℝ) * l = l * (k : ℝ) := by ring
      rw [hcomm]
      linarith
    have hstep2 : (1 / l) * (((wordNorm A.carrier (g ^ k) : ℕ) : ℝ) + B)
        ≤ ((⌈1 / l⌉₊ : ℕ) : ℝ)
          * (((wordNorm A.carrier (g ^ k) : ℕ) : ℝ) + ((⌈B⌉₊ : ℕ) : ℝ)) := by
      refine mul_le_mul hceil1 (by linarith) (by linarith) ?_
      have hpos : (0 : ℝ) ≤ 1 / l := by positivity
      linarith
    have hKcast : ((⌈1 / l⌉₊ : ℕ) : ℝ)
        ≤ ((wordNorm A.carrier g + ⌈1 / l⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left ⌈1 / l⌉₊ (wordNorm A.carrier g)
    have hstep3 : ((⌈1 / l⌉₊ : ℕ) : ℝ)
          * (((wordNorm A.carrier (g ^ k) : ℕ) : ℝ) + ((⌈B⌉₊ : ℕ) : ℝ))
        ≤ ((wordNorm A.carrier g + ⌈1 / l⌉₊ : ℕ) : ℝ)
          * (((wordNorm A.carrier (g ^ k) : ℕ) : ℝ) + ((⌈B⌉₊ : ℕ) : ℝ)) := by
      refine mul_le_mul_of_nonneg_right hKcast ?_
      have hc0 : (0 : ℝ) ≤ ((⌈B⌉₊ : ℕ) : ℝ) := by positivity
      linarith
    have hfinal : (k : ℝ)
        ≤ (((wordNorm A.carrier g + ⌈1 / l⌉₊)
            * (wordNorm A.carrier (g ^ k) + ⌈B⌉₊) : ℕ) : ℝ) := by
      push_cast at hstep3 ⊢
      linarith
    exact_mod_cast hfinal

end HullSC
end GroupApproximation
