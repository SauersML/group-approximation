import GroupApproximation.GGT.DGOLemma421Proof
import GroupApproximation.GGT.VanKampen.Estimating.UnboundComponentSplit

/-!
# The polygon inputs of Osin Lemma 62

Osin's proof of Appendix Lemma 62 (arXiv `math/0411039`) feeds a geodesic
polygon into two outside results.  This file connects the first of them to
the spelling the repository already owns, and proves the counting step that
prepares the second.

The first is Dahmani--Guirardel--Osin Proposition 4.14.  `Unbound.lean` names
the shape Lemma 62 consumes, `UnboundEstimate.UniformProposition414Statement`,
which asks for one constant `L` with `SumBound D b n (L * n)` for every
positive `n`.  That shape is not a second axiom: it is the specialization of
`OsinComponents.DGOProposition414Uniform` at `mu = 1` and `c = b`, and
`uniformProposition414Statement_of_dgo414` proves it so, with no hypothesis
beyond that proposition.

The second is Ol'shanskii's Lemma 25, which Osin cites under the label
`N123`.  Its printed hypothesis is on the aggregate: the sides of a geodesic
`r`-gon split into three classes with `sigma_1 > a * r` and
`sigma_3 < a * r / 1000`.  Getting from that aggregate to a single long side
is the pigeonhole `exists_side_gt_of_sum_gt` proved here.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen
namespace Estimating

open UnboundEstimate
open DGOPolygonCut

universe u w v

/-! ## Proposition 4.14 in the shape Lemma 62 consumes -/

/-- The uniform polygon bound named in `Unbound.lean` is Dahmani--Guirardel--
Osin Proposition 4.14 at `mu = 1` and `c = b`.  The quasi-geodesic clause of
`SumBound` divides by nothing, and `DGOUniformSumBound` divides by `mu`, so
the two agree at `mu = 1`; the constant `L` is the constant `C` that
Proposition 4.14 produces.

The two statements spell hyperbolicity differently, four-point on the word
metric here and `IsHyperbolicSpace` on the Cayley graph there.
`isHyperbolicSpace_cayley_of_fourPoint` converts one to the other at the same
constant, so this theorem needs no hyperbolicity hypothesis of its own. -/
theorem uniformProposition414Statement_of_dgo414
    {G : Type u} [Group G] {Lambda : Type w}
    (h414 : OsinComponents.DGOProposition414Uniform.{u, w})
    (D : GGT.RelGenSet G Lambda) (b : ℕ) :
    UniformProposition414Statement D b := by
  intro hsymm delta hdelta
  have hhyper : ∃ d : ℝ,
      HullGeometry.IsHyperbolicSpace d
        (Manuscript.NonMF.TorsionFree.Cayley D.alphabet) :=
    ⟨(delta : ℝ), isHyperbolicSpace_cayley_of_fourPoint D.alphabet hdelta⟩
  obtain ⟨C, _hCpos, hsum, _hball⟩ :=
    h414 G Lambda D hhyper hsymm 1 (b : ℝ) (le_refl 1) (Nat.cast_nonneg b)
  refine ⟨C, ?_⟩
  intro n _hn v word cut I lam hletters hclosed hcut hI hedge hcomp hisolated
    hquasi
  refine hsum n v word cut I lam hletters hclosed hcut hI hedge hcomp
    hisolated ?_
  intro s hsn hsI p q hsp hpq hqs
  have hstep := hquasi s hsn hsI p q hsp hpq hqs
  rw [div_one]
  exact hstep

/-! ## From an aggregate class bound to one long side -/

/-- If the sides indexed by `s` have total length above `r * a` and there are
at most `r` of them, one of them is longer than `a`.  This is the step that
turns Ol'shanskii's aggregate hypothesis `sigma_1 > a * r` into the single
long side his conclusion names. -/
theorem exists_side_gt_of_sum_gt {r : ℕ} {a : ℝ} (s : Finset ℕ)
    (len : ℕ → ℝ) (ha : 0 ≤ a) (hcard : s.card ≤ r)
    (hsum : (r : ℝ) * a < ∑ i ∈ s, len i) :
    ∃ i ∈ s, a < len i := by
  by_contra hnone
  have hall : ∀ i ∈ s, len i ≤ a := by
    intro i hi
    by_contra hlt
    exact hnone ⟨i, hi, lt_of_not_ge hlt⟩
  have hbound : (∑ i ∈ s, len i) ≤ (s.card : ℝ) * a := by
    calc
      (∑ i ∈ s, len i) ≤ ∑ _i ∈ s, a := Finset.sum_le_sum hall
      _ = (s.card : ℝ) * a := by simp
  have hcardReal : (s.card : ℝ) ≤ (r : ℝ) := by exact_mod_cast hcard
  have hscaled : (s.card : ℝ) * a ≤ (r : ℝ) * a :=
    mul_le_mul_of_nonneg_right hcardReal ha
  exact absurd hsum (not_lt.mpr (le_trans hbound hscaled))

/-! ## Termination of Ol'shanskii's bisection recursion -/

/-- The balanced cut of `Olshanskii.exists_balanced_cut` leaves two pieces
with strictly fewer sides than the polygon it cut.  The cut runs between a
point on side `a` and a point on side `a + m`, so it splits both of those
sides and appears once in each piece: the pieces have `m + 2` and
`n - m + 2` sides, as `exists_innerCut_polygon` and `exists_outerCut_polygon`
produce them, and the two counts sum to `n + 4` rather than to `n`.

The quarter-separation `n <= 4 * m <= 3 * n` is what makes both counts drop,
and it does so only from nine sides up; `bisection_side_counts_eightGon_stalls`
shows the eight-gon is a genuine fixed point, which is why the recursion's
base case has to cover `n <= 8`. -/
theorem bisection_side_counts_lt {n m : ℕ} (hn : 9 ≤ n)
    (hlow : n ≤ 4 * m) (hhigh : 4 * m ≤ 3 * n) :
    m + 2 < n ∧ n - m + 2 < n ∧ 2 ≤ m + 2 ∧ 2 ≤ n - m + 2 := by
  refine ⟨by omega, by omega, by omega, by omega⟩

/-! ## The subdivision into small polygons -/

/-- **The leaf count of the subdivision is linear.**  Cutting adds four sides
and one piece, so `∑ (r_i - 4)` is unchanged by a cut and still equals
`r - 4` at the leaves; that is the identity `∑ size i + 4 = r + 4 * L` below,
not a weakening.  Every leaf of the bisection has at least five sides, since
only polygons with nine sides or more are cut and both pieces of such a cut
have `m + 2 >= 5` and `n - m + 2 >= 5` sides.  So each leaf contributes at
least one to the potential, and there are at most `r - 4` of them. -/
theorem leafCount_le {L r : ℕ} (size : Fin L → ℕ)
    (hsize : ∀ i, 5 ≤ size i)
    (hpotential : (∑ i : Fin L, size i) + 4 = r + 4 * L) :
    L + 4 ≤ r := by
  have hconst : (∑ _i : Fin L, (5 : ℕ)) = L * 5 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hlower : (∑ _i : Fin L, (5 : ℕ)) ≤ ∑ i : Fin L, size i :=
    Finset.sum_le_sum fun i _ => hsize i
  rw [hconst] at hlower
  omega

/-- The total number of sides over all leaves is below `5 * r`.  With
`∑ size i = r - 4 + 4 * L` and `L + 4 <= r`, the total is at most
`5 * r - 20`. -/
theorem totalSides_le {L r : ℕ} (size : Fin L → ℕ)
    (hsize : ∀ i, 5 ≤ size i)
    (hpotential : (∑ i : Fin L, size i) + 4 = r + 4 * L) :
    (∑ i : Fin L, size i) + 20 ≤ 5 * r := by
  have hL := leafCount_le size hsize hpotential
  omega

/-- **The pigeonhole over the leaves.**  If the first class carries more than
`5 * a * r` in total, some leaf carries more than `a` times its own side
count.  The constant `5` is exactly the `5 * r` bound on the total leaf side
count, so it is pinned by the potential identity rather than chosen. -/
theorem exists_leaf_dense {L r : ℕ} {a : ℝ} (size : Fin L → ℕ)
    (sigma : Fin L → ℝ)
    (hsize : ∀ i, 5 ≤ size i)
    (hpotential : (∑ i : Fin L, size i) + 4 = r + 4 * L)
    (ha : 0 ≤ a)
    (htotal : 5 * a * (r : ℝ) < ∑ i : Fin L, sigma i) :
    ∃ i : Fin L, a * (size i : ℝ) < sigma i := by
  by_contra hnone
  have hnone' : ∀ i : Fin L, sigma i ≤ a * (size i : ℝ) := by
    intro i
    by_contra hlt
    exact hnone ⟨i, lt_of_not_ge hlt⟩
  have hcast : ((∑ i : Fin L, size i : ℕ) : ℝ) = ∑ i : Fin L, (size i : ℝ) := by
    simp
  have hbound : ((∑ i : Fin L, size i : ℕ) : ℝ) + 20 ≤ 5 * (r : ℝ) := by
    exact_mod_cast totalSides_le size hsize hpotential
  have hsize' : (∑ i : Fin L, (size i : ℝ)) ≤ 5 * (r : ℝ) := by
    rw [← hcast]
    linarith
  have hkey : (∑ i : Fin L, sigma i) ≤ a * (5 * (r : ℝ)) := by
    calc (∑ i : Fin L, sigma i) ≤ ∑ i : Fin L, a * (size i : ℝ) :=
          Finset.sum_le_sum fun i _ => hnone' i
      _ = a * ∑ i : Fin L, (size i : ℝ) := by rw [Finset.mul_sum]
      _ ≤ a * (5 * (r : ℝ)) := mul_le_mul_of_nonneg_left hsize' ha
  have heq : (5 : ℝ) * a * (r : ℝ) = a * (5 * (r : ℝ)) := by ring
  linarith

/-! ## Model checks -/

/-- The leaf bound at the smallest polygon the cut accepts: a nine-gon cut at
`m = 3` gives a five-gon and an eight-gon, so `L = 2` and the potential reads
`13 + 4 = 9 + 8`. -/
theorem leafCount_nineGon_model (size : Fin 2 → ℕ)
    (h0 : size 0 = 5) (h1 : size 1 = 8) : (2 : ℕ) + 4 ≤ 9 := by
  refine leafCount_le (r := 9) size ?_ ?_
  · rw [Fin.forall_fin_two, h0, h1]
    exact ⟨le_refl 5, by norm_num⟩
  · rw [Fin.sum_univ_two, h0, h1]

/-- The descent at the smallest polygon it accepts: a nine-gon cut at
`m = 3` leaves a five-gon and an eight-gon. -/
theorem bisection_side_counts_oneStep_model :
    (3 : ℕ) + 2 < 9 ∧ 9 - 3 + 2 < 9 ∧ 2 ≤ 3 + 2 ∧ 2 ≤ 9 - 3 + 2 :=
  bisection_side_counts_lt (n := 9) (m := 3) (by norm_num) (by norm_num)
    (by norm_num)

/-- The eight-gon is a fixed point of the cut, not a case the descent covers:
cutting it at `m = 2` leaves a piece with eight sides again.  So the base case
of the recursion must reach `n = 8`, which is what
`exists_long_close_pair_small_polygon` does. -/
theorem bisection_side_counts_eightGon_stalls : ¬ (8 - 2 + 2 < 8) := by omega

/-- The pigeonhole is exact at one side: a single side of length above `a`
is the only way to beat the total `1 * a`. -/
theorem exists_side_gt_oneSide_model {a : ℝ} (ha : 0 ≤ a) (len : ℕ → ℝ)
    (hlen : a < len 0) :
    ∃ i ∈ ({0} : Finset ℕ), a < len i := by
  refine exists_side_gt_of_sum_gt (r := 1) ({0} : Finset ℕ) len ha ?_ ?_
  · simp
  · simpa using hlen

/-- The pigeonhole has no content when the class is empty and `a` is
positive: the aggregate hypothesis cannot hold. -/
theorem exists_side_gt_empty_model {r : ℕ} {a : ℝ} (ha : 0 < a)
    (len : ℕ → ℝ) :
    ¬ ((r : ℝ) * a < ∑ i ∈ (∅ : Finset ℕ), len i) := by
  intro hsum
  rw [Finset.sum_empty] at hsum
  have hnonneg : (0 : ℝ) ≤ (r : ℝ) * a :=
    mul_nonneg (Nat.cast_nonneg r) (le_of_lt ha)
  exact absurd hsum (not_lt.mpr hnonneg)

end Estimating
end VanKampen
end GGT
end GroupApproximation
