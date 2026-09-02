import GroupApproximation.GGT.DGOPolygonCutFamily
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Unbound-arc estimates

This file proves the numerical parts of Osin's Appendix Lemmas 61 and 62.
For Lemma 61, the estimating graph has at most `12n` edges, so arcs of types
`A1` and `A2` number at most `29n`, arcs of type `A3` number at most `24n`,
and the total is at most `53n`.

For Lemma 62, if the total unbound length is at least `n * t`, where the
source later takes `t = sqrt rho`, then one complementary component has
unbound length at least its arc count times `t / 60`.  Cutting that component
into a disc gives at most four times as many sides, so the same component has
unbound length at least its side count times `t / 240`.
-/

namespace GroupApproximation
namespace GGT
namespace VanKampen

namespace UnboundEstimate

open DGOPolygonCut
open OsinComponents

universe u w

/-! ## The uniform polygon input used by Lemma 62 -/

/-- The uniform form of DGO Proposition 4.14 needed in Osin's Appendix
Lemma 62.  The dgo414 development currently exposes conditional assembly
theorems rather than this single source-level proposition, so this is the
named target consumed by the estimating-system proof.

The quasi-geodesic constant is the natural number `b` used by the existing
`SumBound` API.  The conclusion is uniform in the number of sides: one
constant `L` bounds the total relative radii by `L * n` for every positive
`n`. -/
def UniformProposition414Statement
    {G : Type u} [Group G] {Λ : Type w}
    (D : RelGenSet G Λ) (b : ℕ) : Prop :=
  (∀ x ∈ D.base, x⁻¹ ∈ D.base) →
    ∀ δ : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ →
      ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n)

/-- The uniform proposition really is a statement about one constant shared
by all polygons, rather than a vacuous packaging: it holds in the one-element
group with the sharp constant `L = 0`. -/
theorem uniformProposition414_pUnit_model
    {Λ : Type w} (D : RelGenSet PUnit Λ) (b : ℕ) :
    UniformProposition414Statement D b := by
  intro _ δ _
  refine ⟨0, ?_⟩
  intro n _ v word cut I lam hletters hclosed hcut hI hedge hcomp hisolated hquasi
  refine ⟨fun _ => 0, ?_, by simp⟩
  intro s hs
  have hspan :
      (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) = 1 :=
    Subsingleton.elim _ _
  rw [hspan]
  exact one_mem_relBall D (lam s) 0

/-- The uniform DGO proposition specializes to the single constant required
throughout the polygon cuts in Lemma 62.  In particular, `L` is chosen before
the number `n` of sides of a complementary component. -/
theorem lemma62_uniformPolygonBound
    {G : Type u} [Group G] {Λ : Type w}
    (D : RelGenSet G Λ) (b : ℕ)
    (h414 : UniformProposition414Statement D b)
    (hsymm : ∀ x ∈ D.base, x⁻¹ ∈ D.base)
    (δ : ℕ) (hδ : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier δ) :
    ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n → SumBound D (b : ℝ) n (L * n) :=
  h414 hsymm δ hδ

/-! ## Lemma 61 -/

/-- Osin Appendix Lemma 61, numerical count.  The hypotheses are the Euler
edge bound and the two arc-type counts obtained after cutting off relator
cells and distinguished contiguity regions. -/
theorem lemma61_arcCount_le
    (n r vertices edges typeA12 typeA3 : ℕ)
    (hn : 0 < n) (hr : r ≤ 4) (hvertices : vertices ≤ n + r)
    (hedges : edges ≤ 3 * (vertices - 1))
    (hA12 : typeA12 ≤ 2 * edges + n + r)
    (hA3 : typeA3 ≤ 2 * edges) :
    typeA12 + typeA3 ≤ 53 * n := by
  have hvertices' : vertices ≤ n + 4 := by omega
  have hedges' : edges ≤ 12 * n := by
    by_cases hverticesZero : vertices = 0
    · omega
    · have hverticesPos : 0 < vertices := Nat.pos_of_ne_zero hverticesZero
      have hnFour : 4 ≤ 4 * n := by omega
      omega
  have hA12' : typeA12 ≤ 29 * n := by omega
  have hA3' : typeA3 ≤ 24 * n := by omega
  omega

/-- The constants in Lemma 61 agree at the smallest permitted cell count:
`29 + 24 = 53` when `n = 1`. -/
theorem lemma61_constant_base : 29 * 1 + 24 * 1 = 53 * 1 := by
  norm_num

/-! ## Lemma 62: averaging -/

/-- If every component has less than its arc count times `t / 60`, then the
total unbound length is less than `n * t`.  The strict margin is the source's
`53 < 60`. -/
theorem total_lt_of_component_lt_sixty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (hcomponent : ∀ i : Fin d,
      unboundLength i < (arcCount i : ℝ) * t / 60) :
    (∑ i : Fin d, unboundLength i) < (n : ℝ) * t := by
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  by_cases hd : d = 0
  · subst d
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact mul_pos hnReal ht
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
  have hsumStrict :
      (∑ i : Fin d, unboundLength i) <
        ∑ i : Fin d, (arcCount i : ℝ) * t / 60 := by
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
      hcomponent i
  have hcastCount :
      (∑ i : Fin d, (arcCount i : ℝ)) ≤ (53 * n : ℕ) := by
    exact_mod_cast hcount
  have hsumRewrite :
      (∑ i : Fin d, (arcCount i : ℝ) * t / 60) =
        (∑ i : Fin d, (arcCount i : ℝ)) * t / 60 := by
    calc
      (∑ i : Fin d, (arcCount i : ℝ) * t / 60) =
          ∑ i : Fin d, (arcCount i : ℝ) * (t / 60) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i : Fin d, (arcCount i : ℝ)) * (t / 60) := by
        rw [Finset.sum_mul]
      _ = (∑ i : Fin d, (arcCount i : ℝ)) * t / 60 := by ring
  rw [hsumRewrite] at hsumStrict
  have hscaled :
      (∑ i : Fin d, (arcCount i : ℝ)) * t / 60 ≤
        (53 * (n : ℝ)) * t / 60 := by
    have htNonneg : 0 ≤ t / 60 := by positivity
    have hcastCount' :
        (∑ i : Fin d, (arcCount i : ℝ)) ≤ 53 * (n : ℝ) := by
      norm_num at hcastCount ⊢
      exact hcastCount
    calc
      (∑ i : Fin d, (arcCount i : ℝ)) * t / 60 =
          (∑ i : Fin d, (arcCount i : ℝ)) * (t / 60) := by ring
      _ ≤ (53 * (n : ℝ)) * (t / 60) :=
        mul_le_mul_of_nonneg_right hcastCount' htNonneg
      _ = (53 * (n : ℝ)) * t / 60 := by ring
  have hmargin : (53 * (n : ℝ)) * t / 60 < (n : ℝ) * t := by
    nlinarith
  exact lt_of_lt_of_le hsumStrict (le_trans hscaled (le_of_lt hmargin))

/-- The finite numerical certificate used by Appendix Lemma `62`: component
arc counts are bounded by `53 * n`, and every component has unbound length
below its `1/60` density threshold. -/
structure Lemma62AveragingCertificate (n d : ℕ) (t : ℝ) where
  n_pos : 0 < n
  t_pos : 0 < t
  arcCount : Fin d → ℕ
  unboundLength : Fin d → ℝ
  arc_count_le : (∑ i : Fin d, arcCount i) ≤ 53 * n
  component_lt : ∀ i : Fin d,
    unboundLength i < (arcCount i : ℝ) * t / 60

/-- A Lemma 62 averaging certificate forces the total unbound length below
`n * t`, with the strict margin `53 < 60`. -/
theorem Lemma62AveragingCertificate.total_lt
    {n d : ℕ} {t : ℝ}
    (certificate : Lemma62AveragingCertificate n d t) :
    (∑ i : Fin d, certificate.unboundLength i) < (n : ℝ) * t := by
  exact total_lt_of_component_lt_sixty n certificate.n_pos t certificate.t_pos
    certificate.arcCount certificate.unboundLength certificate.arc_count_le
    certificate.component_lt

/-- The empty-component certificate is valid at the smallest positive values,
so the averaging leaf has a nonvacuous positive target. -/
theorem lemma62AveragingCertificate_emptyModel :
    Lemma62AveragingCertificate 1 0 1 := by
  refine {
    n_pos := by norm_num
    t_pos := by norm_num
    arcCount := fun i => i.elim
    unboundLength := fun i => i.elim
    arc_count_le := by simp
    component_lt := ?_ }
  intro i
  exact i.elim

/-- Osin Appendix Lemma 62, averaging form: a total of at least `n * t`
forces one component to meet the `1/60` density threshold. -/
theorem exists_component_ge_sixty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (htotal : (n : ℝ) * t ≤ ∑ i : Fin d, unboundLength i) :
    ∃ i : Fin d,
      (arcCount i : ℝ) * t / 60 ≤ unboundLength i := by
  by_contra hnone
  have hcomponent : ∀ i : Fin d,
      unboundLength i < (arcCount i : ℝ) * t / 60 := by
    intro i
    exact lt_of_not_ge fun hi => hnone ⟨i, hi⟩
  have hstrict := total_lt_of_component_lt_sixty n hn t ht arcCount
    unboundLength hcount hcomponent
  linarith

/-- Cutting a component into a disc introduces at most four sides per
original boundary arc, converting the `1/60` density to `1/240`. -/
theorem component_ge_twoForty
    {arcCount sideCount : ℕ} {unboundLength t : ℝ}
    (ht : 0 ≤ t) (hsides : sideCount ≤ 4 * arcCount)
    (hdense : (arcCount : ℝ) * t / 60 ≤ unboundLength) :
    (sideCount : ℝ) * t / 240 ≤ unboundLength := by
  have hsidesReal : (sideCount : ℝ) ≤ 4 * (arcCount : ℝ) := by
    exact_mod_cast hsides
  have htDiv : 0 ≤ t / 240 := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hsidesReal htDiv
  calc
    (sideCount : ℝ) * t / 240 = (sideCount : ℝ) * (t / 240) := by ring
    _ ≤ (4 * (arcCount : ℝ)) * (t / 240) := hscaled
    _ = (arcCount : ℝ) * t / 60 := by ring
    _ ≤ unboundLength := hdense

/-- Combining the averaging and cutting steps gives the exact `1/240`
threshold used before the hyperbolic polygon lemma in Osin's proof. -/
theorem exists_component_ge_twoForty
    {d : ℕ} (n : ℕ) (hn : 0 < n) (t : ℝ) (ht : 0 < t)
    (arcCount sideCount : Fin d → ℕ) (unboundLength : Fin d → ℝ)
    (hcount : (∑ i : Fin d, arcCount i) ≤ 53 * n)
    (hsides : ∀ i, sideCount i ≤ 4 * arcCount i)
    (htotal : (n : ℝ) * t ≤ ∑ i : Fin d, unboundLength i) :
    ∃ i : Fin d,
      (sideCount i : ℝ) * t / 240 ≤ unboundLength i := by
  obtain ⟨i, hi⟩ := exists_component_ge_sixty n hn t ht arcCount
    unboundLength hcount htotal
  exact ⟨i, component_ge_twoForty (le_of_lt ht) (hsides i) hi⟩

/-! ## Quasi-geodesic replacement lengths -/

/-- Replacing each of `m` unbound arcs by a geodesic loses at most `c` per
arc.  If these arcs have total length strictly greater than `k * t / 240`
and `m ≤ k`, their geodesic replacements have total length strictly greater
than `k * (lambda * t / 240 - c)`.  This is the displayed estimate for
`sigma_1` in Osin's proof of Lemma 62. -/
theorem replacement_total_gt
    {m k : ℕ} {lambda c t : ℝ}
    (arcLength replacementLength : Fin m → ℝ)
    (hlambda : 0 < lambda) (hc : 0 ≤ c) (hmk : m ≤ k)
    (hreplacement : ∀ i, lambda * arcLength i - c ≤ replacementLength i)
    (hdense : (k : ℝ) * t / 240 < ∑ i : Fin m, arcLength i) :
    (k : ℝ) * (lambda * t / 240 - c) <
      ∑ i : Fin m, replacementLength i := by
  have hterm :
      ∑ i : Fin m, (lambda * arcLength i - c) ≤
        ∑ i : Fin m, replacementLength i := by
    exact Finset.sum_le_sum fun i _ => hreplacement i
  have hsum :
      ∑ i : Fin m, (lambda * arcLength i - c) =
        lambda * (∑ i : Fin m, arcLength i) - (m : ℝ) * c := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    simp
  have hmkReal : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hmk
  have hpenalty : (m : ℝ) * c ≤ (k : ℝ) * c :=
    mul_le_mul_of_nonneg_right hmkReal hc
  rw [hsum] at hterm
  have hscaled : lambda * ((k : ℝ) * t / 240) <
      lambda * (∑ i : Fin m, arcLength i) :=
    mul_lt_mul_of_pos_left hdense hlambda
  calc
    (k : ℝ) * (lambda * t / 240 - c) =
        lambda * ((k : ℝ) * t / 240) - (k : ℝ) * c := by ring
    _ < lambda * (∑ i : Fin m, arcLength i) - (m : ℝ) * c := by
      linarith
    _ ≤ ∑ i : Fin m, replacementLength i := hterm

/-- If the side arcs have total length at most `eps * k`, the source's
choice `1000 * eps < a` makes their total strictly less than
`10⁻³ * a * k`, as required by Lemma `N123`. -/
theorem side_total_lt_oneThousandth
    {k : ℕ} {eps a sideTotal : ℝ}
    (hk : 0 < k) (hside : sideTotal ≤ eps * (k : ℝ))
    (hchoice : 1000 * eps < a) :
    sideTotal < (1 / 1000 : ℝ) * a * (k : ℝ) := by
  have hkReal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hscale : eps * (k : ℝ) <
      (1 / 1000 : ℝ) * a * (k : ℝ) := by
    nlinarith
  exact lt_of_le_of_lt hside hscale

/-- For positive `lambda`, one natural threshold works for every larger
`rho` in the inequality `B < lambda * sqrt rho / 240 - c`.  This is the
uniform large-`rho` choice used after the displayed `sigma_1` estimate in
Osin's Lemma 62. -/
theorem exists_nat_sqrt_threshold
    (lambda c B : ℝ) (hlambda : 0 < lambda) :
    ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
      B < lambda * Real.sqrt (rho : ℝ) / 240 - c := by
  let threshold : ℝ := 240 * (B + c) / lambda
  obtain ⟨n, hn⟩ := exists_nat_gt (max threshold 0)
  let k : ℕ := n + 1
  have hk : 0 < k := by simp [k]
  refine ⟨k * k, Nat.mul_pos hk hk, ?_⟩
  intro rho hrho
  have hcast : ((k * k : ℕ) : ℝ) ≤ (rho : ℝ) := by
    exact_mod_cast hrho
  have hsqrt := Real.sqrt_le_sqrt hcast
  have hsqrtK : Real.sqrt (((k * k : ℕ) : ℝ)) = (k : ℝ) := by
    rw [Nat.cast_mul]
    have hnonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    calc
      Real.sqrt ((k : ℝ) * (k : ℝ)) =
          Real.sqrt ((k : ℝ) ^ 2) := by ring
      _ = |(k : ℝ)| := Real.sqrt_sq_eq_abs _
      _ = (k : ℝ) := abs_of_nonneg hnonneg
  rw [hsqrtK] at hsqrt
  have hthreshold : threshold < (k : ℝ) := by
    have hmax : threshold < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
    simp only [k, Nat.cast_add, Nat.cast_one]
    linarith
  have hmul : 240 * (B + c) < (k : ℝ) * lambda := by
    exact (div_lt_iff₀ hlambda).mp hthreshold
  have hscaled : (k : ℝ) * lambda ≤ Real.sqrt (rho : ℝ) * lambda :=
    mul_le_mul_of_nonneg_right hsqrt (le_of_lt hlambda)
  nlinarith

/-- For positive `mu`, the final uncovered-budget threshold holds uniformly
for every sufficiently large natural `rho`. -/
theorem exists_two_mu_sqrt_threshold (mu : ℝ) (hmu : 0 < mu) :
    ∃ rho0 : ℕ, 0 < rho0 ∧ ∀ rho : ℕ, rho0 ≤ rho →
      1 ≤ 2 * mu * Real.sqrt (rho : ℝ) := by
  obtain ⟨rho0, hrho0, hthreshold⟩ :=
    exists_nat_sqrt_threshold (2 * mu) 0 1 (mul_pos (by norm_num) hmu)
  refine ⟨rho0, hrho0, ?_⟩
  intro rho hrho
  have hlarge := hthreshold rho hrho
  nlinarith

/-! ### Model checks -/

/-- The replacement estimate is exact in the one-arc zero-loss model. -/
theorem replacement_total_oneArcModel (t : ℝ) :
    (1 : ℝ) * t / 240 < t →
      (1 : ℝ) * ((1 : ℝ) * t / 240 - 0) < t := by
  intro ht
  simpa using replacement_total_gt
    (m := 1) (k := 1) (lambda := 1) (c := 0)
    (fun _ : Fin 1 => t) (fun _ : Fin 1 => t)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro i; simp) (by simpa using ht)

/-- At the smallest positive square, the square-root normalization used by
`exists_nat_sqrt_threshold` is an equality. -/
theorem sqrt_one_base : Real.sqrt ((1 : ℕ) : ℝ) = 1 := by
  norm_num

/-- The cutting conversion is exact at the smallest positive arc count. -/
theorem twoForty_constant_base (t : ℝ) :
    (4 : ℝ) * t / 240 = (1 : ℝ) * t / 60 := by
  ring

end UnboundEstimate

end VanKampen
end GGT
end GroupApproximation
