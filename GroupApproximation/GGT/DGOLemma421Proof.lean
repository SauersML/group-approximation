import GroupApproximation.GGT.DGOLemma421Statement
import GroupApproximation.GGT.DGOPolygonCutFamily

/-!
# DGO Lemma 4.21 from the uniform isolated-component sum bound

Dahmani--Guirardel--Osin Proposition 4.14 states that, in a weakly relatively
hyperbolic group, the total relative length of distinguished isolated
components in an `n`-gon is bounded by `C(μ,c) n` when all other sides are
`(μ,c)`-quasi-geodesic.  `DGOUniformSumBound` is that conclusion in the
radius-witness form used by `DGOPolygonCut.SumBound`, and
`DGOProposition414Uniform` keeps the source's quantifier order.

The rest of this module proves DGO Lemma 4.21(b) from that uniform bound.
-/

namespace GroupApproximation
namespace GGT
namespace OsinComponents

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric
open GroupApproximation.GGT.DGOPolygonCut

universe u w

variable {G : Type u} [Group G] {Λ : Type w}

/-- **The conclusion of DGO Proposition 4.14 at fixed parameters.**

This is Definition 4.13 and Proposition 4.14 written with a radius witness.
The distinguished sides are isolated components and every other side is
`(μ,c)`-quasi-geodesic.  One radius function bounds all distinguished spans,
and its total is at most `C n`. -/
def DGOUniformSumBound (D : RelGenSet G Λ) (mu c : ℝ) (C : ℕ) : Prop :=
  ∀ (n : ℕ) (v : G) (word : List (RelLetter G Λ))
      (cut : ℕ → ℕ) (I : Finset ℕ) (lam : ℕ → Λ),
    (∀ a ∈ word, D.IsLetter a) →
    RelLetter.listVal word = 1 →
    IsPolygonCut n word cut →
    (∀ s ∈ I, s < n) →
    (∀ s ∈ I, cut (s + 1) = cut s + 1) →
    (∀ s ∈ I, IsComp (lam s) word (cut s) (cut (s + 1))) →
    (∀ s ∈ I, IsIsolated D.fam (lam s) v word (cut s)) →
    (∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ,
      cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex v word p) (vertex v word q) : ℕ) : ℝ)) →
    ∃ r : ℕ → ℕ,
      (∀ s ∈ I,
        (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1))
          ∈ D.relBall (lam s) (r s)) ∧
      ∑ s ∈ I, r s ≤ C * n

/-- **Dahmani--Guirardel--Osin Proposition 4.14, with uniformity in `n`.**

The quantifier order is the one printed in Proposition 4.14: after the group,
relative structure, and weak-hyperbolicity hypothesis are fixed, arbitrary
`μ ≥ 1` and `c ≥ 0` determine one positive constant `C(μ,c)` which works for
every `n`-gon. -/
def DGOProposition414Uniform : Prop :=
  ∀ (G : Type u) [Group G] (Λ : Type w) (D : RelGenSet G Λ),
    (∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet)) →
    ∀ mu c : ℝ, 1 ≤ mu → 0 ≤ c →
      ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound D mu c C

/-- The uniform Proposition 4.14 statement specializes to the landed
`(1,0)` sum-bound interface. -/
theorem exists_sumBound_zero_of_uniform414
    (h : DGOProposition414Uniform.{u, w}) (D : RelGenSet G Λ)
    (hhyp : ∃ delta : ℝ, IsHyperbolicSpace delta (Cayley D.alphabet)) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, SumBound D 0 n (C * n) := by
  obtain ⟨C, hC, hbound⟩ := h G Λ D hhyp 1 0 le_rfl le_rfl
  refine ⟨C, hC, ?_⟩
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  apply hbound n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso
  intro s hs hsI p q hp hpq hq
  simpa using hquasi s hs hsI p q hp hpq hq

/-! ## Model test for the uniform-bound payload -/

/-- The relative structure on the trivial group with one trivial peripheral
member.  Keeping a genuine peripheral index makes the model test non-vacuous. -/
private def trivialUniformRelGenSet : RelGenSet PUnit Unit where
  base := Set.univ
  fam := fun _ => ⊤
  symmetricGenerating := by
    have h := Hyperbolic.isSymmetricGeneratingSet_univ (G := PUnit)
    rw [Finset.coe_univ] at h
    simpa only [Set.univ_union] using h

/-- In the one-point model every distinguished span is the identity, so the
uniform sum bound holds with radius zero for every parameter and constant. -/
theorem dgoUniformSumBound_trivialModel (mu c : ℝ) (C : ℕ) :
    DGOUniformSumBound trivialUniformRelGenSet mu c C := by
  intro n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  refine ⟨fun _ => 0, ?_, by simp⟩
  intro s hs
  have hspan :
      (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1)) = 1 :=
    Subsingleton.elim _ _
  rw [hspan]
  exact one_mem_relBall trivialUniformRelGenSet (lam s) 0

/-- The positive uniform constant required by Proposition 4.14 exists in the
nonempty-peripheral trivial model. -/
theorem dgoProposition414Uniform_trivialModel (mu c : ℝ)
    (_hmu : 1 ≤ mu) (_hc : 0 ≤ c) :
    ∃ C : ℕ, 0 < C ∧ DGOUniformSumBound trivialUniformRelGenSet mu c C := by
  exact ⟨1, Nat.zero_lt_one, dgoUniformSumBound_trivialModel mu c 1⟩

/-! ## Counting deep isolated singleton sides -/

/-- **The counting consequence of Proposition 4.14 at an arbitrary cut.**

If the distinguished singleton sides all lie outside the relative ball of
radius `B`, every radius witness supplied by Proposition 4.14 is at least
`B+1`.  Summing gives `(B+1)|I| ≤ Cn`. -/
theorem deepIsolated_card_bound
    {D : RelGenSet G Λ} {mu c : ℝ} {C B n : ℕ}
    (hbound : DGOUniformSumBound D mu c C)
    {v : G} {word : List (RelLetter G Λ)} {cut : ℕ → ℕ}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hclosed : RelLetter.listVal word = 1)
    (hcut : IsPolygonCut n word cut)
    (I : Finset ℕ) (lam : ℕ → Λ)
    (hI : ∀ s ∈ I, s < n)
    (hedge : ∀ s ∈ I, cut (s + 1) = cut s + 1)
    (hcomp : ∀ s ∈ I, IsComp (lam s) word (cut s) (cut (s + 1)))
    (hiso : ∀ s ∈ I, IsIsolated D.fam (lam s) v word (cut s))
    (hquasi : ∀ s : ℕ, s < n → s ∉ I → ∀ p q : ℕ,
      cut s ≤ p → p ≤ q → q ≤ cut (s + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex v word p) (vertex v word q) : ℕ) : ℝ))
    (hdeep : ∀ s ∈ I,
      (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1))
        ∉ D.relBall (lam s) B) :
    (B + 1) * I.card ≤ C * n := by
  obtain ⟨r, hrmem, hrsum⟩ :=
    hbound n v word cut I lam hlet hclosed hcut hI hedge hcomp hiso hquasi
  have hrLarge : ∀ s ∈ I, B + 1 ≤ r s := by
    intro s hs
    by_contra hnot
    have hrle : r s ≤ B := by omega
    have hmono : D.relBall (lam s) (r s) ⊆ D.relBall (lam s) B :=
      RelGenSet.relBall_mono_radius D hrle
    exact hdeep s hs (hmono (hrmem s hs))
  calc
    (B + 1) * I.card = ∑ _s ∈ I, (B + 1) := by
      rw [Finset.sum_const_nat]
      exact Nat.mul_comm _ _
    _ ≤ ∑ s ∈ I, r s := by
      exact Finset.sum_le_sum fun s hs => hrLarge s hs
    _ ≤ C * n := hrsum

/-- A deep singleton side of an `n`-gon cannot be isolated once its depth
threshold is at least the Proposition 4.14 bound `C n`. -/
theorem not_isolated_singleton_of_uniformBound
    {D : RelGenSet G Λ} {mu c : ℝ} {C n : ℕ}
    (hbound : DGOUniformSumBound D mu c C)
    {v : G} {word : List (RelLetter G Λ)} {cut : ℕ → ℕ}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hclosed : RelLetter.listVal word = 1)
    (hcut : IsPolygonCut n word cut)
    {s : ℕ} (hs : s < n) {lam : Λ}
    (hedge : cut (s + 1) = cut s + 1)
    (hcomp : IsComp lam word (cut s) (cut (s + 1)))
    (hquasi : ∀ t : ℕ, t < n → t ≠ s → ∀ p q : ℕ,
      cut t ≤ p → p ≤ q → q ≤ cut (t + 1) →
      ((q - p : ℕ) : ℝ) / mu - c ≤
        ((wordDist D.alphabet.carrier
          (vertex v word p) (vertex v word q) : ℕ) : ℝ))
    (hdeep : (vertex v word (cut s))⁻¹ * vertex v word (cut (s + 1))
      ∉ D.relBall lam (C * n)) :
    ¬ IsIsolated D.fam lam v word (cut s) := by
  intro hiso
  have hcount := deepIsolated_card_bound hbound hlet hclosed hcut
    {s} (fun _ => lam)
    (by simp [hs]) (by simp [hedge]) (by simpa [hedge] using hcomp)
    (by simpa using hiso)
    (by
      intro t ht htn
      exact hquasi t ht (by simpa using htn))
    (by simpa using hdeep)
  simp only [Finset.card_singleton] at hcount
  omega

/-! ## The every-edge specialization -/

/-- **The counting consequence of Proposition 4.14 used in Lemma 4.21.**

Cut a closed word at every letter.  Every non-distinguished side is
`(1,1)`-quasi-geodesic, including a possible identity-labelled edge.  If every
distinguished singleton component lies outside the relative ball of radius
`B`, the radius witnesses supplied by Proposition 4.14 are all larger than
`B`, so `(B+1)|I| ≤ C · length`. -/
theorem deepIsolated_card_bound_everyEdge
    {D : RelGenSet G Λ} {C B : ℕ}
    (hbound : DGOUniformSumBound D 1 1 C)
    {v : G} {word : List (RelLetter G Λ)}
    (hlet : ∀ a ∈ word, D.IsLetter a)
    (hclosed : RelLetter.listVal word = 1)
    (I : Finset ℕ) (lam : ℕ → Λ)
    (hI : ∀ s ∈ I, s < word.length)
    (hcomp : ∀ s ∈ I, IsComp (lam s) word s (s + 1))
    (hiso : ∀ s ∈ I, IsIsolated D.fam (lam s) v word s)
    (hdeep : ∀ s ∈ I,
      (vertex v word s)⁻¹ * vertex v word (s + 1)
        ∉ D.relBall (lam s) B) :
    (B + 1) * I.card ≤ C * word.length := by
  have hcut : IsPolygonCut word.length word (fun s => s) :=
    ⟨rfl, rfl, fun s => Nat.le_succ s⟩
  apply deepIsolated_card_bound hbound hlet hclosed hcut I lam hI
    (fun _ _ => rfl) hcomp hiso (by
        intro s hs hsI p q hp hpq hq
        have hpqOne : q - p ≤ 1 := by omega
        have hnonneg : (0 : ℝ) ≤
            ((wordDist D.alphabet.carrier
              (vertex v word p) (vertex v word q) : ℕ) : ℝ) :=
          Nat.cast_nonneg _
        norm_num
        exact le_trans (by exact_mod_cast hpqOne) (by linarith)) hdeep

end OsinComponents
end GGT
end GroupApproximation
