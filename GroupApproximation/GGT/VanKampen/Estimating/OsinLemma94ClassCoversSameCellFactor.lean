import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94PolygonClasses
import GroupApproximation.Meta.AxiomGuard

/-!
# Osin's Lemma 9.4: the class cover with a factor for the same-cell darts

Osin (math/0411039v3, §9), proof of Lemma 9.4: "Let `S_i` denote the sum of lengths of all arcs
of type (A1) in `∂Δ_i`, `i = 1, …, d`. [...] Indeed otherwise we have
`S = ∑_{i=1}^d S_i ≤ (√ρ / 60) ∑_{i=1}^d n_i < n √ρ`."

An unbound dart of a relator cell whose reverse lies on the same cell lies across no polygon
side, so no class word covers it.  Such darts are bounded only through quasi-geodesicity.  Along
a maximal unbound stretch with `X` of them and `N` other darts, `λ X ≤ (1 - λ) N + c`
(`OsinUnboundSameCellStretchBound`, `OsinUnboundSameCellScanBound`).  So their total is at most
`M₀` times the other unbound darts, plus `T n`.  A bound `T n` alone fails when one cell carries
many short pockets.

`OsinLemma94ClassPolygons.classCovers_of_sameCellFactor` turns two bounds into the class cover
`ClassCovers (M₀ + 1) ((M₀ + 1) L₀ + T)`.
* The unbound darts whose reverse lies on a different face are covered by the (A1) class words,
  up to `L₀ n`.
* The unbound darts with their own cell across number at most `M₀` times those, plus `T n`.

`OsinLemma94ClassCoversSameCellFactor.add_le_of_factor` is the arithmetic.

## Manuscript status

Infrastructure for `thm:hull` ("Hull's small cancellation theorem", through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

universe u w v

open GroupApproximation.GGT.VanKampen.Embedded

namespace OsinLemma94ClassCoversSameCellFactor

/-- **The arithmetic of the factor.**  If `A ≤ m B + t n` and `B ≤ X + l n` with `0 ≤ m`, then
`A + B ≤ (m + 1) X + ((m + 1) l + t) n`. -/
theorem add_le_of_factor {A B X n m l t : ℝ} (hm : 0 ≤ m) (hA : A ≤ m * B + t * n)
    (hB : B ≤ X + l * n) : A + B ≤ (m + 1) * X + ((m + 1) * l + t) * n := by
  have hmul : (m + 1) * B ≤ (m + 1) * (X + l * n) :=
    mul_le_mul_of_nonneg_left hB (by linarith)
  calc A + B ≤ m * B + t * n + B := by linarith
    _ = (m + 1) * B + t * n := by ring
    _ ≤ (m + 1) * (X + l * n) + t * n := by linarith
    _ = (m + 1) * X + ((m + 1) * l + t) * n := by ring

end OsinLemma94ClassCoversSameCellFactor

namespace OsinLemma94ClassPolygons

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

open scoped Classical in
/-- **The class cover with the same-cell factor.**  Suppose the unbound darts whose reverse lies
on a different face are covered by the (A1) class words up to `L₀ n`, and the unbound darts with
their own cell across number at most `M₀` times those plus `T n`.  Then the class polygons cover
every unbound dart, with factor `M₀ + 1` on the class words and slack `(M₀ + 1) L₀ + T`. -/
theorem classCovers_of_sameCellFactor (Q : OsinLemma94ClassPolygons P) {M₀ L₀ T : ℕ}
    (hother : (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          ¬ (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) ≤
      ∑ k, classWordLength (Q.word k) (Q.classCount k) (Q.relatorClasses k) +
        (L₀ : ℝ) * Delta.rCellCount)
    (hsame : (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) ≤
      (M₀ : ℝ) * (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          ¬ (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) +
        (T : ℝ) * Delta.rCellCount) :
    Q.ClassCovers (M₀ + 1) ((M₀ + 1) * L₀ + T) := by
  have hsplit : (∑ i : Fin S.diagram.rCellCount,
      ((RegionCandidate.unboundDarts S.family i).card : ℝ)) =
      (∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ)) +
      ∑ i : Fin S.diagram.rCellCount,
        (((RegionCandidate.unboundDarts S.family i).filter fun d =>
          ¬ (cell S.diagram i).face =
            S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcard := Finset.card_filter_add_card_filter_not
      (s := RegionCandidate.unboundDarts S.family i)
      fun d => (cell S.diagram i).face =
        S.diagram.toCombMap.faceOf (S.diagram.toCombMap.alpha d)
    exact_mod_cast hcard.symm
  have key := OsinLemma94ClassCoversSameCellFactor.add_le_of_factor
    (Nat.cast_nonneg M₀) hsame hother
  unfold ClassCovers
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  linarith [key, hsplit]

end OsinLemma94ClassPolygons

#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassCoversSameCellFactor.add_le_of_factor
#audit_axioms GroupApproximation.GGT.VanKampen.OsinLemma94ClassPolygons.classCovers_of_sameCellFactor

end GroupApproximation.GGT.VanKampen
