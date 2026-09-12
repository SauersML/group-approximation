import GroupApproximation.GGT.VanKampen.Estimating.UnboundSmallMuCounterexample
import GroupApproximation.Meta.AxiomGuard

/-!
# The scaled unbound output statement is false as stated

`EstimatingUnboundOutputStatement` (`Estimating/Assembly.lean`) was repaired at
`c685697b9` by adding hyperbolicity and the certificate
`UnboundEstimate.OsinUnboundScale lambda c mu kappa c1 c2 eps rho`.  Its docstring
argues that `density_large` excludes both earlier counterexamples.  That is true at
the parameter tuples those files use, but the statement quantifies `lambda`, `c`,
`kappa`, `c1` and `c2` freely, and the constants `kappa`, `c1`, `c2` are tied to
nothing: in Osin (arXiv:math/0411039v3, Appendix, equation (36)) they are the
constants of his Lemmas 3.1 and 3.7 for the hyperbolicity constant of the Cayley
graph, and here they are arbitrary reals.

This file refutes the statement at `.{0,0,0}` with the geometry of
`UnboundSmallMuCounterexample` unchanged (the group `S₃ × ℤ` with every element a
letter, one relator cell of length `1089`, singleton outer word) and the tuple

    eps = 0, rho = 1089, mu = 1/32, lambda = 1/1089, c = 0,
    kappa = 0, c1 = -1, c2 = 0.

* `condition_fine`: the family satisfies `OsinCCondition` at `lambda = 1/1089`,
  `c = 0`, because every nonempty subpath of a relator moves the `ℤ`-coordinate, so
  consecutive-vertex distances are at least `1 >= lambda * 1089`.
* `outer_quasiGeodesic_fine`: the outer word `[b]` is `(1/1089, 0)`-quasi-geodesic.
* `scale_fine`: every field of `OsinUnboundScale` holds: `c1 + 2 kappa = -1 < 0`,
  and the density quantity is `33/261360 > 0 = max (1000 * eps) c2`.
* the unbound total of every O-equivalent output is `1089 > 1 * sqrt 1089`, as in
  `UnboundSmallMuCounterexample.exists_counterexample`.

**What a repair has to constrain.**  At `eps = 0` the field `epsilon_large` needs
`c1 + 2 * kappa < 0`, so `0 <= kappa` and `0 <= c1` already force `0 < eps`
(`scale_eps_pos_of_nonneg`), and then this bounded-alphabet model is gone for a
further reason: with every element a letter, a `(lambda, c)`-quasi-geodesic relator
of length at least `rho` forces `lambda * rho - c <= 1`, so the density quantity is
below `1 <= 1000 * eps`.  Nonnegativity alone is not a proof that the statement is
repaired.  The faithful repair ties the constants to the geometry the argument uses
(`c1 = 12 (delta + 1)` and `c2 = 100000 (delta + 1)` for a hyperbolicity constant of
the Cayley realization, and `kappa` a Morse radius for `(lambda, c)`-quasi-geodesic
words), which is the shape `UnboundEstimate.exists_polygonScale_parameters`
produces.
-/

namespace GroupApproximation.GGT.VanKampen.Estimating.UnboundScaledCounterexample

open GroupApproximation.HullSC GroupApproximation.WordMetric

universe u w

section Generic

variable {Γ : Type u} [Group Γ] {Λ : Type w}

/-- Reading a constant word `g^n` from `v` reaches `v * g ^ min i n` after `i` letters. -/
theorem vertex_replicate_base (v g : Γ) (n i : ℕ) :
    OsinComponents.vertex v (List.replicate n (RelLetter.base g : RelLetter Γ Λ)) i =
      v * g ^ min i n := by
  induction n generalizing v i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      rw [List.replicate_succ, OsinComponents.vertex_cons_succ, ih,
        Nat.add_min_add_right, pow_succ', ← mul_assoc]
      rfl

/-- A word whose vertices at distinct positions are distinct is
`(lambda, 0)`-quasi-geodesic as soon as `lambda` times its length is at most `1`:
distinct vertices are at word distance at least `1`. -/
theorem quasiGeodesic_of_vertex_ne (D : RelGenSet Γ Λ) {w : List (RelLetter Γ Λ)}
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (hscale : lambda * (w.length : ℝ) ≤ 1)
    (hadm : RelWord.IsAdmissible D w)
    (hne : ∀ i j : ℕ, i < j → j ≤ w.length →
      OsinComponents.vertex 1 w i ≠ OsinComponents.vertex 1 w j) :
    IsLambdaCQuasiGeodesicWord D lambda 0 w := by
  refine ⟨hadm, ?_⟩
  intro i j hij hj
  rcases Nat.lt_or_eq_of_le hij with hlt | rfl
  · have hdist : 1 ≤ wordDist D.alphabet.carrier
        (OsinComponents.vertex 1 w i) (OsinComponents.vertex 1 w j) :=
      one_le_wordNorm D.alphabet.symmetricGenerating
        (fun h => hne i j hlt hj (inv_mul_eq_one.mp h))
    have hdistReal : (1 : ℝ) ≤ ((wordDist D.alphabet.carrier
        (OsinComponents.vertex 1 w i) (OsinComponents.vertex 1 w j) : ℕ) : ℝ) := by
      exact_mod_cast hdist
    have hgap : ((j - i : ℕ) : ℝ) ≤ (w.length : ℝ) := by
      exact_mod_cast (show j - i ≤ w.length by omega)
    have hmul : lambda * ((j - i : ℕ) : ℝ) ≤ lambda * (w.length : ℝ) :=
      mul_le_mul_of_nonneg_left hgap hlambda
    linarith
  · have hnonneg : (0 : ℝ) ≤ ((wordDist D.alphabet.carrier
        (OsinComponents.vertex 1 w i) (OsinComponents.vertex 1 w i) : ℕ) : ℝ) := by
      positivity
    simp only [Nat.sub_self, Nat.cast_zero, mul_zero, sub_zero]
    exact hnonneg

/-- With nonnegative `kappa` and `c1`, the scale certificate forces a positive
relator-closeness threshold `eps`.  At `eps = 0` the certificate is satisfiable only
through a negative constant, which is what the refutation below uses. -/
theorem scale_eps_pos_of_nonneg {lambda c mu kappa c1 c2 : ℝ} {eps rho : ℕ}
    (scale : UnboundEstimate.OsinUnboundScale lambda c mu kappa c1 c2 eps rho)
    (hkappa : 0 ≤ kappa) (hc1 : 0 ≤ c1) : 0 < eps := by
  have h := scale.epsilon_large
  have hreal : (0 : ℝ) < (eps : ℝ) := by linarith
  exact_mod_cast hreal

end Generic

section Model

open UnboundSmallMuCounterexample

/-- The vertices of a small-mu relator word are powers of its letter. -/
theorem vertex_word (g : G) (i : ℕ) :
    OsinComponents.vertex 1 (word g) i = g ^ min i 1089 := by
  unfold word
  rw [vertex_replicate_base, one_mul]

theorem vertex_word_a_ne {i j : ℕ} (hij : i < j) (hj : j ≤ 1089) :
    OsinComponents.vertex 1 (word a) i ≠ OsinComponents.vertex 1 (word a) j := by
  rw [vertex_word, vertex_word, Nat.min_eq_left (by omega), Nat.min_eq_left hj]
  intro h
  have he := congrArg (fun g : G => g.2.toAdd) h
  simp only [exponent_a] at he
  omega

theorem vertex_word_inv_a_ne {i j : ℕ} (hij : i < j) (hj : j ≤ 1089) :
    OsinComponents.vertex 1 (word a⁻¹) i ≠ OsinComponents.vertex 1 (word a⁻¹) j := by
  rw [vertex_word, vertex_word, Nat.min_eq_left (by omega), Nat.min_eq_left hj]
  intro h
  have he := congrArg (fun g : G => g.2.toAdd) h
  simp only [exponent_inv_a] at he
  omega

/-- Both relator words are `(1/1089, 0)`-quasi-geodesic. -/
theorem word_quasiGeodesic_fine (w : List (RelLetter G Empty)) (hw : w ∈ W) :
    IsLambdaCQuasiGeodesicWord D (1 / 1089) 0 w := by
  have hlen := word_length w hw
  refine quasiGeodesic_of_vertex_ne D (by norm_num) (by rw [hlen]; norm_num)
    (quasiGeodesic_of_length_le (le_of_eq hlen)).1 ?_
  intro i j hij hj
  rw [hlen] at hj
  rcases hw with rfl | hw
  · exact vertex_word_a_ne hij hj
  · rw [Set.mem_singleton_iff.mp hw]
    exact vertex_word_inv_a_ne hij hj

/-- The singleton outer word `[b]` is `(1/1089, 0)`-quasi-geodesic. -/
theorem outer_quasiGeodesic_fine : IsLambdaCQuasiGeodesicWord D (1 / 1089) 0 outer := by
  refine quasiGeodesic_of_vertex_ne D (by norm_num) (by norm_num [outer])
    (quasiGeodesic_of_length_le (by decide)).1 ?_
  intro i j hij hj
  have hlen : outer.length = 1 := rfl
  have hj1 : j = 1 := by omega
  have hi0 : i = 0 := by omega
  subst hj1
  subst hi0
  change (1 : G) ≠ 1 * b
  rw [one_mul]
  exact fun h => b_ne_one h.symm

/-- The small-mu family satisfies Osin's condition at `lambda = 1/1089`, `c = 0`.
Only the quasi-geodesic field depends on `lambda` and `c`. -/
theorem condition_fine : OsinCCondition D W 0 (1 / 32) (1 / 1089) 0 1089 :=
  { condition.toIsSmallCancellation with
    quasiGeodesic := word_quasiGeodesic_fine
    publishedPiecesSmall := condition.publishedPiecesSmall }

theorem sqrt_rho : Real.sqrt ((1089 : ℕ) : ℝ) = 33 := by
  rw [show ((1089 : ℕ) : ℝ) = (33 : ℝ) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Every field of the scale certificate holds at the refuting tuple. -/
theorem scale_fine :
    UnboundEstimate.OsinUnboundScale (1 / 1089) 0 (1 / 32) 0 (-1) 0 0 1089 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · rw [sqrt_rho]
    norm_num
  · rw [sqrt_rho]
    norm_num
  · rw [sqrt_rho]
    norm_num

/-- **`EstimatingUnboundOutputStatement` is false.**  The hypotheses hold with the
small-mu geometry at `eps = 0`, `rho = 1089`, `mu = 1/32`, `lambda = 1/1089`, `c = 0`,
`kappa = 0`, `c1 = -1`, `c2 = 0`, and no O-equivalent output meets the budget. -/
theorem not_estimatingUnboundOutputStatement :
    ¬ EstimatingUnboundOutputStatement.{0, 0, 0} := by
  intro h
  obtain ⟨Delta, hred, hcount, hb, scaffold, ⟨graph⟩, hbad⟩ := exists_counterexample
  obtain ⟨Delta', ⟨equiv⟩, _, scaffold', _, budget⟩ :=
    h D 0 1089 (1 / 32) (1 / 1089) 0 0 (-1) 0 ⟨1, hyperbolic⟩ scale_fine condition_fine
      Delta hred (by omega) scaffold graph (by rw [hb]; exact outer_quasiGeodesic_fine)
  exact hbad Delta' equiv scaffold' budget

end Model

end GroupApproximation.GGT.VanKampen.Estimating.UnboundScaledCounterexample

#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundScaledCounterexample.not_estimatingUnboundOutputStatement
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundScaledCounterexample.condition_fine
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundScaledCounterexample.scale_fine
#audit_closed_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundScaledCounterexample.outer_quasiGeodesic_fine
#audit_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundScaledCounterexample.scale_eps_pos_of_nonneg
#audit_axioms GroupApproximation.GGT.VanKampen.Estimating.UnboundScaledCounterexample.quasiGeodesic_of_vertex_ne
