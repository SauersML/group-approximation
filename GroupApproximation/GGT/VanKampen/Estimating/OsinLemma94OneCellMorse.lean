import GroupApproximation.GGT.CayleyFourPointBridge
import GroupApproximation.GGT.HullSCLemma44RelativeDehn
import GroupApproximation.GGT.OsinTheorem54SepPolygonVertex
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94OneCellValue
import GroupApproximation.GGT.VanKampen.Estimating.UnboundMonotoneMorseIndex
import GroupApproximation.Meta.AxiomGuard

/-!
# The Morse kill for a pocket with no relator cell in the one-cell branch of Lemma 9.4

Osin (math/0411039v3, §9), Lemma 9.4, Case 1, when the source and target sides of the connector
pair lie on one relator cell `Π`.  In `OsinLemma94OneCellValue` the arc `S = q M p` of `Π` reads
the connector `Y` whenever the closed walk `X M` bounds a pocket with no relator cell.  Here the
contradiction comes at the printed threshold `ε ≥ ε₀`, with `ε₀` chosen after `λ` and `c` only.

Let `x₀`, `x₁`, `x₃` be the start of `S`, the end of `q` and the end of `S`, and let `κ` be a Morse
radius for `(λ, c)`-quasi-geodesic words.  The vertex `x₁` lies within `κ` of a point of a geodesic
from `x₀` to `x₃`, so `d(x₀, x₁) + d(x₁, x₃) ≤ 2κ + d(x₀, x₃)`.  The side `q` spans more than `ε`,
so `d(x₀, x₁) > ε`.  The rest `M p` of the arc is quasi-geodesic and at least as long as `p`,
which spans more than `ε`, so `d(x₁, x₃) ≥ λ ε - c`.  The connector is shorter than `ε`, so
`d(x₀, x₃) < ε`.  Together `λ ε - c < 2κ`, which fails once `2κ + c ≤ λ ε`.

* `IsLambdaCQuasiGeodesicWord.vertex_detour_le_morse`: a vertex of a quasi-geodesic word
  costs at most `2κ` as a detour between the endpoints.
* `IsLambdaCQuasiGeodesicWord.lambda_eps_lt_of_hairpin`: a quasi-geodesic word `A M B` with
  `|A|, |B| > ε` and `|A M B| < ε` in the word norm has `λ ε - c < 2κ`.
* `exists_morse_threshold_of_fourPoint`: a four-point hyperbolic alphabet has a Morse radius `κ`
  and a threshold `ε₀` with `2κ + c ≤ λ ε` for every `ε ≥ ε₀`.
* `listVal_dartWord_eq_of_cellFree_pocket_X` and `_Y`: the value step of `OsinLemma94OneCellValue`
  as a named lemma.
* `false_of_cellFree_pocket_X_morse` and `false_of_cellFree_pocket_Y_morse`: the two pockets with
  no relator cell are impossible at the threshold.

## Manuscript status

Infrastructure for `thm:hull` (tex 1636, "Hull's small cancellation theorem", through Osin's
Lemma 4.4); certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen

open CayleyGeodesicModel

universe u w v

variable {G : Type u} [Group G] {Lambda : Type w} {W : Set (List (GGT.RelLetter G Lambda))}

namespace IsLambdaCQuasiGeodesicWord

/-- **A vertex of a quasi-geodesic word is a detour of at most `2κ`.**  The vertex `i` lies within
`κ` of a point `f t` of a geodesic `f` between the endpoints, and `f t` splits the geodesic into
lengths `t` and `d - t`. -/
theorem vertex_detour_le_morse {D : GGT.RelGenSet G Lambda} {lambda c kappa : ℝ}
    (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    {word : List (GGT.RelLetter G Lambda)} (hword : IsLambdaCQuasiGeodesicWord D lambda c word)
    {i : ℕ} (hi : i ≤ word.length) :
    (WordMetric.wordNorm D.alphabet.carrier (OsinComponents.vertex 1 word i) : ℝ) +
        (WordMetric.wordDist D.alphabet.carrier (OsinComponents.vertex 1 word i)
          (GGT.RelLetter.listVal word) : ℝ) ≤
      2 * kappa + (WordMetric.wordNorm D.alphabet.carrier (GGT.RelLetter.listVal word) : ℝ) := by
  obtain ⟨f, hf, hf0, hf1⟩ := isGeodesicRealisationQuot D.alphabet
    (vertexQuot D.alphabet 1) (vertexQuot D.alphabet (1 * GGT.RelLetter.listVal word))
  obtain ⟨t, ht, hnear⟩ := (hmorse word hword 1 f hf hf0 hf1).1 i hi
  have hstart := hf 0 ⟨le_rfl, le_trans ht.1 ht.2⟩ t ht
  rw [hf0, zero_sub, abs_neg, abs_of_nonneg ht.1] at hstart
  have hend := hf t ht
    (dist (vertexQuot D.alphabet 1) (vertexQuot D.alphabet (1 * GGT.RelLetter.listVal word)))
    ⟨le_trans ht.1 ht.2, le_rfl⟩
  rw [hf1, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hend
  have htri := dist_triangle (vertexQuot D.alphabet 1) (f t)
    (vertexQuot D.alphabet (OsinComponents.vertex 1 word i))
  have htri' := dist_triangle (vertexQuot D.alphabet (OsinComponents.vertex 1 word i)) (f t)
    (vertexQuot D.alphabet (1 * GGT.RelLetter.listVal word))
  rw [dist_comm (f t)] at htri
  simp only [dist_vertexQuot, one_mul, WordMetric.wordDist_one_left] at htri htri' hend
  linarith

/-- **A quasi-geodesic hairpin has `λ ε - c < 2κ`.**  The word `A M B` is `(λ, c)`-quasi-geodesic,
`A` and `B` read elements of word norm more than `ε`, and the whole word reads an element of word
norm less than `ε`.  The end of `A` is at distance more than `ε` from the start, and at distance at
least `λ |M B| - c ≥ λ ε - c` from the end. -/
theorem lambda_eps_lt_of_hairpin {D : GGT.RelGenSet G Lambda} {lambda c kappa : ℝ}
    (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa) (hlambda : 0 ≤ lambda)
    {A M B : List (GGT.RelLetter G Lambda)}
    (hword : IsLambdaCQuasiGeodesicWord D lambda c (A ++ M ++ B)) {eps : ℕ}
    (hshort :
      WordMetric.wordNorm D.alphabet.carrier (GGT.RelLetter.listVal (A ++ M ++ B)) < eps)
    (hA : eps < WordMetric.wordNorm D.alphabet.carrier (GGT.RelLetter.listVal A))
    (hB : eps < WordMetric.wordNorm D.alphabet.carrier (GGT.RelLetter.listVal B)) :
    lambda * eps - c < 2 * kappa := by
  have hi : A.length ≤ (A ++ M ++ B).length := by
    simp only [List.length_append]
    omega
  have hvertex :
      OsinComponents.vertex 1 (A ++ M ++ B) A.length = GGT.RelLetter.listVal A := by
    rw [List.append_assoc, OsinComponents.vertex_append_of_le A (M ++ B) 1 A.length le_rfl,
      OsinComponents.vertex_length, one_mul]
  have hmain := hword.vertex_detour_le_morse hmorse hi
  rw [hvertex] at hmain
  have hsub := hword.2 A.length (A ++ M ++ B).length hi le_rfl
  have hlen : (A ++ M ++ B).length - A.length = M.length + B.length := by
    simp only [List.length_append]
    omega
  rw [hvertex, OsinComponents.vertex_length, one_mul, hlen] at hsub
  have hadmissible : HullSC.RelWord.IsAdmissible D B := fun a ha =>
    hword.1 a (List.mem_append.mpr (Or.inr ha))
  have hBlength :=
    HullSC.RelativeBoundaryContiguity.wordNorm_listVal_le_length D B hadmissible
  have heps : (eps : ℝ) ≤ ((M.length + B.length : ℕ) : ℝ) := by
    exact_mod_cast (show eps ≤ M.length + B.length by omega)
  have hlam := mul_le_mul_of_nonneg_left heps hlambda
  have hA' :
      (eps : ℝ) < (WordMetric.wordNorm D.alphabet.carrier (GGT.RelLetter.listVal A) : ℝ) := by
    exact_mod_cast hA
  have hshort' : (WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (A ++ M ++ B)) : ℝ) < eps := by
    exact_mod_cast hshort
  linarith

end IsLambdaCQuasiGeodesicWord

/-- **A Morse radius and the threshold `2κ + c ≤ λ ε`.**  For a four-point hyperbolic alphabet the
Cayley realisation is hyperbolic, so one radius `κ` serves every `(λ, c)`-quasi-geodesic word, and
`ε₀ = ⌈λ⁻¹ (2κ + c)⌉` works. -/
theorem exists_morse_threshold_of_fourPoint (D : GGT.RelGenSet G Lambda)
    (hhyper : ∃ delta : ℕ, Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (lambda c : ℝ) (hlambda : 0 < lambda) :
    ∃ kappa : ℝ, UnboundEstimate.IsWordMorseRadius D lambda c kappa ∧
      ∃ eps0 : ℕ, ∀ eps : ℕ, eps0 ≤ eps → 2 * kappa + c ≤ lambda * eps := by
  obtain ⟨delta, hdelta⟩ := hhyper
  obtain ⟨kappa, -, hmorse⟩ := exists_word_replacement_morse D lambda c hlambda
    (isHyperbolicSpace_cayley_of_fourPoint D.alphabet hdelta) (by positivity)
  refine ⟨kappa, hmorse, ⌈lambda⁻¹ * (2 * kappa + c)⌉₊, fun eps heps => ?_⟩
  have hceil : lambda⁻¹ * (2 * kappa + c) ≤ (eps : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast heps)
  have hmul := mul_le_mul_of_nonneg_left hceil hlambda.le
  rwa [← mul_assoc, mul_inv_cancel₀ hlambda.ne', one_mul] at hmul

/-- **The value step, pocket across `X`.**  The arc `q M p` reads `Y`. -/
theorem listVal_dartWord_eq_of_cellFree_pocket_X {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount} {l X Y M : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q : Embedded.CyclicArc (Embedded.cellDarts Delta i))
    (hrot : l ~r X ++ Embedded.invDarts Delta q.darts ++ Y ++ Embedded.invDarts Delta p.darts)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r X ++ M) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta (q.darts ++ M ++ p.darts)) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta Y) := by
  have hM := P.listVal_eq_inv_of_outer_isRotated hcells hpocket
  have hface := Embedded.listVal_dartWord_eq_of_isRotated_invDarts Delta hl hrot
  rw [Embedded.dartWord_append, HullSC.RelWord.listVal_append, Embedded.dartWord_append,
    HullSC.RelWord.listVal_append, hM, hface]

/-- **The value step, pocket across `Y`.**  The arc `p M q` reads `X`. -/
theorem listVal_dartWord_eq_of_cellFree_pocket_Y {Delta : DiscDiagram.{u, w, v} W}
    {i : Fin Delta.rCellCount} {l X Y M : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q : Embedded.CyclicArc (Embedded.cellDarts Delta i))
    (hrot : l ~r X ++ Embedded.invDarts Delta q.darts ++ Y ++ Embedded.invDarts Delta p.darts)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r Y ++ M) :
    GGT.RelLetter.listVal (Embedded.dartWord Delta (p.darts ++ M ++ q.darts)) =
      GGT.RelLetter.listVal (Embedded.dartWord Delta X) := by
  have hrot' :
      l ~r Y ++ Embedded.invDarts Delta p.darts ++ X ++ Embedded.invDarts Delta q.darts := by
    refine hrot.trans ?_
    simpa only [List.append_assoc] using
      (List.isRotated_append (l := X ++ Embedded.invDarts Delta q.darts)
        (l' := Y ++ Embedded.invDarts Delta p.darts))
  have hM := P.listVal_eq_inv_of_outer_isRotated hcells hpocket
  have hface := Embedded.listVal_dartWord_eq_of_isRotated_invDarts Delta hl hrot'
  rw [Embedded.dartWord_append, HullSC.RelWord.listVal_append, Embedded.dartWord_append,
    HullSC.RelWord.listVal_append, hM, hface]

/-- **The Morse kill, pocket across `X`.**  The arc `S = q M p` of the cell is quasi-geodesic and
reads `Y`, so it is a hairpin: `|q|, |p| > ε` and `|Y| < ε` give `λ ε - c < 2κ`. -/
theorem false_of_cellFree_pocket_X_morse {D : GGT.RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c kappa : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 ≤ lambda) (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    (hthreshold : 2 * kappa + c ≤ lambda * eps)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    {l X Y M : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q S : Embedded.CyclicArc (Embedded.cellDarts Delta i))
    (hrot : l ~r X ++ Embedded.invDarts Delta q.darts ++ Y ++ Embedded.invDarts Delta p.darts)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r X ++ M) (hS : S.darts = q.darts ++ M ++ p.darts)
    (hY : WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta Y)) < eps)
    (hp : eps < WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta p.darts)))
    (hq : eps < WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta q.darts))) : False := by
  have hword := Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts hcond S
  rw [hS, Embedded.dartWord_append, Embedded.dartWord_append] at hword
  have hvalue := listVal_dartWord_eq_of_cellFree_pocket_X hl p q hrot P hcells hpocket
  rw [Embedded.dartWord_append, Embedded.dartWord_append] at hvalue
  have hbound := hword.lambda_eps_lt_of_hairpin hmorse hlambda
    (by rw [hvalue]; exact hY) hq hp
  linarith

/-- **The Morse kill, pocket across `Y`.**  As `false_of_cellFree_pocket_X_morse`, with the arc
`S = p M q` reading `X`. -/
theorem false_of_cellFree_pocket_Y_morse {D : GGT.RelGenSet G Lambda} {eps rho : ℕ}
    {mu lambda c kappa : ℝ} (hcond : OsinCCondition D W eps mu lambda c rho)
    (hlambda : 0 ≤ lambda) (hmorse : UnboundEstimate.IsWordMorseRadius D lambda c kappa)
    (hthreshold : 2 * kappa + c ≤ lambda * eps)
    {Delta : DiscDiagram.{u, w, v} W} {i : Fin Delta.rCellCount}
    {l X Y M : List Delta.toCombMap.Dart}
    (hl : GGT.RelLetter.listVal (Embedded.dartWord Delta l) = 1)
    (p q S : Embedded.CyclicArc (Embedded.cellDarts Delta i))
    (hrot : l ~r X ++ Embedded.invDarts Delta q.darts ++ Y ++ Embedded.invDarts Delta p.darts)
    (P : PocketRegion Delta) (hcells : ∀ C ∈ Delta.relatorCells, C.face ∉ P.faces)
    (hpocket : P.outer.cycle ~r Y ++ M) (hS : S.darts = p.darts ++ M ++ q.darts)
    (hX : WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta X)) < eps)
    (hp : eps < WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta p.darts)))
    (hq : eps < WordMetric.wordNorm D.alphabet.carrier
      (GGT.RelLetter.listVal (Embedded.dartWord Delta q.darts))) : False := by
  have hword := Embedded.CyclicArc.isLambdaCQuasiGeodesicWord_darts_cellDarts hcond S
  rw [hS, Embedded.dartWord_append, Embedded.dartWord_append] at hword
  have hvalue := listVal_dartWord_eq_of_cellFree_pocket_Y hl p q hrot P hcells hpocket
  rw [Embedded.dartWord_append, Embedded.dartWord_append] at hvalue
  have hbound := hword.lambda_eps_lt_of_hairpin hmorse hlambda
    (by rw [hvalue]; exact hX) hp hq
  linarith

end GroupApproximation.GGT.VanKampen

#audit_axioms GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.vertex_detour_le_morse
#audit_axioms GroupApproximation.GGT.VanKampen.IsLambdaCQuasiGeodesicWord.lambda_eps_lt_of_hairpin
#audit_axioms GroupApproximation.GGT.VanKampen.exists_morse_threshold_of_fourPoint
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_dartWord_eq_of_cellFree_pocket_X
#audit_axioms GroupApproximation.GGT.VanKampen.listVal_dartWord_eq_of_cellFree_pocket_Y
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_cellFree_pocket_X_morse
#audit_axioms GroupApproximation.GGT.VanKampen.false_of_cellFree_pocket_Y_morse
