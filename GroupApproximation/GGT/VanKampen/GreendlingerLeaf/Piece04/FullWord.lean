import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.DiffKind
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.Gap
import GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.FullWordMetric
import GroupApproximation.GGT.VanKampen.Estimating.OsinLemma94ClassCornerMove
import GroupApproximation.GGT.VanKampen.WordGeodesicReplacement
import GroupApproximation.GGT.DGOQuasiGeodesicChainHausdorff
import GroupApproximation.Meta.AxiomGuard

/-!
# Greendlinger leaf, piece 04: the full-word different-kind branch

This module proves `ClassFullWordDiffKindStatement` (module `Piece04.Gap`).

**Setting.** `C` is a backwards class-word pair: the source class is (A1), the target class is long,
the kinds differ and the target is not cutting. The pair is full-word, meaning `a = 0`, `a' = |w_s|`,
`b' = 0` and `b = |w_t|`, and both connectors have length `ε − 1`.

Write `d` for the word metric of `symmetricLabelAlphabet D`, and `v_s`, `v_t` for the vertices of the
two class words. Put `A = v_s(0)`, `A' = v_s(|w_s|)`, `B' = v_t(0)` and `B = v_t(|w_t|)`. Then:
* `d(A,A') > ε` (`source_long`) and `d(B,B') > ε` (`target_long`);
* `d(B,A) = ε − 1` (`wordDist_start_eq`) and `d(B',A') = ε − 1` (`wordDist_end_eq`).

## Why the three local fixes fail

* **(i) An interior step.** Moving `(0, |w_t|)` or `(|w_s|, 0)` one letter inward costs one letter on
  the far connector, so it reaches `ε`, and the region insertion needs `≤ ε − 1` on one step and
  `≤ ε` on the other. No local argument can do better. The four points `A, A', B, B'` of a tree
  with `d(B,A) = ε−1`, `d(B,A') = ε`, `d(B',A) = ε`, `d(B',A') = ε+1` show this: every one-letter
  move of the corner pairs keeps a connector at `ε + 1`.
* **(ii) The quadrilateral argument, applied directly.** The face walk of the class polygon does not
  carry the gap darts, so the whole class arcs do not bound a sub-disc to which
  `false_of_quadrilateral_face` applies. That surgery is `OsinLemma94PinchedQuadrilateralStatement`,
  which is open.
* **(iii) Raising the threshold.** The connector length `ε − 1` is tied to the family parameter `ε`
  itself (`start_short : |startConnector| < ε`). Raising `ε₀` changes nothing about the pair.

## The proof: hyperbolic thinness

The residual pair is refuted metrically. The hypothesis `hhyper` of the statement has been unused
so far, and it is what does the work.

1. **Four-point step** (`exists_close_of_fullWord`, module `Piece04.FullWordMetric`). We have
   `d(B,A) + d(B',A') = 2ε − 2 < 2ε + 2 ≤ d(A,A') + d(B,B')`. So some `p` between `A` and `A'` and
   some `q` between `B'` and `B` satisfy `d(p,q) ≤ 8δ + 2`.
2. **Morse step** (`exists_index_near`). The class words are `(λ, c+2)`-quasi-geodesic
   (`quasiGeodesic_of_mem`), so they are `(λ⁻¹, ⌈c+2⌉₊)` chains (`to_chainAt`).
   `exists_chainAt_hausdorff_bound` gives one radius `R`, depending only on `λ, c, δ`, such that
   `d(p, v_s(i)) ≤ R` and `d(q, v_t(j)) ≤ R` for some indices `i`, `j`. So
   `d(v_t(j), v_s(i)) ≤ 2R + 8δ + 2`.
3. **Corner move** (`false_of_nearIndices`). `exists_cornerMove` moves `i` and `j` out of the gaps,
   by at most `⌊B/2⌋` letters each, where `B = ⌈(c+2)/λ⌉₊`. The distance grows by at most `B`
   (`wordDist_move_le`).
4. **Dispatch.** Both words have positive length (`a < a'` and `b' < b`). Choose the pair lemma of
   `Piece04.DiffKind` by position:
   * source moved forward when `i₁ < |w_s|`, else backward;
   * target moved forward when `j₁ = 0`, else backward.

   Each of the four lemmas needs `d + 2 ≤ ε`, and `d ≤ 2R + 8δ + 2 + B`.
5. **Threshold.** `ε₀ = 2R + 8δ + B + 5` (which is `≥ 3`) and `ρ₀ = 1`. Here `R` is chosen after `δ`
   and before `ε`.

Status: PROVED (by static authoring; not compiled).

## Manuscript status

Infrastructure for `thm:hull` (Hull's small cancellation theorem, through Osin's Lemma 9.4);
certifies no printed sentence on its own.
-/

namespace GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

universe u w v

open GroupApproximation.WordMetric
open GroupApproximation.GGT.VanKampen.Embedded
open GroupApproximation.GGT.VanKampen.UnboundEstimate

variable {G : Type u} [Group G] {Lambda : Type w}
  {W : Set (List (RelLetter G Lambda))}
  {D : RelGenSet G Lambda} {lambda c : ℝ} {eps : ℕ}
  {Delta : DiscDiagram.{u, w, v} W}
  {cuts : SectionCuts D lambda c Delta.boundaryWord}
  {S : GloballyDistinguishedSectionFamily D lambda c eps Delta cuts}
  {P : OsinLemma94RealizedPolygons S}

/-- **A point between the ends of a class word is near one of its vertices.** Here `hR` is the
reverse-proximity half of `exists_chainAt_hausdorff_bound` at `(λ⁻¹, ⌈c + 2⌉₊, δ)`. -/
theorem exists_index_near (Q : OsinLemma94ClassPolygons P) {δ R : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic (symmetricLabelAlphabet D).alphabet.carrier δ)
    (hR : ∀ (y : ℕ → G) (n : ℕ),
      IsSymmetricGeneratingSet (symmetricLabelAlphabet D).alphabet.carrier →
      Hyperbolic.IsFourPointHyperbolic (symmetricLabelAlphabet D).alphabet.carrier δ →
      IsQuasiGeodesicChainAt (symmetricLabelAlphabet D).alphabet.carrier lambda⁻¹ ⌈c + 2⌉₊ y n →
      ∀ q : G, Hyperbolic.IsBetween (symmetricLabelAlphabet D).alphabet.carrier (y 0) q (y n) →
        ∃ j : ℕ, j ≤ n ∧ wordDist (symmetricLabelAlphabet D).alphabet.carrier q (y j) ≤ R)
    {k : Fin P.count} {i : ℕ} (hi : i < Q.classCount k)
    (hmem : i ∈ Q.relatorClasses k ∨ i ∈ Q.longClasses k) {p : G}
    (hp : Hyperbolic.IsBetween (symmetricLabelAlphabet D).alphabet.carrier
      (OsinComponents.vertex (Q.corner k i) (Q.word k i) 0) p
      (OsinComponents.vertex (Q.corner k i) (Q.word k i) (Q.word k i).length)) :
    ∃ j : ℕ, j ≤ (Q.word k i).length ∧
      wordDist (symmetricLabelAlphabet D).alphabet.carrier p
        (OsinComponents.vertex (Q.corner k i) (Q.word k i) j) ≤ R :=
  hR (OsinComponents.vertex (Q.corner k i) (Q.word k i)) (Q.word k i).length
    (symmetricLabelAlphabet D).alphabet.symmetricGenerating hδ
    (IsLambdaCQuasiGeodesicWord.to_chainAt (Q.quasiGeodesic_of_mem k i hi hmem) (Q.corner k i))
    p hp

/-- **Near vertices refute the pair.** Any two vertices of the source and target class words at
distance `d` with `d + ⌈(c + 2) / λ⌉₊ + 2 ≤ ε` give a contradiction. The corner move takes both off
the gaps, and one of the four pair lemmas of `Piece04.DiffKind` applies. -/
theorem false_of_nearIndices (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps)
    (hlambda : 0 < lambda) {k : Fin P.count}
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hcut : Q.classKind k C.target ≠ .cutting)
    (hkind : Q.classKind k C.source ≠ Q.classKind k C.target)
    {x y : ℕ} (hx : x ≤ (Q.word k C.source).length) (hy : y ≤ (Q.word k C.target).length)
    (hs0 : 0 < (Q.word k C.source).length) (ht0 : 0 < (Q.word k C.target).length)
    (hd : wordDist (symmetricLabelAlphabet D).alphabet.carrier
        (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) y)
        (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) x) +
      ⌈(c + 2) / lambda⌉₊ + 2 ≤ eps) : False := by
  obtain ⟨x1, hx1, hngx, hx1x, hxx1⟩ :=
    Q.exists_cornerMove hlambda C.source_lt (Or.inl C.source_mem) hx
  obtain ⟨y1, hy1, hngy, hy1y, hyy1⟩ :=
    Q.exists_cornerMove hlambda C.target_lt (Or.inr C.target_mem) hy
  have hmove := wordDist_move_le Q C.source_admissible C.target_admissible
    (x := x) (x' := x1) (y := y) (y' := y1)
    (dx := ⌈(c + 2) / lambda⌉₊ / 2) (dy := ⌈(c + 2) / lambda⌉₊ / 2)
    hx hx1 (by omega) (by omega) hy hy1 (by omega) (by omega)
  rcases Nat.lt_or_ge x1 (Q.word k C.source).length with hxs | hxs
  · rcases Nat.eq_zero_or_pos y1 with hy0 | hy0
    · exact false_of_forwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
        C.target_mem C.source_admissible C.target_admissible hcut hkind hxs hngx (by omega) hngy
        (by omega)
    · exact false_of_forwardBackwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
        C.target_mem C.source_admissible C.target_admissible hcut hkind hxs hngx hy0 hy1 hngy
        (by omega)
  · rcases Nat.eq_zero_or_pos y1 with hy0 | hy0
    · exact false_of_backwardForwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
        C.target_mem C.source_admissible C.target_admissible hcut hkind (by omega) hx1 hngx
        (by omega) hngy (by omega)
    · exact false_of_backwardPair Q heps C.source_lt C.target_lt C.distinct C.source_mem
        C.target_mem C.source_admissible C.target_admissible hcut hkind (by omega) hx1 hngx hy0
        hy1 hngy (by omega)

/-- **The full-word different-kind pair is refuted**, at fixed parameters, once
`2R + 8δ + ⌈(c + 2) / λ⌉₊ + 4 ≤ ε`. -/
theorem false_of_fullWord (Q : OsinLemma94ClassPolygons P) (heps : 3 ≤ eps)
    (hlambda : 0 < lambda) {δ R : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic (symmetricLabelAlphabet D).alphabet.carrier δ)
    (hR : ∀ (y : ℕ → G) (n : ℕ),
      IsSymmetricGeneratingSet (symmetricLabelAlphabet D).alphabet.carrier →
      Hyperbolic.IsFourPointHyperbolic (symmetricLabelAlphabet D).alphabet.carrier δ →
      IsQuasiGeodesicChainAt (symmetricLabelAlphabet D).alphabet.carrier lambda⁻¹ ⌈c + 2⌉₊ y n →
      ∀ q : G, Hyperbolic.IsBetween (symmetricLabelAlphabet D).alphabet.carrier (y 0) q (y n) →
        ∃ j : ℕ, j ≤ n ∧ wordDist (symmetricLabelAlphabet D).alphabet.carrier q (y j) ≤ R)
    (hbig : 2 * R + 8 * δ + ⌈(c + 2) / lambda⌉₊ + 4 ≤ eps) (k : Fin P.count)
    (C : WordConnectorPair (symmetricLabelAlphabet D) (Q.corner k) (Q.word k) (Q.classCount k)
      (Q.relatorClasses k) (Q.longClasses k) eps)
    (hback : C.b' < C.b) (hcut : Q.classKind k C.target ≠ .cutting)
    (hkind : Q.classKind k C.source ≠ Q.classKind k C.target)
    (ha : C.a = 0) (ha' : C.a' = (Q.word k C.source).length) (hb' : C.b' = 0)
    (hb : C.b = (Q.word k C.target).length) (hstart : C.startConnector.length + 1 = eps)
    (hend : C.endConnector.length + 1 = eps) : False := by
  have hS := (symmetricLabelAlphabet D).alphabet.symmetricGenerating
  have hst := wordDist_start_eq Q C
  have hen := wordDist_end_eq Q C
  have hsl := C.source_long
  have htl := C.target_long
  have hfwd := C.source_forward
  rw [ha, hb] at hst
  rw [ha', hb'] at hen
  rw [ha, ha'] at hsl
  rw [hb, hb'] at htl
  obtain ⟨p, q, hp, hq, hpq⟩ := exists_close_of_fullWord hS hδ
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) 0)
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) (Q.word k C.source).length)
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) (Q.word k C.target).length)
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) 0) (by omega)
  obtain ⟨i, hi, hpi⟩ := exists_index_near Q hδ hR C.source_lt (Or.inl C.source_mem) hp
  obtain ⟨j, hj, hqj⟩ := exists_index_near Q hδ hR C.target_lt (Or.inr C.target_mem) hq
  have t1 := wordDist_triangle hS
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) j) q
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) i)
  have t2 := wordDist_triangle hS q p
    (OsinComponents.vertex (Q.corner k C.source) (Q.word k C.source) i)
  have c1 := wordDist_comm hS
    (OsinComponents.vertex (Q.corner k C.target) (Q.word k C.target) j) q
  have c2 := wordDist_comm hS q p
  exact false_of_nearIndices Q heps hlambda C hcut hkind hi hj (by omega) (by omega) (by omega)

/-- **The full-word different-kind branch of GapSpan.** -/
theorem fullWordDiffKind : ClassFullWordDiffKindStatement.{u, w, v} := by
  intro G _ Lambda D hhyper lambda c mu hlambda _ _ _ _
  obtain ⟨δ, hδ⟩ := hhyper
  have hδS : Hyperbolic.IsFourPointHyperbolic (symmetricLabelAlphabet D).alphabet.carrier δ := by
    rw [symmetricLabelAlphabet.carrier_eq]
    exact hδ
  obtain ⟨R, hR⟩ := exists_chainAt_hausdorff_bound (symmetricLabelAlphabet D).alphabet.carrier
    lambda⁻¹ ⌈c + 2⌉₊ δ (inv_pos.mpr hlambda)
  refine ⟨2 * R + 8 * δ + ⌈(c + 2) / lambda⌉₊ + 5, fun eps heps =>
    ⟨1, Nat.one_pos, fun _ _ => ?_⟩⟩
  intro _ _ _ _ _ _ _ _ _ _ _ _ Q k C hback _ _ hcut hkind ha ha' hb' hb hstart hend
  exact false_of_fullWord Q (by omega) hlambda hδS
    (fun y n hS' hδ' hchain => (hR y n hS' hδ' hchain).2) (by omega) k C hback hcut hkind ha ha'
    hb' hb hstart hend

end GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04

#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.exists_index_near
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_nearIndices
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.false_of_fullWord
#audit_axioms GroupApproximation.GGT.VanKampen.GreendlingerLeaf.Piece04.fullWordDiffKind
