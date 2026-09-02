import GroupApproximation.GGT.HullSCLemma49PowerChain
import GroupApproximation.GGT.HullSCConeOffHeavyChordChain
import GroupApproximation.GGT.DGOThinPolygonVertex

/-!
# Shadowing across the Lemma 4.9 contiguity quadrangle

The exterior arc of the selected relator cell and its opposite power-boundary
arc have corresponding endpoints at distance at most `eps`.  When both arcs
are uniform quasi-geodesics, every vertex of the power arc is uniformly close
to a vertex of the relator exterior.

The proof uses the two proved directions of Morse stability.  First move the
power vertex to a between-point of its endpoint chord.  Thinness of the
quadrangle moves that point either to the exterior chord or to one of the two
short connector chords.  In the exterior case, chord-near-chain Morse returns
an exterior vertex.  In either connector case, the relevant endpoint of the
exterior already works.

The constant is selected before either chain and depends only on their two
quasi-geodesic constants, the four-point hyperbolicity constant, and the
connector bound.  This is data produced from proved geometry; no new geometric
proposition is declared.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.WordMetric

universe u

/-! ## Uniform vertex shadowing -/

/-- Two endpoint-close `(4,b)` chains shadow one another at vertices.  The
first chain uses additive constant `1`, as relator words in Hull's `C₁`
condition do; the second uses an arbitrary additive constant `b`, allowing the
long-period power estimate from `HullSCLemma49PowerChain`.

The chain-near-chord constant is selected directly from the universe-uniform
Morse theorem.  This placement of the quantifier is important: one natural
number then serves every group and alphabet appearing after it. -/
theorem exists_quasiChain_quadrangleShadow
    (delta eps b : ℕ) :
    ∃ K : ℕ, ∀
      (G : Type u) (_ : Group G) (S : Set G)
      (qRel qPow : ℕ → G) (nRel nPow : ℕ),
      IsSymmetricGeneratingSet S →
      Hyperbolic.IsFourPointHyperbolic S delta →
      GGT.IsQuasiGeodesicChainAt S 4 1 qRel nRel →
      GGT.IsQuasiGeodesicChainAt S 4 b qPow nPow →
      wordDist S (qRel 0) (qPow 0) ≤ eps →
      wordDist S (qPow nPow) (qRel nRel) ≤ eps →
      ∀ i ≤ nPow, ∃ j ≤ nRel, wordDist S (qPow i) (qRel j) ≤ K := by
  obtain ⟨Rp, hp⟩ := Hyperbolic.morseLemma_univ.{u} 4 b delta
  obtain ⟨Rr, hr⟩ :=
    exists_index_wordDist_le_of_isBetween_of_fourPoint (u := u) 4 1 delta
  refine ⟨Rp + Rr + 8 * delta + eps, ?_⟩
  intro G _ S qRel qPow nRel nPow hS hdelta hRel hPow hleft hright i hi
  have hpActual := hp G inferInstance S hS hdelta nPow qPow
    hPow.toQuasiGeodesic_four i hi
  obtain ⟨p, hpBetween, hip⟩ := hpActual
  rcases GGT.exists_isBetween_of_quadrangle hS hdelta hpBetween
      (x₃ := qRel nRel) (x₄ := qRel 0) with hconnRight | hrelChord | hconnLeft
  · obtain ⟨q, hq, hpq⟩ := hconnRight
    refine ⟨nRel, le_rfl, ?_⟩
    have hqend : wordDist S q (qRel nRel) ≤ eps := by
      have hdist : wordDist S (qPow nPow) q + wordDist S q (qRel nRel) =
          wordDist S (qPow nPow) (qRel nRel) := hq
      omega
    have htri₁ := wordDist_triangle hS (qPow i) p q
    have htri₂ := wordDist_triangle hS (qPow i) q (qRel nRel)
    omega
  · obtain ⟨q, hq, hpq⟩ := hrelChord
    have hq' : Hyperbolic.IsBetween S (qRel 0) q (qRel nRel) :=
      Hyperbolic.IsBetween.symm hS hq
    obtain ⟨j, hj, hqj⟩ := hr G inferInstance S hS hdelta nRel qRel
      hRel.toQuasiGeodesic_four q hq'
    refine ⟨j, hj, ?_⟩
    have htri₁ := wordDist_triangle hS (qPow i) p q
    have htri₂ := wordDist_triangle hS (qPow i) q (qRel j)
    omega
  · obtain ⟨q, hq, hpq⟩ := hconnLeft
    refine ⟨0, Nat.zero_le _, ?_⟩
    have hqstart : wordDist S q (qRel 0) ≤ eps := by
      have hdist : wordDist S (qRel 0) q + wordDist S q (qPow 0) =
          wordDist S (qRel 0) (qPow 0) := hq
      have hcomm := wordDist_comm hS q (qRel 0)
      omega
    have htri₁ := wordDist_triangle hS (qPow i) p q
    have htri₂ := wordDist_triangle hS (qPow i) q (qRel 0)
    omega

/-! ## Restricting and translating chains -/

/-- Restrict a quasi-geodesic chain to a consecutive interval of its
parameter domain. -/
theorem isQuasiGeodesicChainAt_shift
    {G : Type u} [Group G] {S : Set G} {mu : ℝ} {b : ℕ}
    {q : ℕ → G} {n start length : ℕ}
    (h : GGT.IsQuasiGeodesicChainAt S mu b q n)
    (hfit : start + length ≤ n) :
    GGT.IsQuasiGeodesicChainAt S mu b (fun i => q (start + i)) length := by
  intro i j hij hj
  have hraw := h (start + i) (start + j) (by omega) (by omega)
  have hsub : start + j - (start + i) = j - i := by omega
  simpa only [hsub] using hraw

/-- Left translation preserves both halves of the chain estimate. -/
theorem isQuasiGeodesicChainAt_leftTranslate
    {G : Type u} [Group G] {S : Set G} {mu : ℝ} {b : ℕ}
    {q : ℕ → G} {n : ℕ}
    (h : GGT.IsQuasiGeodesicChainAt S mu b q n) (a : G) :
    GGT.IsQuasiGeodesicChainAt S mu b (fun i => a * q i) n := by
  intro i j hij hj
  simpa only [wordDist_left_invariant] using h i j hij hj

/-- A chain predicate only sees the pairwise distances of its vertices. -/
theorem isQuasiGeodesicChainAt_of_pairwiseDistance
    {G : Type u} [Group G] {S : Set G} {mu : ℝ} {b : ℕ}
    {q q' : ℕ → G} {n : ℕ}
    (h : GGT.IsQuasiGeodesicChainAt S mu b q n)
    (hdist : ∀ i ≤ n, ∀ j ≤ n,
      wordDist S (q' i) (q' j) = wordDist S (q i) (q j)) :
    GGT.IsQuasiGeodesicChainAt S mu b q' n := by
  intro i j hij hj
  rw [hdist i (le_trans hij hj) j hj]
  exact h i j hij hj

/-! ## The two concrete chains in a power contiguity certificate -/

/-- Vertices on the exterior prefix of the selected relator cell. -/
def Lemma49RelativeGreendlingerCell.exteriorVertex
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z) (
      i : ℕ) : G :=
  GGT.RelLetter.listVal (C.contiguity.exterior.take i)

/-- Vertices on the opposite boundary arc, translated so its first endpoint
is the endpoint of the left contiguity side. -/
def Lemma49RelativeGreendlingerCell.powerArcVertex
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z) (
      i : ℕ) : G :=
  GGT.RelLetter.listVal C.contiguity.leftSide *
    GGT.RelLetter.listVal (C.boundaryArc.take i)

/-- The exterior prefix inherits the relator's `(4,1)` chain estimate. -/
theorem Lemma49RelativeGreendlingerCell.exterior_isQuasiGeodesicChainAt
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps rho : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z)
    (hinput : RelWord.IsLemma49Input D (RelWord.symmetrized v) eps mu rho) :
    GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 1 C.exteriorVertex
      C.contiguity.exterior.length := by
  have hprefix := isQuasiGeodesicChainAt_shift
    (hinput.quasiGeodesic C.relator C.relator_mem)
    C.contiguity.exterior_length_le_relator
  apply isQuasiGeodesicChainAt_of_pairwiseDistance
    hprefix
  intro i hi j hj
  have hiTake : C.relator.take i = C.contiguity.exterior.take i := by
    rw [C.contiguity.relator_decomposition,
      List.take_append_of_le_length hi]
  have hjTake : C.relator.take j = C.contiguity.exterior.take j := by
    rw [C.contiguity.relator_decomposition,
      List.take_append_of_le_length hj]
  simp only [Nat.zero_add, Lemma49RelativeGreendlingerCell.exteriorVertex,
    hiTake, hjTake]

/-- Restricting the global power chain to the literal certificate factor and
translating it by the left side gives the power-arc chain. -/
theorem Lemma49RelativeGreendlingerCell.powerArc_isQuasiGeodesicChainAt
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    {b : ℕ}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z)
    (hpower : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b
      (fun i => GGT.OsinComponents.vertex 1
        (lemma49BoundaryPower Z.boundaryWord n) i)
      (lemma49BoundaryPower Z.boundaryWord n).length) :
    GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b C.powerArcVertex
      C.boundaryArc.length := by
  let start := C.boundaryBefore.length
  have hfit : start + C.boundaryArc.length ≤
      (lemma49BoundaryPower Z.boundaryWord n).length := by
    dsimp [start]
    rw [C.boundary_decomposition]
    simp only [List.length_append]
    omega
  have hshift := isQuasiGeodesicChainAt_shift hpower hfit
  let qArc : ℕ → G := fun i => GGT.RelLetter.listVal (C.boundaryArc.take i)
  have hvertex : ∀ i ≤ C.boundaryArc.length,
      GGT.OsinComponents.vertex 1
          (lemma49BoundaryPower Z.boundaryWord n) (start + i) =
        GGT.RelLetter.listVal C.boundaryBefore * qArc i := by
    intro i hi
    dsimp [start, qArc]
    rw [C.boundary_decomposition, ← List.append_assoc,
      GGT.OsinComponents.vertex_append_add C.boundaryBefore
        (C.boundaryArc ++ C.boundaryAfter) 1 i,
      one_mul,
      GGT.OsinComponents.vertex_append_of_le C.boundaryArc
        C.boundaryAfter (GGT.RelLetter.listVal C.boundaryBefore) i hi,
      GGT.OsinComponents.vertex_eq_mul_listVal_take]
  have hArc : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 4 b qArc
      C.boundaryArc.length := by
    apply isQuasiGeodesicChainAt_of_pairwiseDistance hshift
    intro i hi j hj
    rw [hvertex i hi, hvertex j hj, wordDist_left_invariant]
  have htranslated := isQuasiGeodesicChainAt_leftTranslate hArc
    (GGT.RelLetter.listVal C.contiguity.leftSide)
  exact htranslated

/-- The two first endpoints are joined by the left contiguity side. -/
theorem Lemma49RelativeGreendlingerCell.leftEndpoint_close
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z) :
    wordDist D.alphabet.carrier (C.exteriorVertex 0) (C.powerArcVertex 0)
      ≤ eps := by
  have hnorm := GGT.OsinComponents.wordNorm_listVal_le D
    C.contiguity.leftSide C.contiguity.leftSide_admissible
  simpa only [Lemma49RelativeGreendlingerCell.exteriorVertex,
    Lemma49RelativeGreendlingerCell.powerArcVertex, List.take_zero,
    GGT.RelLetter.listVal_nil, mul_one, wordDist_one_left] using
      le_trans hnorm C.contiguity.leftSide_short

/-- The two final endpoints are joined by the right contiguity side. -/
theorem Lemma49RelativeGreendlingerCell.rightEndpoint_close
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z) :
    wordDist D.alphabet.carrier (C.powerArcVertex C.boundaryArc.length)
        (C.exteriorVertex C.contiguity.exterior.length) ≤ eps := by
  have hnorm := GGT.OsinComponents.wordNorm_listVal_le D
    C.contiguity.rightSide C.contiguity.rightSide_admissible
  have hdist : wordDist D.alphabet.carrier
      (GGT.RelLetter.listVal C.contiguity.leftSide *
        GGT.RelLetter.listVal C.boundaryArc)
      (GGT.RelLetter.listVal C.contiguity.exterior) =
      wordNorm D.alphabet.carrier
        (GGT.RelLetter.listVal C.contiguity.rightSide) := by
    rw [C.boundaryArc_value, C.contiguity.exterior_value,
      ← wordDist_one_left D.alphabet.carrier
        (GGT.RelLetter.listVal C.contiguity.rightSide),
      ← wordDist_left_invariant D.alphabet.carrier
        (GGT.RelLetter.listVal C.contiguity.leftSide *
          C.contiguity.boundaryArc.prod) 1
          (GGT.RelLetter.listVal C.contiguity.rightSide)]
    simp only [mul_one, mul_assoc]
  simpa only [Lemma49RelativeGreendlingerCell.exteriorVertex,
    Lemma49RelativeGreendlingerCell.powerArcVertex, List.take_length] using
      hdist.trans_le (le_trans hnorm C.contiguity.rightSide_short)

/-! ## Certificate-level shadow data -/

/-- A concrete nearest exterior index for every power-arc vertex.  The
structure contains data and inequalities, not a new geometric hypothesis. -/
structure Lemma49ContiguityShadow
    {G : Type u} [Group G] {Lambda : Type*}
    {D : GGT.RelGenSet G Lambda}
    {v : List (GGT.RelLetter G Lambda)} {g : G} {n eps : ℕ} {mu : ℝ}
    {Z : Lemma49GeodesicPowerDiagram D v g n}
    (C : Lemma49RelativeGreendlingerCell D v g n eps mu Z) (K : ℕ) where
  index : ℕ → ℕ
  index_le : ∀ i ≤ C.boundaryArc.length,
    index i ≤ C.contiguity.exterior.length
  close : ∀ i ≤ C.boundaryArc.length,
    wordDist D.alphabet.carrier (C.powerArcVertex i)
      (C.exteriorVertex (index i)) ≤ K

/-- Uniform shadow data for every selected cell whose shortest power period is
long enough for the proved local-to-global estimate. -/
theorem exists_lemma49ContiguityShadow_constant
    (delta eps : ℕ) :
    ∃ K : ℕ, ∀
      (G : Type u) (_ : Group G) (Lambda : Type*)
      (D : GGT.RelGenSet G Lambda)
      (v : List (GGT.RelLetter G Lambda)) (g : G) (n rho : ℕ)
      (Z : Lemma49GeodesicPowerDiagram D v g n)
      (C : Lemma49RelativeGreendlingerCell D v g n eps (1 / 1000) Z)
      (N : Subgroup G) (_ : N.Normal),
      Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta →
      RelWord.IsLemma49Input D (RelWord.symmetrized v) eps (1 / 1000) rho →
      IsShortestModuloConjugacy D.alphabet.carrier N g →
      8 * delta + 2 ≤ Z.boundaryWord.length →
      Nonempty (Lemma49ContiguityShadow C K) := by
  obtain ⟨K, hK⟩ := exists_quasiChain_quadrangleShadow
    (u := u) delta eps (8 * delta + 2)
  refine ⟨K, ?_⟩
  intro G _ Lambda D v g n rho Z C N _ hdelta hinput hshort hlong
  have hRel := C.exterior_isQuasiGeodesicChainAt hinput
  have hPowerGlobal := isQuasiGeodesicChainAt_power_of_long_period
    D N hshort Z.boundary_geodesic Z.exponent_pos hdelta hlong
  have hPower := C.powerArc_isQuasiGeodesicChainAt hPowerGlobal
  have hnear := hK G inferInstance D.alphabet.carrier C.exteriorVertex
    C.powerArcVertex C.contiguity.exterior.length C.boundaryArc.length
    D.alphabet.symmetricGenerating hdelta hRel hPower
    C.leftEndpoint_close C.rightEndpoint_close
  choose index hindex hclose using hnear
  exact ⟨{
    index := index
    index_le := hindex
    close := hclose }⟩

/-! ## Model check -/

/-- Constant chains shadow each other at index zero when their endpoints
coincide.  This checks the endpoint branches independently of Morse geometry. -/
theorem constantChain_shadow_model {G : Type u} [Group G]
    {S : Set G} (hS : IsSymmetricGeneratingSet S) (x : G) :
    ∀ i ≤ 0, ∃ j ≤ 0,
      wordDist S ((fun _ : ℕ => x) i) ((fun _ : ℕ => x) j) ≤ 0 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  exact ⟨0, le_rfl, by simp [wordDist_self]⟩

end HullSC
end GroupApproximation
