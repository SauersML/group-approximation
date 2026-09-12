import GroupApproximation.GGT.HullTheorem316CosetProjection
import GroupApproximation.GGT.HullYiCyclicRelativeBall
import GroupApproximation.GGT.HullYiStatements
import GroupApproximation.GGT.DGOIsolatedComponentReduce

/-!
# Hull's Theorem 3.16: the quantitative assembly

The printed long-side argument has two independent constants: `D` controls
the distance between the two sides and `β` controls the length of the parallel
subsegments.  Keeping them independent is essential.  We first fix `D` from
hyperbolicity and the maximum relative-word length, ask geometric separation
for its diameter bound, and only then choose `β` larger than that bound.

This closes the prescribed-alphabet relative-ball estimate for a finite cyclic
family satisfying `E(g) = ⟨g⟩`, and hence closes local finiteness and the full
hyperbolic-embedding conclusion used by Hull.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.HullGeometry
open GroupApproximation.Olshanskii
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G]

/-- The relative-word polygon with independent fellow-travel distance `D` and
parallel length `β`.  This is the form of Ol'shanskii's lemma needed in Hull's
Theorem 3.16: `D` is fixed before geometric separation supplies its diameter
bound, while `β` is chosen afterwards. -/
theorem exists_peripheral_side_close_to_long_closing_side_at
    {Λ : Type w} (A : Alphabet G) (K : Λ → Subgroup G) {δ : ℕ}
    (hδ : Hyperbolic.IsFourPointHyperbolic A.carrier δ)
    (q : List (RelLetter G Λ))
    (hlet : ∀ a ∈ q, (coneOffFamily A K).IsLetter a)
    (hq : 0 < q.length) {D β θ : ℝ}
    (hD : 3 * ((δ : ℝ) + 6) *
        ((Nat.clog 2 q.length : ℝ) + 1) ≤ D)
    (hβ : 0 < β)
    (hθ : (q.length : ℝ) * (β + 4 * D) + 2 * (q.length : ℝ) < θ)
    (hθb : θ ≤ dist (iotaG A (RelLetter.listVal q)) (iotaG A 1)) :
    ∃ i lam h, 0 < i ∧ i < q.length + 1 ∧
      q[i - 1]? = some (RelLetter.comp lam h) ∧
      ∃ u ∈ Set.Icc (0 : ℝ)
          (dist (iotaG A (RelLetter.listVal q)) (iotaG A 1)),
        ∃ u' ∈ Set.Icc (0 : ℝ)
            (dist (iotaG A (RelLetter.listVal q)) (iotaG A 1)),
          ∃ s ∈ Set.Icc (0 : ℝ)
              (dist (relativeClosingVertex A q i)
                (relativeClosingVertex A q (i + 1))),
            ∃ s' ∈ Set.Icc (0 : ℝ)
                (dist (relativeClosingVertex A q i)
                  (relativeClosingVertex A q (i + 1))),
              β ≤ u' - u ∧ β ≤ |s' - s| ∧
                dist ((Classical.choose (exists_relativeClosingPolygon A q)) 0 u)
                    ((Classical.choose (exists_relativeClosingPolygon A q)) i s)
                  ≤ D ∧
                dist ((Classical.choose (exists_relativeClosingPolygon A q)) 0 u')
                    ((Classical.choose (exists_relativeClosingPolygon A q)) i s')
                  ≤ D := by
  let sides := Classical.choose (exists_relativeClosingPolygon A q)
  have hpoly : IsClosedPolygonAt (relativeClosingVertex A q) sides 0
      (q.length + 1) := Classical.choose_spec (exists_relativeClosingPolygon A q)
  have hhypC : IsHyperbolicSpace ((δ : ℝ)) (Cayley A) :=
    isHyperbolicSpace_cayley_of_fourPoint A hδ
  have hhyp : IsHyperbolicSpace ((δ : ℝ) + 6)
      (CayleyGeodesicModel.PointQuot A) :=
    CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point A hhypC)
  have hgeo : IsGeodesicSpace (CayleyGeodesicModel.PointQuot A) :=
    CayleyGeodesicModel.isGeodesicRealisationQuot A
  have hδ0 : (0 : ℝ) ≤ (δ : ℝ) + 6 := by positivity
  have hn : 2 ≤ q.length + 1 := by omega
  have hshort : ∀ i, 0 < i → i < q.length + 1 →
      i ∉ relativeCompSides q →
      dist (relativeClosingVertex A q i)
        (relativeClosingVertex A q (i + 1)) ≤ (fun _ => (2 : ℝ)) i := by
    intro i hi0 hi hin
    exact dist_relativeClosingVertex_le_two_of_not_comp A K q hlet hi0 hi hin
  have hρ : ∑ j ∈ Finset.range ((q.length + 1) - 1),
      (fun _ => (2 : ℝ)) (0 + 1 + j) ≤ 2 * (q.length : ℝ) := by
    simpa using relative_short_side_budget (G := G) (Λ := Λ) q
  have hlong : (((q.length + 1 : ℕ) : ℝ) - 1) * (β + 4 * D) +
      2 * (q.length : ℝ) <
        dist (relativeClosingVertex A q 0) (relativeClosingVertex A q (0 + 1)) := by
    push_cast
    simpa [relativeClosingVertex] using lt_of_lt_of_le hθ hθb
  obtain ⟨i, hi0, hi, hiS, u, hu, u', hu', s, hs, s', hs',
      huu', hss', hclose, hclose'⟩ :=
    exists_long_close_pair hhyp hδ0 hgeo hn
      (Nat.le_pow_clog (by norm_num) q.length) hpoly hD
      (relativeCompSides q) (fun _ => (2 : ℝ)) (fun _ => by positivity)
      (fun i hi0 hi hiS => hshort i hi0 (by omega) hiS)
      hρ hβ hlong
  obtain ⟨lam, h, hletter⟩ := hiS
  refine ⟨i, lam, h, hi0, (by omega), hletter, u, ?_, u', ?_, s, hs, s', hs',
    huu', hss', ?_, ?_⟩
  · simpa [relativeClosingVertex] using hu
  · simpa [relativeClosingVertex] using hu'
  · simpa [sides] using hclose
  · simpa [sides] using hclose'

/-- Hull's prescribed-alphabet estimate: every fixed-radius relative ball in
the cyclic family has uniformly bounded displacement in the original Cayley
graph.  All constants are constructed internally from `A`, `g`, and the radius.
-/
theorem orbitBound_zpowersFamily_of_elementaryClosure_eq
    {Λ : Type w} [Fintype Λ] [Nonempty Λ]
    (A : HullGeneratingSet G) (g : Λ → G)
    (hncom : PairwiseNonCommensurable g)
    (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A.alphabet))
    (hcyc : ∀ lam : Λ,
      Elementary.elementaryClosure (g lam) = Subgroup.zpowers (g lam)) :
    ∀ (lam : Λ) (n : ℕ), ∃ R : ℝ,
      ∀ h : G, h ∈
        (coneOffFamily A.alphabet
          (fun nu => Subgroup.zpowers (g nu))).relBall lam n →
        dist (Cayley.base A.alphabet) (h • Cayley.base A.alphabet) ≤ R := by
  classical
  let K : Λ → Subgroup G := fun nu => Subgroup.zpowers (g nu)
  have hsep : IsGeometricallySeparated A.alphabet K :=
    isGeometricallySeparated_zpowers_of_elementaryClosure_eq
      A g hncom hlox hcyc
  have hprojAll : ∀ mu : Λ, ∃ σ : ℝ, 0 ≤ σ ∧ ∀ (v a b : G),
      a ∈ K mu → b ∈ K mu →
      ∀ f : ℝ → CayleyGeodesicModel.PointQuot A.alphabet,
        IsGeodesicSegment f 0
          (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))) →
        f 0 = iotaG A.alphabet (v * a) →
        f (dist (iotaG A.alphabet (v * a))
          (iotaG A.alphabet (v * b))) = iotaG A.alphabet (v * b) →
        ∀ t ∈ Set.Icc (0 : ℝ)
            (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))),
          ∃ c : G, c ∈ K mu ∧
            dist (f t) (iotaG A.alphabet (v * c)) ≤ σ := by
    intro mu
    exact exists_zpowers_coset_projection_pointQuot A (hlox mu) (hcyc mu)
  choose σ hσ0 hproj using hprojAll
  let S : ℝ := ∑ mu : Λ, σ mu
  have hσS : ∀ mu : Λ, σ mu ≤ S := by
    intro mu
    exact Finset.single_le_sum (fun nu _ => hσ0 nu) (Finset.mem_univ mu)
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun mu _ => hσ0 mu
  have hfour : Hyperbolic.IsFourPointHyperbolic A.alphabet.carrier ⌈A.delta⌉₊ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley A.alphabet A.hyperbolic
  intro lam n
  let D : ℝ := 3 * (((⌈A.delta⌉₊ : ℕ) : ℝ) + 6) *
    ((Nat.clog 2 n : ℝ) + 1)
  let E : ℝ := 2 * S + D
  obtain ⟨Rsep, hRsep⟩ := geometricSeparation_of_pointQuot_witness
    A.alphabet K hsep E
  let β : ℝ := (Rsep : ℝ) + 2 * S + 2
  have hβ0 : 0 < β := by
    dsimp [β]
    positivity
  let θ : ℝ := (n : ℝ) * (β + 4 * D) + 2 * (n : ℝ) + 1
  refine ⟨θ + 1, ?_⟩
  intro h hh
  obtain ⟨hhK, q, hlet, hqval, hav, hqlen⟩ := hh
  by_cases hq0 : q.length = 0
  · have hnil : q = [] := List.length_eq_zero_iff.mp hq0
    subst hnil
    simp only [RelLetter.listVal] at hqval
    subst h
    simp
    have : 0 ≤ θ := by
      dsimp [θ]
      positivity
    linarith
  · have hqpos : 0 < q.length := Nat.pos_of_ne_zero hq0
    have hqn : q.length ≤ n := hqlen
    have hclog : Nat.clog 2 q.length ≤ Nat.clog 2 n :=
      Nat.clog_mono_right 2 hqn
    have hDq : 3 * (((⌈A.delta⌉₊ : ℕ) : ℝ) + 6) *
        ((Nat.clog 2 q.length : ℝ) + 1) ≤ D := by
      dsimp [D]
      have hnonneg : 0 ≤ 3 * (((⌈A.delta⌉₊ : ℕ) : ℝ) + 6) := by positivity
      gcongr
    have hθq : (q.length : ℝ) * (β + 4 * D) + 2 * (q.length : ℝ) < θ := by
      have hcast : (q.length : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqn
      dsimp [θ]
      have hcoef : 0 ≤ β + 4 * D := by positivity
      nlinarith
    by_contra hnot
    have hfar : θ ≤ dist (iotaG A.alphabet (RelLetter.listVal q))
        (iotaG A.alphabet 1) := by
      have hmodel := le_dist_iotaG A.alphabet (RelLetter.listVal q) 1
      have hcayley : dist (Cayley.base A.alphabet)
          (h • Cayley.base A.alphabet) =
          ((wordDist A.alphabet.carrier (RelLetter.listVal q) 1 : ℕ) : ℝ) := by
        rw [dist_base_smul, ← hqval, ← wordDist_one_left,
          wordDist_comm A.alphabet.symmetricGenerating]
      have hlarge : θ + 1 < dist (Cayley.base A.alphabet)
          (h • Cayley.base A.alphabet) := lt_of_not_ge hnot
      rw [hcayley] at hlarge
      linarith
    obtain ⟨i, mu, k, hi0, hi, hletter, u, hu, u', hu', s, hs, s', hs',
        huu', -, hclose, hclose'⟩ :=
      exists_peripheral_side_close_to_long_closing_side_at
        A.alphabet K hfour q hlet hqpos hDq hβ0 hθq hfar
    have hkK : k ∈ K mu := by
      have hklet := hlet (RelLetter.comp mu k) (List.mem_of_getElem? hletter)
      exact hklet
    let sides := Classical.choose (exists_relativeClosingPolygon A.alphabet q)
    have hpoly : IsClosedPolygonAt (relativeClosingVertex A.alphabet q) sides 0
        (q.length + 1) :=
      Classical.choose_spec (exists_relativeClosingPolygon A.alphabet q)
    have hclosing := hpoly.1 0 (by omega) (by omega)
    have hqK : RelLetter.listVal q ∈ K lam := by
      rw [hqval]
      simpa [K] using hhK
    obtain ⟨a, haK, hua⟩ := hproj lam 1 (RelLetter.listVal q) 1 hqK (one_mem _)
      (sides 0) (by simpa [relativeClosingVertex] using hclosing.1)
      (by simpa [relativeClosingVertex] using hclosing.2.1)
      (by simpa [relativeClosingVertex] using hclosing.2.2) u
      (by simpa [relativeClosingVertex] using hu)
    obtain ⟨b, hbK, hu'b⟩ := hproj lam 1 (RelLetter.listVal q) 1 hqK (one_mem _)
      (sides 0) (by simpa [relativeClosingVertex] using hclosing.1)
      (by simpa [relativeClosingVertex] using hclosing.2.1)
      (by simpa [relativeClosingVertex] using hclosing.2.2) u'
      (by simpa [relativeClosingVertex] using hu')
    let v : G := vertex 1 q (i - 1)
    have hperipheral := hpoly.1 i (by omega) (by omega)
    have hv0 : relativeClosingVertex A.alphabet q i = iotaG A.alphabet (v * 1) := by
      rw [show i = (i - 1) + 1 by omega, relativeClosingVertex_succ]
      simp [v]
    have hv1 : relativeClosingVertex A.alphabet q (i + 1) =
        iotaG A.alphabet (v * k) := by
      have hj : i - 1 < q.length := by omega
      have hget : q[i - 1]? = some (q[i - 1]'hj) := List.getElem?_eq_getElem hj
      have heq : q[i - 1]'hj = RelLetter.comp mu k := by
        apply Option.some.inj
        rw [← hget]
        exact hletter
      change iotaG A.alphabet (vertex 1 q i) = iotaG A.alphabet (v * k)
      congr 1
      rw [show i = (i - 1) + 1 by omega, vertex_succ q 1 (i - 1) hj, heq]
      rfl
    obtain ⟨c, hcK, hsc⟩ := hproj mu v 1 k (one_mem _) hkK (sides i)
      (by simpa only [hv0, hv1] using hperipheral.1)
      (by simpa only [hv0] using hperipheral.2.1)
      (by simpa only [hv0, hv1] using hperipheral.2.2) s
      (by simpa only [hv0, hv1] using hs)
    obtain ⟨d, hdK, hs'd⟩ := hproj mu v 1 k (one_mem _) hkK (sides i)
      (by simpa only [hv0, hv1] using hperipheral.1)
      (by simpa only [hv0] using hperipheral.2.1)
      (by simpa only [hv0, hv1] using hperipheral.2.2) s'
      (by simpa only [hv0, hv1] using hs')
    have hac : dist (iotaG A.alphabet a) (iotaG A.alphabet (v * c)) ≤ E := by
      have htri := dist_triangle4 (iotaG A.alphabet a) (sides 0 u)
        (sides i s) (iotaG A.alphabet (v * c))
      have hua' : dist (iotaG A.alphabet a) (sides 0 u) ≤ σ lam := by
        rw [dist_comm]
        simpa using hua
      dsimp [E]
      linarith [hσS lam, hσS mu]
    have hbd : dist (iotaG A.alphabet b) (iotaG A.alphabet (v * d)) ≤ E := by
      have htri := dist_triangle4 (iotaG A.alphabet b) (sides 0 u')
        (sides i s') (iotaG A.alphabet (v * d))
      have hu'b' : dist (iotaG A.alphabet b) (sides 0 u') ≤ σ lam := by
        rw [dist_comm]
        simpa using hu'b
      dsimp [E]
      linarith [hσS lam, hσS mu]
    have habModel : β - 2 * S ≤ dist (iotaG A.alphabet a) (iotaG A.alphabet b) := by
      have hgeo := hclosing.1.dist_eq
        (by simpa [relativeClosingVertex] using hu)
        (by simpa [relativeClosingVertex] using hu')
      have htri := dist_triangle4 (sides 0 u) (iotaG A.alphabet a)
        (iotaG A.alphabet b) (sides 0 u')
      have hua0 : dist (sides 0 u) (iotaG A.alphabet a) ≤ σ lam := by
        simpa using hua
      have hu'b0 : dist (iotaG A.alphabet b) (sides 0 u') ≤ σ lam := by
        rw [dist_comm]
        simpa using hu'b
      have huu0 : 0 ≤ u' - u := le_trans hβ0.le huu'
      have huuorder : u ≤ u' := sub_nonneg.mp huu0
      have habs : |u - u'| = u' - u := by
        rw [abs_of_nonpos (sub_nonpos.mpr huuorder)]
        ring
      rw [hgeo, habs] at htri
      linarith [hσS lam]
    have habWord : Rsep ≤ wordDist A.alphabet.carrier a b := by
      have hup := dist_iotaG_le A.alphabet a b
      dsimp [β] at habModel
      exact_mod_cast (by linarith : (Rsep : ℝ) ≤
        (wordDist A.alphabet.carrier a b : ℝ))
    obtain ⟨hmu, hvK⟩ := hRsep v mu lam a b c d haK hbK hcK hdK
      hac hbd habWord
    subst mu
    have hj : i - 1 < q.length := by omega
    have hcomp : (q[i - 1]'hj).IsCompOf lam := by
      have hget : q[i - 1]? = some (q[i - 1]'hj) := List.getElem?_eq_getElem hj
      have heq : q[i - 1]'hj = RelLetter.comp lam k := by
        apply Option.some.inj
        rw [← hget]
        exact hletter
      rw [heq]
      rfl
    exact notMem_fam_vertex_of_avoidsFrom K lam hav hj hcomp hvK

/-- The cyclic family with `E(g) = ⟨g⟩` is hyperbolically embedded over Hull's
original alphabet.  This is the no-input conclusion of Hull's Theorem 3.16
used in the manuscript. -/
theorem isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional
    {Λ : Type w} [Fintype Λ] [Nonempty Λ]
    (A : HullGeneratingSet G) (g : Λ → G)
    (hncom : PairwiseNonCommensurable g)
    (hlox : ∀ lam : Λ, IsLoxodromic (g lam) (Cayley.base A.alphabet))
    (hcyc : ∀ lam : Λ,
      Elementary.elementaryClosure (g lam) = Subgroup.zpowers (g lam)) :
    (coneOffFamily A.alphabet
      (fun lam => Subgroup.zpowers (g lam))).IsHyperbolicallyEmbedded := by
  exact isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_of_orbitBound
    A g hncom hlox hcyc
      (orbitBound_zpowersFamily_of_elementaryClosure_eq A g hncom hlox hcyc)

/-- The `heGX` conclusion in the exact situation returned by `yi`.  The
elementary-closure family is rewritten to the cyclic family and Theorem 3.16's
quantitative assembly supplies its hyperbolic embedding. -/
theorem heGXPair_of_elementaryClosure_eq_zpowers
    (A : HullGeneratingSet G) (g : Bool → G)
    (hlox : ∀ b : Bool, IsLoxodromic (g b) (Cayley.base A.alphabet))
    (hnc : ∀ (c : G) (p q : ℤ), p ≠ 0 → q ≠ 0 →
      c⁻¹ * g false ^ p * c ≠ g true ^ q)
    (hcyc : ∀ b : Bool,
      Elementary.elementaryClosure (g b) = Subgroup.zpowers (g b)) :
    (coneOffFamily A.alphabet
      (fun b => Elementary.elementaryClosure (g b))).IsHyperbolicallyEmbedded := by
  have hncom : PairwiseNonCommensurable g :=
    pairwiseNonCommensurable_bool_of_notCommensurable hnc
  have hemb := isHyperbolicallyEmbedded_zpowers_of_elementaryClosure_eq_unconditional
    A g hncom hlox hcyc
  have hfam : (fun b : Bool => Elementary.elementaryClosure (g b)) =
      fun b : Bool => Subgroup.zpowers (g b) := funext hcyc
  rwa [hfam]

/-- Hull's `yi` now implies the exact pair cone-off row with no separate
`heGX` literature input: the quantitative Theorem 3.16 assembly above is the
missing embedding step. -/
theorem existsHypEmbeddedConeOff₂_of_yi_theorem316
    (hyi : YiSuitablePair.{u}) : ExistsHypEmbeddedConeOff₂.{u} := by
  intro G _ A N hN
  obtain ⟨g, hgN, hglox, hnc, hcyc⟩ := hyi A hN
  have hemb := heGXPair_of_elementaryClosure_eq_zpowers A g hglox hnc hcyc
  have hfam : (fun b : Bool => Elementary.elementaryClosure (g b)) =
      fun b : Bool => Subgroup.zpowers (g b) := funext hcyc
  rw [hfam] at hemb
  refine ⟨fun b => Subgroup.zpowers (g b), ?_, hemb, g, ?_, hglox, ?_⟩
  · intro b
    exact Subgroup.zpowers_le.mpr (hgN b)
  · intro b
    exact Subgroup.mem_zpowers (g b)
  · intro x hx0 hx1
    exact eq_one_of_mem_zpowers_of_notCommensurable hnc hx0 hx1

end HullSC
end GroupApproximation
