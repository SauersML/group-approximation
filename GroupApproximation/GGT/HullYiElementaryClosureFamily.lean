import GroupApproximation.GGT.HullTheorem316Assembly
import GroupApproximation.GGT.ElementaryFiniteTransversalConsequences

/-!
# Finite elementary-closure families over Hull's alphabet

The cyclic-product construction needs to choose its peripheral letters after
the depth constant supplied by DGO Lemma 4.21(b).  This file proves that the
elementary closures of a finite pairwise non-commensurable loxodromic family
are hyperbolically embedded over Hull's prescribed alphabet.  In particular,
their relative balls are finite and the deep powers required by the product
construction can be chosen.

No global coarse-translation hypothesis is used.  For each loxodromic, the
geodesic realization of the Cayley graph and WPD give a finite transversal for
its cyclic subgroup in its elementary closure.  That finite transversal gives
the three inputs to Hull's Theorem 3.16 argument: closeness to powers,
quasiconvexity, and properness.  The quantitative polygon argument already in
`HullTheorem316Assembly` then proves the prescribed-base relative-ball bound.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.GGT
open GroupApproximation.GGT.Elementary
open GroupApproximation.GGT.OsinComponents
open GroupApproximation.GGT.DGOPolygonCut
open GroupApproximation.HullGeometry
open GroupApproximation.Olshanskii
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u w

variable {G : Type u} [Group G]

/-- Every loxodromic for a Hull generating set has a finite cyclic transversal
in its elementary closure. -/
theorem elementaryClosureFiniteTransversal_hullGeneratingSet
    (A : HullGeneratingSet G) {h : G}
    (hlox : IsLoxodromic h (Cayley.base A.alphabet)) :
    ElementaryClosureFiniteTransversal h := by
  have hdelta0 : 0 <= A.delta :=
    nonneg_of_isHyperbolicSpace A.hyperbolic (Cayley.base A.alphabet)
  let M := CayleyGeodesicModel.modelQuot A.alphabet A.hyperbolic hdelta0
    (CayleyGeodesicModel.isGeodesicRealisationQuot A.alphabet)
  letI : PseudoMetricSpace M.W := M.metric
  letI : MulAction G M.W := M.action
  have hlox' : IsLoxodromic h (M.iota (Cayley.base A.alphabet)) :=
    isLoxodromic_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hlox
  have hwpd : IsWPDAt h (Cayley.base A.alphabet) :=
    isWPDAt_of_isAcylindrical A.acylindrical hlox
  have hwpd' : IsWPDAt h (M.iota (Cayley.base A.alphabet)) :=
    isWPDAt_map M.distortion_nonneg M.hasAdditiveDistortion M.equivariant hwpd
  exact exists_finite_transversal_elementaryClosure_of_geodesic
    M.hyperbolic M.delta_nonneg M.geodesic M.isometric hlox' hwpd'

/-- A finite transversal bounds every elementary-closure element from a power
in the original word metric. -/
theorem exists_closureNearPowers_of_finiteTransversal
    (A : Alphabet G) {h : G} (hfin : ElementaryClosureFiniteTransversal h) :
    exists rho : Nat, ClosureNearPowers A h rho := by
  classical
  obtain ⟨F, hF, hcover⟩ := hfin
  obtain ⟨rho, hrho⟩ :=
    (hF.image fun f : G => wordDist A.carrier f 1).bddAbove
  refine ⟨rho, ?_⟩
  intro x hx
  obtain ⟨c, f, hf, rfl⟩ := hcover x hx
  refine ⟨c, ?_⟩
  have hdist := wordDist_left_invariant A.carrier (h ^ c)⁻¹
    (h ^ c * f) (h ^ c)
  have hsimp : (h ^ c)⁻¹ * (h ^ c * f) = f := by group
  have hsimp' : (h ^ c)⁻¹ * h ^ c = 1 := by group
  rw [hsimp, hsimp'] at hdist
  rw [← hdist]
  exact hrho ⟨f, hf, rfl⟩

/-- Finite choice makes the power-neighborhood constant uniform over a finite
family. -/
theorem exists_uniform_closureNearPowers_of_finiteTransversal
    {Lambda : Type w} [Fintype Lambda] (A : Alphabet G) (g : Lambda -> G)
    (hfin : forall i, ElementaryClosureFiniteTransversal (g i)) :
    exists rho : Nat, forall i, ClosureNearPowers A (g i) rho := by
  classical
  have hall : forall i : Lambda, exists rho : Nat,
      ClosureNearPowers A (g i) rho :=
    fun i => exists_closureNearPowers_of_finiteTransversal A (hfin i)
  choose rho hrho using hall
  refine ⟨Finset.univ.sup rho, ?_⟩
  intro i x hx
  obtain ⟨c, hc⟩ := hrho i x hx
  exact ⟨c, hc.trans (Finset.le_sup (f := rho) (Finset.mem_univ i))⟩

/-- Cone-off hyperbolicity for a finite elementary-closure family needs no
separation hypothesis.  Each elementary closure is uniformly close to the
cyclic subgroup of its loxodromic generator, and electrifying a finite
uniformly quasiconvex family preserves hyperbolicity.  Pairwise
non-commensurability enters only later, when proving local finiteness of the
relative metrics. -/
theorem exists_hyperbolic_coneOffFamily_elementaryClosure_family
    {Lambda : Type w} [Fintype Lambda]
    (A : HullGeneratingSet G) (g : Lambda -> G)
    (hlox : forall i, IsLoxodromic (g i) (Cayley.base A.alphabet)) :
    exists delta' : Real, IsHyperbolicSpace delta'
      (Cayley (coneOffFamily A.alphabet
        (fun i => elementaryClosure (g i))).alphabet) := by
  have hfin : forall i, ElementaryClosureFiniteTransversal (g i) :=
    fun i => elementaryClosureFiniteTransversal_hullGeneratingSet A (hlox i)
  obtain ⟨rho, hclose⟩ :=
    exists_uniform_closureNearPowers_of_finiteTransversal A.alphabet g hfin
  exact exists_hyperbolic_coneOffFamily_of_close A g hlox
    (fun i => elementaryClosure (g i))
    (fun i => zpowers_le_elementaryClosure (g i)) rho
    (fun i b hb => by
      obtain ⟨c, hc⟩ := hclose i b hb
      exact ⟨g i ^ c, Subgroup.mem_zpowers_iff.mpr ⟨c, rfl⟩, hc⟩)

/-- Finite-transversal quasiconvexity, translated to arbitrary left cosets in
the prescribed-alphabet geodesic model. -/
theorem exists_elementaryClosure_coset_projection_pointQuot
    (A : HullGeneratingSet G) {h : G}
    (hlox : IsLoxodromic h (Cayley.base A.alphabet))
    (hfin : ElementaryClosureFiniteTransversal h) :
    exists sigma : Real, 0 <= sigma ∧ forall (v a b : G),
      a ∈ elementaryClosure h -> b ∈ elementaryClosure h ->
      forall f : Real -> CayleyGeodesicModel.PointQuot A.alphabet,
        IsGeodesicSegment f 0
          (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))) ->
        f 0 = iotaG A.alphabet (v * a) ->
        f (dist (iotaG A.alphabet (v * a))
          (iotaG A.alphabet (v * b))) = iotaG A.alphabet (v * b) ->
        ∀ t ∈ Set.Icc (0 : Real)
            (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))),
          exists c : G, c ∈ elementaryClosure h ∧
            dist (f t) (iotaG A.alphabet (v * c)) <= sigma := by
  have hhyp : IsHyperbolicSpace (A.delta + 6)
      (CayleyGeodesicModel.PointQuot A.alphabet) :=
    CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point A.alphabet A.hyperbolic)
  have hdelta0 : 0 <= A.delta + 6 := by
    have hA := nonneg_of_isHyperbolicSpace A.hyperbolic
      (Cayley.base A.alphabet)
    linarith
  have hiso : IsIsometricAction G
      (CayleyGeodesicModel.PointQuot A.alphabet) :=
    CayleyGeodesicModel.isIsometricAction_pointQuot A.alphabet
  have hlox' : IsLoxodromic h (iotaG A.alphabet 1) := by
    apply isLoxodromic_map (C := (1 : Real)) zero_le_one
      (CayleyGeodesicModel.hasAdditiveDistortion_iotaQuot A.alphabet)
      (CayleyGeodesicModel.isEquivariant_iotaQuot A.alphabet)
      hlox
  have hqc : IsQuasiconvexOrbitAt (elementaryClosure h)
      (iotaG A.alphabet 1) :=
    isQuasiconvexOrbitAt_elementaryClosure_of_finiteTransversal
      hhyp hdelta0 hiso hlox' hfin
  obtain ⟨sigma, hsigma, hproj⟩ :=
    exists_coset_point_ne_of_quasiconvexOrbitAt hiso hqc
  refine ⟨sigma, hsigma, ?_⟩
  intro v a b ha hb f hf hf0 hf1 t ht
  have hva := iotaG_eq_smul_one A.alphabet (v * a)
  have hvb := iotaG_eq_smul_one A.alphabet (v * b)
  obtain ⟨c, hc, hnear⟩ := hproj v a b ha hb f
    (by rwa [← hva, ← hvb]) (by rwa [← hva]) (by rwa [← hva, ← hvb]) t
    (by rwa [← hva, ← hvb])
  exact ⟨c, hc, by rwa [← iotaG_eq_smul_one A.alphabet (v * c)] at hnear⟩

/-- The prescribed-alphabet displacement estimate underlying local finiteness,
stated for any finite peripheral family with geometric separation and uniform
coset projection. -/
theorem orbitBound_family_of_geometricSeparation_of_projection
    {Lambda : Type w} [Fintype Lambda] [Nonempty Lambda]
    (A : HullGeneratingSet G) (K : Lambda -> Subgroup G)
    (hsep : IsGeometricallySeparated A.alphabet K)
    (hprojAll : forall mu : Lambda, exists sigma : Real, 0 <= sigma ∧
      forall (v a b : G), a ∈ K mu -> b ∈ K mu ->
      forall f : Real -> CayleyGeodesicModel.PointQuot A.alphabet,
        IsGeodesicSegment f 0
          (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))) ->
        f 0 = iotaG A.alphabet (v * a) ->
        f (dist (iotaG A.alphabet (v * a))
          (iotaG A.alphabet (v * b))) = iotaG A.alphabet (v * b) ->
        ∀ t ∈ Set.Icc (0 : Real)
            (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))),
          exists c : G, c ∈ K mu ∧
            dist (f t) (iotaG A.alphabet (v * c)) <= sigma) :
    forall (lam : Lambda) (n : Nat), exists R : Real,
      forall h : G, h ∈ (coneOffFamily A.alphabet K).relBall lam n ->
        dist (Cayley.base A.alphabet) (h • Cayley.base A.alphabet) <= R := by
  classical
  choose sigma hsigma0 hproj using hprojAll
  let S : Real := ∑ mu : Lambda, sigma mu
  have hsigmaS : forall mu : Lambda, sigma mu <= S := by
    intro mu
    exact Finset.single_le_sum (fun nu _ => hsigma0 nu) (Finset.mem_univ mu)
  have hfour : Hyperbolic.IsFourPointHyperbolic A.alphabet.carrier ⌈A.delta⌉₊ :=
    isFourPointHyperbolic_of_isHyperbolicSpace_cayley A.alphabet A.hyperbolic
  intro lam n
  let D : Real := 3 * (((⌈A.delta⌉₊ : Nat) : Real) + 6) *
    ((Nat.clog 2 n : Real) + 1)
  let E : Real := 2 * S + D
  obtain ⟨Rsep, hRsep⟩ := geometricSeparation_of_pointQuot_witness
    A.alphabet K hsep E
  let beta : Real := (Rsep : Real) + 2 * S + 2
  have hbeta0 : 0 < beta := by
    have hS0 : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg (fun i _ ↦ hsigma0 i)
    have hRsep0 : 0 ≤ (Rsep : Real) := Nat.cast_nonneg Rsep
    dsimp [beta]
    linarith
  let theta : Real := (n : Real) * (beta + 4 * D) + 2 * (n : Real) + 1
  refine ⟨theta + 1, ?_⟩
  intro h hh
  obtain ⟨hhK, q, hlet, hqval, hav, hqlen⟩ := hh
  by_cases hq0 : q.length = 0
  · have hnil : q = [] := List.length_eq_zero_iff.mp hq0
    subst hnil
    simp only [RelLetter.listVal] at hqval
    subst h
    simp
    have htheta0 : 0 <= theta := by
      dsimp [theta]
      positivity
    linarith
  · have hqpos : 0 < q.length := Nat.pos_of_ne_zero hq0
    have hqn : q.length <= n := hqlen
    have hclog : Nat.clog 2 q.length <= Nat.clog 2 n :=
      Nat.clog_mono_right 2 hqn
    have hDq : 3 * (((⌈A.delta⌉₊ : Nat) : Real) + 6) *
        ((Nat.clog 2 q.length : Real) + 1) <= D := by
      dsimp [D]
      have hnonneg : 0 <= 3 * (((⌈A.delta⌉₊ : Nat) : Real) + 6) := by
        positivity
      gcongr
    have hthetaq : (q.length : Real) * (beta + 4 * D) +
        2 * (q.length : Real) < theta := by
      have hcast : (q.length : Real) <= (n : Real) := by exact_mod_cast hqn
      dsimp [theta]
      have hcoef : 0 <= beta + 4 * D := by positivity
      nlinarith
    by_contra hnot
    have hfar : theta <= dist (iotaG A.alphabet (RelLetter.listVal q))
        (iotaG A.alphabet 1) := by
      have hmodel := le_dist_iotaG A.alphabet (RelLetter.listVal q) 1
      have hcayley : dist (Cayley.base A.alphabet)
          (h • Cayley.base A.alphabet) =
          ((wordDist A.alphabet.carrier (RelLetter.listVal q) 1 : Nat) : Real) := by
        rw [dist_base_smul, ← hqval, ← wordDist_one_left,
          wordDist_comm A.alphabet.symmetricGenerating]
      have hlarge : theta + 1 < dist (Cayley.base A.alphabet)
          (h • Cayley.base A.alphabet) := lt_of_not_ge hnot
      rw [hcayley] at hlarge
      linarith
    obtain ⟨i, mu, k, hi0, hi, hletter, u, hu, u', hu', s, hs, s', hs',
        huu', -, hclose, hclose'⟩ :=
      exists_peripheral_side_close_to_long_closing_side_at
        A.alphabet K hfour q hlet hqpos hDq hbeta0 hthetaq hfar
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
      exact hhK
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
    have hv0 : relativeClosingVertex A.alphabet q i =
        iotaG A.alphabet (v * 1) := by
      rw [show i = (i - 1) + 1 by omega, relativeClosingVertex_succ]
      simp [v]
    have hv1 : relativeClosingVertex A.alphabet q (i + 1) =
        iotaG A.alphabet (v * k) := by
      have hj : i - 1 < q.length := by omega
      have hget : q[i - 1]? = some (q[i - 1]'hj) :=
        List.getElem?_eq_getElem hj
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
    have hac : dist (iotaG A.alphabet a) (iotaG A.alphabet (v * c)) <= E := by
      have htri := dist_triangle4 (iotaG A.alphabet a) (sides 0 u)
        (sides i s) (iotaG A.alphabet (v * c))
      have hua' : dist (iotaG A.alphabet a) (sides 0 u) <= sigma lam := by
        rw [dist_comm]
        simpa using hua
      dsimp [E]
      linarith [hsigmaS lam, hsigmaS mu]
    have hbd : dist (iotaG A.alphabet b) (iotaG A.alphabet (v * d)) <= E := by
      have htri := dist_triangle4 (iotaG A.alphabet b) (sides 0 u')
        (sides i s') (iotaG A.alphabet (v * d))
      have hu'b' : dist (iotaG A.alphabet b) (sides 0 u') <= sigma lam := by
        rw [dist_comm]
        simpa using hu'b
      dsimp [E]
      linarith [hsigmaS lam, hsigmaS mu]
    have habModel : beta - 2 * S <=
        dist (iotaG A.alphabet a) (iotaG A.alphabet b) := by
      have hgeo := hclosing.1.dist_eq
        (by simpa [relativeClosingVertex] using hu)
        (by simpa [relativeClosingVertex] using hu')
      have htri := dist_triangle4 (sides 0 u) (iotaG A.alphabet a)
        (iotaG A.alphabet b) (sides 0 u')
      have hua0 : dist (sides 0 u) (iotaG A.alphabet a) <= sigma lam := by
        simpa using hua
      have hu'b0 : dist (iotaG A.alphabet b) (sides 0 u') <= sigma lam := by
        rw [dist_comm]
        simpa using hu'b
      have huu0 : 0 <= u' - u := le_trans hbeta0.le huu'
      have habs : |u - u'| = u' - u := by
        rw [abs_of_nonpos (sub_nonpos.mpr (sub_nonneg.mp huu0))]
        ring
      rw [hgeo, habs] at htri
      linarith [hsigmaS lam]
    have habWord : Rsep <= wordDist A.alphabet.carrier a b := by
      have hup := dist_iotaG_le A.alphabet a b
      dsimp [beta] at habModel
      exact_mod_cast (by linarith : (Rsep : Real) <=
        (wordDist A.alphabet.carrier a b : Real))
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

/-- The elementary closures of a finite pairwise non-commensurable loxodromic
family are hyperbolically embedded over Hull's original alphabet. -/
theorem isHyperbolicallyEmbedded_elementaryClosure_family
    {Lambda : Type w} [Fintype Lambda] [Nonempty Lambda]
    (A : HullGeneratingSet G) (g : Lambda -> G)
    (hncom : PairwiseNonCommensurable g)
    (hlox : forall i, IsLoxodromic (g i) (Cayley.base A.alphabet)) :
    (coneOffFamily A.alphabet
      (fun i => elementaryClosure (g i))).IsHyperbolicallyEmbedded := by
  have hfin : forall i, ElementaryClosureFiniteTransversal (g i) :=
    fun i => elementaryClosureFiniteTransversal_hullGeneratingSet A (hlox i)
  obtain ⟨rho, hclose⟩ :=
    exists_uniform_closureNearPowers_of_finiteTransversal A.alphabet g hfin
  have hhyp :=
    exists_hyperbolic_coneOffFamily_elementaryClosure_family A g hlox
  have hdelta0 : 0 <= A.delta :=
    nonneg_of_isHyperbolicSpace A.hyperbolic (Cayley.base A.alphabet)
  have hgeo : IsGeodesicSpace (CayleyGeodesicModel.PointQuot A.alphabet) :=
    CayleyGeodesicModel.isGeodesicRealisationQuot A.alphabet
  have hhypQ : IsHyperbolicSpace (A.delta + 6)
      (CayleyGeodesicModel.PointQuot A.alphabet) :=
    CayleyGeodesicModel.isHyperbolicSpace_pointQuot
      (CayleyGeodesicModel.isHyperbolicSpace_point A.alphabet A.hyperbolic)
  have hisoQ : IsIsometricAction G
      (CayleyGeodesicModel.PointQuot A.alphabet) :=
    CayleyGeodesicModel.isIsometricAction_pointQuot A.alphabet
  have hacyQ : IsAcylindrical G
      (CayleyGeodesicModel.PointQuot A.alphabet) :=
    isAcylindrical_of_additiveDistortion_of_dense zero_le_one
      (CayleyGeodesicModel.hasAdditiveDistortion_iotaQuot A.alphabet)
      (CayleyGeodesicModel.hasDenseImage_iotaQuot A.alphabet)
      (CayleyGeodesicModel.isEquivariant_iotaQuot A.alphabet) hisoQ
      A.acylindrical
  have hunif : UniformCommonZpowThreshold G
      (CayleyGeodesicModel.PointQuot A.alphabet) :=
    uniformCommonZpowThreshold_of_acylindrical hhypQ (by linarith) hgeo hisoQ hacyQ
  have hsep : IsGeometricallySeparated A.alphabet
      (fun i => elementaryClosure (g i)) :=
    isGeometricallySeparated_of_uniformThreshold_of_finite
      A.alphabet g hncom hclose hlox hunif
  have hproj : forall i, exists sigma : Real, 0 <= sigma ∧
      forall (v a b : G), a ∈ elementaryClosure (g i) ->
        b ∈ elementaryClosure (g i) ->
      forall f : Real -> CayleyGeodesicModel.PointQuot A.alphabet,
        IsGeodesicSegment f 0
          (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))) ->
        f 0 = iotaG A.alphabet (v * a) ->
        f (dist (iotaG A.alphabet (v * a))
          (iotaG A.alphabet (v * b))) = iotaG A.alphabet (v * b) ->
        ∀ t ∈ Set.Icc (0 : Real)
            (dist (iotaG A.alphabet (v * a)) (iotaG A.alphabet (v * b))),
          exists c : G, c ∈ elementaryClosure (g i) ∧
            dist (f t) (iotaG A.alphabet (v * c)) <= sigma :=
    fun i => exists_elementaryClosure_coset_projection_pointQuot
      A (hlox i) (hfin i)
  have hbound := orbitBound_family_of_geometricSeparation_of_projection
    A (fun i => elementaryClosure (g i)) hsep hproj
  have hproper : forall i,
      ActsProperlyAt (elementaryClosure (g i)) (Cayley.base A.alphabet) :=
    fun i => actsProperlyAt_elementaryClosure_of_finiteTransversal
      (isIsometricAction_cayley A.alphabet) (hlox i) (hfin i)
  exact ⟨hhyp, locallyFinite_family_of_orbitBound_of_actsProperly hproper hbound⟩

end HullSC
end GroupApproximation
