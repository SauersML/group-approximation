import GroupApproximation.GGT.HullSCLemma49PowerChain
import GroupApproximation.GGT.HullSCLemma49StablePowerChain
import GroupApproximation.GGT.VanKampen.RelativeGreendlinger

/-!
# Hull Lemma 4.9 inputs for source-faithful relative Greendlinger

Osin's relative Greendlinger theorem is stated for a word satisfying a
`(lambda,c)` lower bound, while Hull's small-cancellation input and the power
estimates use `IsQuasiGeodesicChainAt`.  This module proves the exact
translations between those conventions.

In particular, a Hull `(4,1)` relator is an Osin `(1/4,1)` word, so every
`IsLemma44Input` gives `OsinCCondition`.  The long-period and stable-translation
power estimates give the same source boundary premise with their corresponding
reciprocal multiplicative constants.  These are the non-planar hypotheses
needed to apply source Lemma Gr0 to a planar realization of a power diagram.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.WordMetric
open GroupApproximation.HullGeometry

universe u w

/-! ## Identifying the two vertex conventions -/

/-- At basepoint one, Osin's vertex is the value of the corresponding word
prefix. -/
theorem lemma49_vertex_one_eq_listVal_take
    {G : Type u} [Group G] {Lambda : Type w}
    (word : List (GGT.RelLetter G Lambda)) (i : ℕ) :
    GGT.OsinComponents.vertex 1 word i =
      GGT.RelLetter.listVal (word.take i) := by
  rw [GGT.OsinComponents.vertex_eq_mul_listVal_take, one_mul]

/-- A chain written using prefix values is the same chain written using
Osin's vertices based at one. -/
theorem isQuasiGeodesicChainAt_vertex_one_iff
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {M : ℝ} {b : ℕ}
    {word : List (GGT.RelLetter G Lambda)} :
    GGT.IsQuasiGeodesicChainAt D.alphabet.carrier M b
        (fun i => GGT.OsinComponents.vertex 1 word i) word.length ↔
      GGT.IsQuasiGeodesicChainAt D.alphabet.carrier M b
        (fun i => GGT.RelLetter.listVal (word.take i)) word.length := by
  constructor
  · intro h
    simpa only [lemma49_vertex_one_eq_listVal_take] using h
  · intro h
    simpa only [lemma49_vertex_one_eq_listVal_take] using h

/-! ## Chain estimates as source word estimates -/

/-- A `(M,b)` chain is an Osin `(1/M,b)` quasi-geodesic word.  The two
lower bounds differ only by commuting the two real factors. -/
theorem isLambdaCQuasiGeodesicWord_of_chainAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {word : List (GGT.RelLetter G Lambda)}
    {M : ℝ} {b : ℕ}
    (hadmissible : RelWord.IsAdmissible D word)
    (hchain : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier M b
      (fun i => GGT.OsinComponents.vertex 1 word i) word.length) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / M) b word := by
  refine ⟨hadmissible, ?_⟩
  intro i j hij hj
  have hlower := (hchain i j hij hj).1
  change (1 / M) * ((j - i : ℕ) : ℝ) - (b : ℝ) ≤
    ((wordDist D.alphabet.carrier
      (GGT.OsinComponents.vertex 1 word i)
      (GGT.OsinComponents.vertex 1 word j) : ℕ) : ℝ)
  calc
    (1 / M) * ((j - i : ℕ) : ℝ) - (b : ℝ) =
        ((j - i : ℕ) : ℝ) / M - (b : ℝ) := by ring
    _ ≤ _ := hlower

/-- The same conversion when the chain is stored using values of prefixes,
as in Hull's `IsLemma44Input`. -/
theorem isLambdaCQuasiGeodesicWord_of_prefixChainAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {word : List (GGT.RelLetter G Lambda)}
    {M : ℝ} {b : ℕ}
    (hadmissible : RelWord.IsAdmissible D word)
    (hchain : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier M b
      (fun i => GGT.RelLetter.listVal (word.take i)) word.length) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / M) b word := by
  apply isLambdaCQuasiGeodesicWord_of_chainAt D hadmissible
  exact isQuasiGeodesicChainAt_vertex_one_iff.mpr hchain

/-- Weakening the additive error preserves Osin quasi-geodesicity. -/
theorem isLambdaCQuasiGeodesicWord_mono_error
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {word : List (GGT.RelLetter G Lambda)}
    {lambda c c' : ℝ}
    (hword : GGT.VanKampen.IsLambdaCQuasiGeodesicWord D lambda c word)
    (hc : c ≤ c') :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D lambda c' word := by
  refine ⟨hword.1, ?_⟩
  intro i j hij hj
  have hlower := hword.2 i j hij hj
  linarith

/-- Decreasing the multiplicative coefficient preserves Osin
quasi-geodesicity. -/
theorem isLambdaCQuasiGeodesicWord_mono_slope
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda} {word : List (GGT.RelLetter G Lambda)}
    {lambda lambda' c : ℝ}
    (hword : GGT.VanKampen.IsLambdaCQuasiGeodesicWord D lambda c word)
    (hle : lambda' ≤ lambda) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D lambda' c word := by
  refine ⟨hword.1, ?_⟩
  intro i j hij hj
  have hlower := hword.2 i j hij hj
  have hlength : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by positivity
  nlinarith

/-! ## Relator input -/

/-- Hull's `(4,1)` relator-chain field is exactly Osin's `(1/4,1)` word
field. -/
theorem RelWord.IsLemma44Input.relator_isLambdaCQuasiGeodesicWord
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hinput : RelWord.IsLemma44Input D W eps mu rho)
    {word : List (GGT.RelLetter G Lambda)} (hword : word ∈ W) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / 4) 1 word := by
  have hresult := isLambdaCQuasiGeodesicWord_of_prefixChainAt D
    (hinput.admissible word hword) (hinput.quasiGeodesic word hword)
  convert hresult using 1
  norm_num

/-- Every Hull Lemma 4.4 input supplies Osin's exact
`C(epsilon,mu,1/4,1,rho)` condition. -/
theorem RelWord.IsLemma44Input.toOsinCCondition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hinput : RelWord.IsLemma44Input D W eps mu rho) :
    GGT.VanKampen.OsinCCondition D W eps mu (1 / 4) 1 rho where
  toIsSmallCancellation := hinput.toIsSmallCancellation
  quasiGeodesic _ hword :=
    hinput.relator_isLambdaCQuasiGeodesicWord hword
  publishedPiecesSmall := hinput.publishedPiecesSmall

/-- Hull Lemma 4.9 input supplies the same Osin condition through its Lemma
4.4 fields. -/
theorem RelWord.IsLemma49Input.toOsinCCondition
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu : ℝ}
    (hinput : RelWord.IsLemma49Input D W eps mu rho) :
    GGT.VanKampen.OsinCCondition D W eps mu (1 / 4) 1 rho :=
  hinput.toIsLemma44Input.toOsinCCondition

/-- Hull's relator condition remains an Osin condition after decreasing the
multiplicative coefficient and increasing the additive error. -/
theorem RelWord.IsLemma44Input.toOsinCCondition_of_weakerConstants
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu lambda c : ℝ}
    (hinput : RelWord.IsLemma44Input D W eps mu rho)
    (hlambda : lambda ≤ 1 / 4) (hc : 1 ≤ c) :
    GGT.VanKampen.OsinCCondition D W eps mu lambda c rho where
  toIsSmallCancellation := hinput.toIsSmallCancellation
  quasiGeodesic word hword := by
    have hbase := hinput.relator_isLambdaCQuasiGeodesicWord hword
    have hslope := isLambdaCQuasiGeodesicWord_mono_slope hbase hlambda
    exact isLambdaCQuasiGeodesicWord_mono_error hslope hc
  publishedPiecesSmall := hinput.publishedPiecesSmall

/-- The same weakening is available directly from a Lemma 4.9 input. -/
theorem RelWord.IsLemma49Input.toOsinCCondition_of_weakerConstants
    {G : Type u} [Group G] {Lambda : Type w}
    {D : GGT.RelGenSet G Lambda}
    {W : Set (List (GGT.RelLetter G Lambda))}
    {eps rho : ℕ} {mu lambda c : ℝ}
    (hinput : RelWord.IsLemma49Input D W eps mu rho)
    (hlambda : lambda ≤ 1 / 4) (hc : 1 ≤ c) :
    GGT.VanKampen.OsinCCondition D W eps mu lambda c rho :=
  hinput.toIsLemma44Input.toOsinCCondition_of_weakerConstants hlambda hc

/-! ## Geodesic and power boundaries -/

/-- A geodesic word has the exact chain estimate with multiplicative
constant one and zero additive error. -/
theorem isQuasiGeodesicChainAt_one_zero_of_isGeodesicWord
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {first last : G}
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D first last word) :
    GGT.IsQuasiGeodesicChainAt D.alphabet.carrier 1 0
      (fun i => GGT.OsinComponents.vertex first word i) word.length := by
  intro i j hij hj
  have hlower := GGT.OsinComponents.sub_le_wordDist_vertex
    D hword i j hij hj
  have hupper := GGT.OsinComponents.wordDist_vertex_le'
    D hword.1 first hij hj
  constructor
  · simpa only [div_one, Nat.cast_zero, sub_zero] using
      (Nat.cast_le.mpr hlower :
        ((j - i : ℕ) : ℝ) ≤
          ((wordDist D.alphabet.carrier
            (GGT.OsinComponents.vertex first word i)
            (GGT.OsinComponents.vertex first word j) : ℕ) : ℝ))
  · exact hupper

/-- A geodesic word is an Osin `(1,0)` quasi-geodesic word when read from
basepoint one. -/
theorem isLambdaCQuasiGeodesicWord_one_zero_of_isGeodesicWord
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {last : G}
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 last word) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D 1 0 word := by
  have hresult := isLambdaCQuasiGeodesicWord_of_chainAt
    (M := (1 : ℝ)) (b := 0) D hword.1
      (isQuasiGeodesicChainAt_one_zero_of_isGeodesicWord D hword)
  simpa only [one_div, inv_one, Nat.cast_zero] using hresult

/-- A geodesic word also satisfies the weaker fixed source convention used
for Hull relators. -/
theorem isLambdaCQuasiGeodesicWord_quarter_one_of_isGeodesicWord
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {last : G}
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 last word) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / 4) 1 word := by
  have hone := isLambdaCQuasiGeodesicWord_one_zero_of_isGeodesicWord D hword
  have hquarterOne : (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hslope := isLambdaCQuasiGeodesicWord_mono_slope
    hone hquarterOne
  exact isLambdaCQuasiGeodesicWord_mono_error hslope (by norm_num)

/-- Any previously established power-chain bound is precisely the outer-word
hypothesis of source Gr0. -/
theorem isLambdaCQuasiGeodesicWord_lemma49BoundaryPower_of_chainAt
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda)
    {word : List (GGT.RelLetter G Lambda)} {n b : ℕ} {M : ℝ}
    (hadmissible : RelWord.IsAdmissible D word)
    (hchain : GGT.IsQuasiGeodesicChainAt D.alphabet.carrier M b
      (fun i => GGT.OsinComponents.vertex 1
        (lemma49BoundaryPower word n) i)
      (lemma49BoundaryPower word n).length) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / M) b
      (lemma49BoundaryPower word n) := by
  apply isLambdaCQuasiGeodesicWord_of_chainAt D
  · exact isAdmissible_lemma49BoundaryPower hadmissible n
  · exact hchain

/-- The long-period local-to-global estimate supplies a
`(1/4,8*delta+2)` source boundary. -/
theorem isLambdaCQuasiGeodesicWord_power_of_long_period
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) (N : Subgroup G) [N.Normal]
    {g : G} (hshort : IsShortestModuloConjugacy D.alphabet.carrier N g)
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {n delta : ℕ} (hn : 0 < n)
    (hdelta : Hyperbolic.IsFourPointHyperbolic D.alphabet.carrier delta)
    (hlong : 8 * delta + 2 ≤ word.length) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / 4)
      ((8 * delta + 2 : ℕ) : ℝ) (lemma49BoundaryPower word n) := by
  exact isLambdaCQuasiGeodesicWord_lemma49BoundaryPower_of_chainAt
    (n := n) (b := 8 * delta + 2) (M := (4 : ℝ)) D hword.1
      (isQuasiGeodesicChainAt_power_of_long_period
        D N hshort hword hn hdelta hlong)

/-- The stable-translation estimate supplies a `(1/M,4*L)` source boundary
for every bounded loxodromic period. -/
theorem isLambdaCQuasiGeodesicWord_power_of_stableTranslation
    {G : Type u} [Group G] {Lambda : Type w}
    (D : GGT.RelGenSet G Lambda) {g : G}
    {word : List (GGT.RelLetter G Lambda)}
    (hword : GGT.OsinComponents.IsGeodesicWord D 1 g word)
    {n L M : ℕ} (hwordPos : 0 < word.length)
    (hlength : word.length ≤ L) (hM : 0 < M)
    {d : ℝ} (hd : 0 < d)
    (hdStable : d ≤ stableTranslation g (Cayley.base D.alphabet))
    (hdL : d ≤ L) (hLM : (L : ℝ) ≤ d * M) :
    GGT.VanKampen.IsLambdaCQuasiGeodesicWord D (1 / (M : ℝ))
      ((4 * L : ℕ) : ℝ)
      (lemma49BoundaryPower word n) := by
  exact isLambdaCQuasiGeodesicWord_lemma49BoundaryPower_of_chainAt
    (n := n) (b := 4 * L) (M := (M : ℝ)) D hword.1
      (isQuasiGeodesicChainAt_power_of_stableTranslation D hword
        hwordPos hlength hM hd hdStable hdL hLM)

/-- The stable-power multiplicative constant can be chosen at least four, so
its reciprocal is no larger than the fixed relator coefficient `1/4`. -/
theorem exists_lemma49StablePowerConstant_four_le
    {d : ℝ} (hd : 0 < d) (L : ℕ) :
    ∃ M : ℕ, 4 ≤ M ∧ (L : ℝ) ≤ d * M := by
  obtain ⟨M, _hM, hLM⟩ := exists_lemma49StablePowerConstant hd L
  let M' := M + 4
  have hMM' : M ≤ M' := by
    dsimp [M']
    omega
  have hcast : (M : ℝ) ≤ (M' : ℕ) := Nat.cast_le.mpr hMM'
  have hproduct : d * (M : ℝ) ≤ d * (M' : ℕ) :=
    mul_le_mul_of_nonneg_left hcast hd.le
  refine ⟨M', ?_, le_trans hLM hproduct⟩
  dsimp [M']
  omega

/-- A natural denominator at least four gives an Osin coefficient no larger
than the relator coefficient. -/
theorem one_div_natCast_le_quarter {M : ℕ} (hM : 4 ≤ M) :
    (1 / (M : ℝ)) ≤ 1 / 4 := by
  have hcast : (4 : ℝ) ≤ (M : ℕ) := Nat.cast_le.mpr hM
  exact one_div_le_one_div_of_le (by norm_num) hcast

/-! ## Numerical source parameters -/

/-- The fixed relator slope `1/4` lies in Osin's source range. -/
theorem lemma49_sourceLambda_pos : (0 : ℝ) < 1 / 4 := by norm_num

/-- The fixed relator slope `1/4` is at most one. -/
theorem lemma49_sourceLambda_le_one : (1 / 4 : ℝ) ≤ 1 := by norm_num

/-- Hull's fixed additive relator error is nonnegative. -/
theorem lemma49_sourceError_nonneg : (0 : ℝ) ≤ 1 := by norm_num

end HullSC
end GroupApproximation
