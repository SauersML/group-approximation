import GroupApproximation.GGT.ElementaryBowditchProof
import GroupApproximation.GGT.WPDDGOReduction

/-!
# Osin's Lemma 5.12 from Corollary 6.12 alone, torsion included

`GGT.WPDDGOReduction` proves `RelativeCayleyNonElementary` --- Osin's Lemma 5.12
in the form `GGT.WPDAcylindricalHyperbolicity` records it --- from
`DGOCorollary612` **together with an infinite-order element of the peripheral
subgroup**, and keeps `DGOTheorem614` for the case where there is none.  This
module removes that hypothesis: `relativeCayleyNonElementary_of_612` is Lemma
5.12 from `DGOCorollary612` alone, for an infinite peripheral subgroup with no
assumption on its torsion.

## Where the missing element comes from

The whole difficulty is to produce an element outside `E(g)` for the loxodromic
`g` that Corollary 6.12 supplies.  For an infinite-order `h ∈ H` that is
immediate --- `h` would share a nonzero power with `g`, so a power of `h` would
be loxodromic, while coning off `H` makes every element of `H` elliptic.  For an
infinite torsion `H` that argument is unavailable, and Osin reaches the same
conclusion through a free subgroup, which costs the whole of
Dahmani--Guirardel--Osin §6.2.

`exists_notMem_elementaryClosure_of_infinite_bounded` gets it from acylindricity
instead --- a hypothesis Osin does not have in Lemma 5.12, but which
`RelativeCayleyNonElementary` carries, because the assembly applies Lemma 5.12
only to the generating set Theorem 5.4 produces:

> **An infinite subgroup with bounded orbit is never contained in `E(g)`**, for
> `g` loxodromic in an acylindrical action.

That is a fragment of Osin's Theorem 6.8 --- `E(g)` is virtually cyclic --- but a
fragment with a three-step proof.  Suppose `H ⊆ E(g)`.

1. **Orientation.**  For `a ∈ E(g)`, `a gⁿ a⁻¹ = g^{±n}` with `n ≠ 0`
   (`Elementary.conj_zpow_eq_or_of_mem_elementaryClosure`, which is the
   translation-length normalisation, not the classification).  Write `A` for the
   elements of `H` realising the `+` sign and `B` for the `−` sign.
2. **`A` is infinite** (`infinite_orientationPreserving`).  `H = A ∪ B`, so if
   `A` were finite then `B` would be infinite; and `b₀⁻¹b ∈ A` for `b₀, b ∈ B`,
   the two sign reversals cancelling on the common exponent `n₀n_b`, so `B` maps
   injectively into `A` and `A` is infinite after all.  This is the index-two
   argument, written without quotients.
3. **Counting.**  Acylindricity at `ε = r + 1` gives `R` and `N`.  Any `N + 1`
   elements of `A` share a nonzero exponent `n` --- multiply their exponents
   together, `exists_finset_conj_zpow_eq` --- and so all commute with `gⁿ`.  Then
   each of them moves both `x` and `(gⁿ)^K x` by at most `r`, the second because
   it commutes with `(gⁿ)^K`; taking `K` with `d(x, (gⁿ)^K x) ≥ R`, which
   loxodromy of `gⁿ` supplies, acylindricity allows at most `N` of them.

Nothing in the argument is specific to a Cayley graph or to a peripheral
subgroup: it is a statement about an infinite subgroup with a bounded orbit, and
`H` has one because every element of `H` is a letter of `Γ(G, X ⊔ ℋ)`.

## The residual leaf, weakened

`escapingIsLoxodromic_cayley_of_hyperbolic` is Bowditch's dichotomy at a bare
alphabet --- the same transport as
`ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic`, through the
geodesic realisation, with `GGT.escapingIsLoxodromic_of_geodesic` in place of the
common-power theorem.  With it,
`relativeCayleyNonElementary_of_exists_isEscaping` proves Lemma 5.12 from
**`∃ c, IsEscaping c`** in place of `∃ c, IsLoxodromic c`: what Corollary 6.12
must supply is only an element whose orbit leaves every bounded set.
`exists_isEscaping_of_dgoCorollary612` records that this is the weaker demand.
-/

namespace GroupApproximation
namespace GGT
namespace OsinLemma512

open GroupApproximation.HullGeometry
open GroupApproximation.Manuscript.NonMF.TorsionFree
open GroupApproximation.Manuscript.NonMF.AxisDichotomyRoute

universe u v

/-! ## Finitely many elements share one exponent -/

/-- **A common exponent for any finite family.**  If every element of an infinite
set `A` conjugates *some* nonzero power of `g` to itself, then for every `k`
there are `k` distinct elements of `A` and one nonzero exponent `n` that all `k`
of them fix: multiply the exponents together, one at a time.

The step is `a gᵖ a⁻¹ = gᵖ ⟹ a g^{pq} a⁻¹ = g^{pq}`, which is
`Elementary.conj_zpow_eq` and nothing else. -/
theorem exists_finset_conj_zpow_eq {G : Type u} [Group G] (g : G) {A : Set G}
    (hA : A.Infinite)
    (hAmem : ∀ a ∈ A, ∃ n : ℤ, n ≠ 0 ∧ a * g ^ n * a⁻¹ = g ^ n) (k : ℕ) :
    ∃ (n : ℤ) (F : Finset G), n ≠ 0 ∧ (↑F : Set G) ⊆ A ∧ F.card = k ∧
      ∀ a ∈ F, a * g ^ n * a⁻¹ = g ^ n := by
  classical
  have key : ∀ (y : G) (p q : ℤ), y * g ^ p * y⁻¹ = g ^ p →
      y * g ^ (p * q) * y⁻¹ = g ^ (p * q) := by
    intro y p q hy
    rw [zpow_mul g p q, Elementary.conj_zpow_eq y (g ^ p) q, hy]
  induction k with
  | zero => exact ⟨1, ∅, one_ne_zero, by simp, by simp, by simp⟩
  | succ k ih =>
      obtain ⟨n, F, hn, hFA, hcard, hFcomm⟩ := ih
      have hex : ∃ a, a ∈ A ∧ a ∉ F := by
        by_contra hcon
        refine hA (F.finite_toSet.subset ?_)
        intro y hy
        by_contra hy'
        exact hcon ⟨y, hy, fun hmem => hy' (Finset.mem_coe.mpr hmem)⟩
      obtain ⟨a, haA, haF⟩ := hex
      obtain ⟨m, hm, hmeq⟩ := hAmem a haA
      refine ⟨n * m, insert a F, mul_ne_zero hn hm, ?_, ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp (Finset.mem_coe.mp hy) with heq | hy'
        · rw [heq]
          exact haA
        · exact hFA (Finset.mem_coe.mpr hy')
      · rw [Finset.card_insert_of_notMem haF, hcard]
      · intro y hy
        rcases Finset.mem_insert.mp hy with heq | hy'
        · rw [heq]
          have h := key a m n hmeq
          rwa [mul_comm m n] at h
        · exact key y n m (hFcomm y hy')

/-! ## The orientation-preserving part is infinite -/

/-- **The index-two step, without quotients.**  If every element of an infinite
subgroup `H` conjugates some nonzero power of `g` to `g^{±n}`, then infinitely
many of them realise the `+` sign.

If the `+` part `A` were finite, the `−` part `B` would be infinite; and for
`b₀, b ∈ B` with exponents `n₀, n_b`, the element `b₀⁻¹b` conjugates `g^{n₀n_b}`
to itself, the two sign reversals cancelling.  So `B ⊆ b₀ · A`, and `A` finite
would make `B` finite. -/
theorem infinite_orientationPreserving {G : Type u} [Group G] (g : G)
    {H : Subgroup G} (hinf : (H : Set G).Infinite)
    (hsplit : ∀ h ∈ H, ∃ n : ℤ, n ≠ 0 ∧
      (h * g ^ n * h⁻¹ = g ^ n ∨ h * g ^ n * h⁻¹ = g ^ (-n))) :
    {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧ a * g ^ n * a⁻¹ = g ^ n}.Infinite := by
  have hconj : ∀ (c y : G) (k : ℤ), c⁻¹ * y ^ k * c = (c⁻¹ * y * c) ^ k := by
    intro c y k
    have h := Elementary.conj_zpow_eq c⁻¹ y k
    rwa [inv_inv] at h
  have hHAB : (H : Set G) ⊆
      {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧ a * g ^ n * a⁻¹ = g ^ n} ∪
      {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧ a * g ^ n * a⁻¹ = g ^ (-n)} := by
    intro h hh
    have hhH : h ∈ H := hh
    obtain ⟨n, hn, hcase⟩ := hsplit h hhH
    rcases hcase with h1 | h2
    · exact Or.inl ⟨hhH, n, hn, h1⟩
    · exact Or.inr ⟨hhH, n, hn, h2⟩
  intro hAfin
  have hBinf : {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧
      a * g ^ n * a⁻¹ = g ^ (-n)}.Infinite := by
    intro hBfin
    exact hinf ((hAfin.union hBfin).subset hHAB)
  obtain ⟨b₀, hb₀H, n₀, hn₀, hb₀eq⟩ := hBinf.nonempty
  have hb₀inv : b₀⁻¹ * g ^ (-n₀) * b₀ = g ^ n₀ := by
    rw [← hb₀eq]
    group
  have hstep : ∀ b ∈ {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧
        a * g ^ n * a⁻¹ = g ^ (-n)},
      b₀⁻¹ * b ∈ {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧
        a * g ^ n * a⁻¹ = g ^ n} := by
    intro b hb
    obtain ⟨hbH, nb, hnb, hbeq⟩ := hb
    refine ⟨H.mul_mem (H.inv_mem hb₀H) hbH, n₀ * nb, mul_ne_zero hn₀ hnb, ?_⟩
    have h1 : b * g ^ (n₀ * nb) * b⁻¹ = g ^ (-(n₀ * nb)) := by
      have e1 : g ^ (n₀ * nb) = (g ^ nb) ^ n₀ := by
        rw [← zpow_mul g nb n₀, mul_comm nb n₀]
      have e2 : (-nb) * n₀ = -(n₀ * nb) := by ring
      rw [e1, Elementary.conj_zpow_eq b (g ^ nb) n₀, hbeq,
        ← zpow_mul g (-nb) n₀, e2]
    have h2 : b₀⁻¹ * g ^ (-(n₀ * nb)) * b₀ = g ^ (n₀ * nb) := by
      have e3 : -(n₀ * nb) = (-n₀) * nb := by ring
      rw [e3, zpow_mul g (-n₀) nb, hconj b₀ (g ^ (-n₀)) nb, hb₀inv,
        ← zpow_mul g n₀ nb]
    calc (b₀⁻¹ * b) * g ^ (n₀ * nb) * (b₀⁻¹ * b)⁻¹
        = b₀⁻¹ * (b * g ^ (n₀ * nb) * b⁻¹) * b₀ := by group
      _ = b₀⁻¹ * g ^ (-(n₀ * nb)) * b₀ := by rw [h1]
      _ = g ^ (n₀ * nb) := h2
  have hBsub : {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧ a * g ^ n * a⁻¹ = g ^ (-n)}
      ⊆ (fun c : G => b₀ * c) ''
        {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧ a * g ^ n * a⁻¹ = g ^ n} := by
    intro b hb
    exact ⟨b₀⁻¹ * b, hstep b hb, mul_inv_cancel_left b₀ b⟩
  exact hBinf ((hAfin.image _).subset hBsub)

/-! ## An infinite bounded subgroup escapes the elementary closure -/

section Action

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- **An infinite subgroup with a bounded orbit is not contained in `E(g)`.**

Under an acylindrical action, for `g` loxodromic at `x` and `H` an infinite
subgroup every element of which moves `x` by at most `r`, some element of `H`
lies outside the elementary closure of `g`.

This is the fragment of Osin's Theorem 6.8 the argument needs, and it does not
need the classification.  Suppose the contrary.  Infinitely many elements of `H`
conjugate some nonzero power of `g` to *itself*
(`infinite_orientationPreserving`), so `N + 1` of them share one exponent `n`
(`exists_finset_conj_zpow_eq`) and commute with `gⁿ`, where `N` is the
acylindricity bound at `ε = r + 1`.  Each of them then moves both `x` and
`(gⁿ)^K x` by at most `r` --- the second by commuting past `(gⁿ)^K` --- and `K`
can be chosen with `d(x, (gⁿ)^K x) ≥ R` because `gⁿ` is loxodromic.
Acylindricity allows `N`. -/
theorem exists_notMem_elementaryClosure_of_infinite_bounded
    (hiso : IsIsometricAction G X) (hacy : IsAcylindrical G X) {x : X}
    {g : G} (hg : IsLoxodromic g x) {H : Subgroup G}
    (hinf : (H : Set G).Infinite) {r : ℝ}
    (hbdd : ∀ h ∈ H, dist x (h • x) ≤ r) :
    ∃ h ∈ H, h ∉ Elementary.elementaryClosure g := by
  by_contra hcon
  have hall : ∀ h : G, h ∈ H → h ∈ Elementary.elementaryClosure g := by
    intro h hh
    by_contra hne
    exact hcon ⟨h, hh, hne⟩
  have hAinf : {a : G | a ∈ H ∧ ∃ n : ℤ, n ≠ 0 ∧
      a * g ^ n * a⁻¹ = g ^ n}.Infinite := by
    refine infinite_orientationPreserving g hinf ?_
    intro h hh
    exact Elementary.conj_zpow_eq_or_of_mem_elementaryClosure hiso hg (hall h hh)
  have hr0 : (0 : ℝ) ≤ r := by
    have h1 := hbdd 1 H.one_mem
    rwa [one_smul, dist_self] at h1
  obtain ⟨R, N, hRN⟩ := hacy (r + 1) (by linarith)
  obtain ⟨n, F, hn, hFA, hcard, hFcomm⟩ :=
    exists_finset_conj_zpow_eq g hAinf (fun a ha => ha.2) (N + 1)
  have hlox : IsLoxodromic (g ^ n) x := isLoxodromic_zpow hiso hg hn
  have hev := hlox.isEscaping.eventually_ge_atTop R
  rw [Filter.eventually_atTop] at hev
  obtain ⟨K, hK⟩ := hev
  have hfar : R ≤ dist x (((g ^ n) ^ K) • x) := hK K le_rfl
  obtain ⟨hSfin, hScard⟩ := hRN x (((g ^ n) ^ K) • x) hfar
  have hFsub : (↑F : Set G) ⊆
      {k : G | dist x (k • x) ≤ r + 1 ∧
        dist (((g ^ n) ^ K) • x) (k • (((g ^ n) ^ K) • x)) ≤ r + 1} := by
    intro a ha
    have haF : a ∈ F := Finset.mem_coe.mp ha
    have haH : a ∈ H := (hFA ha).1
    have hax : dist x (a • x) ≤ r := hbdd a haH
    refine ⟨by linarith, ?_⟩
    have hKconj : a * (g ^ n) ^ K * a⁻¹ = (g ^ n) ^ K := by
      rw [← conj_pow, hFcomm a haF]
    have hswap : a * (g ^ n) ^ K = (g ^ n) ^ K * a := by
      calc a * (g ^ n) ^ K = (a * (g ^ n) ^ K * a⁻¹) * a := by group
        _ = (g ^ n) ^ K * a := by rw [hKconj]
    have hsmul : a • (((g ^ n) ^ K) • x) = ((g ^ n) ^ K) • (a • x) := by
      rw [← mul_smul, ← mul_smul, hswap]
    rw [hsmul, hiso ((g ^ n) ^ K) x (a • x)]
    linarith
  have hle : (↑F : Set G).ncard ≤ N :=
    le_trans (Set.ncard_le_ncard hFsub hSfin) hScard
  rw [Set.ncard_coe_finset, hcard] at hle
  omega

end Action

/-! ## Lemma 5.12 at the relative Cayley graph -/

section Cayley

variable {G : Type u} [Group G]

/-- **Every element of the peripheral subgroup is a letter**, so it moves the
basepoint of `Γ(G, X ⊔ ℋ)` by at most one.  This is the bounded orbit the
counting argument needs, and it holds for every family. -/
theorem dist_base_le_one_of_mem_fam (D : RelGenSet G Unit) {h : G}
    (hh : h ∈ D.fam ()) :
    dist (Cayley.base D.alphabet) (h • Cayley.base D.alphabet) ≤ (1 : ℝ) := by
  have hmem : h ∈ D.alphabet.carrier := RelGenSet.fam_subset_alphabet D () hh
  have hnorm : WordMetric.wordNorm D.alphabet.carrier h ≤ 1 :=
    WordMetric.wordNorm_le_one_of_mem hmem
  have hdist : dist (Cayley.base D.alphabet) (h • Cayley.base D.alphabet)
      = (WordMetric.wordDist D.alphabet.carrier 1 h : ℝ) := by simp
  rw [hdist, WordMetric.wordDist_one_left]
  exact_mod_cast hnorm

/-- **An infinite peripheral subgroup escapes `E(g)`**, with no hypothesis on its
torsion.  The subgroup is infinite and sits in the ball of radius one about the
basepoint, so `exists_notMem_elementaryClosure_of_infinite_bounded` applies. -/
theorem exists_notMem_elementaryClosure_of_infinite_fam
    (D : RelGenSet G Unit) (hacy : IsAcylindrical G (Cayley D.alphabet))
    {g : G} (hg : IsLoxodromic g (Cayley.base D.alphabet))
    (hinf : ((D.fam () : Subgroup G) : Set G).Infinite) :
    ∃ h ∈ D.fam (), h ∉ Elementary.elementaryClosure g := by
  refine exists_notMem_elementaryClosure_of_infinite_bounded
    (isIsometricAction_cayley D.alphabet) hacy hg hinf (r := 1) ?_
  intro h hh
  exact dist_base_le_one_of_mem_fam D hh

/-- **Two independent loxodromics from one loxodromic and an infinite peripheral
subgroup.**  The pair is `g` and its conjugate by the element the previous
theorem puts outside `E(g)`.

The infinite-order hypothesis of
`GGT.actsNonElementarily_of_isLoxodromic_of_infiniteOrder_mem_fam` is gone. -/
theorem actsNonElementarily_of_isLoxodromic_of_infinite_fam
    (D : RelGenSet G Unit) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley D.alphabet))
    (hacy : IsAcylindrical G (Cayley D.alphabet))
    {g : G} (hg : IsLoxodromic g (Cayley.base D.alphabet))
    (hinf : ((D.fam () : Subgroup G) : Set G).Infinite) :
    ActsNonElementarily (⊤ : Subgroup G) (Cayley.base D.alphabet) := by
  obtain ⟨h, -, hnot⟩ :=
    exists_notMem_elementaryClosure_of_infinite_fam D hacy hg hinf
  exact Elementary.actsNonElementarily_of_notMem_elementaryClosure
    (isIsometricAction_cayley D.alphabet)
    (ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic
      D.alphabet hδ hacy)
    (Subgroup.mem_top g) (Subgroup.mem_top h) hg hnot

/-- **Bowditch's dichotomy at a bare alphabet.**  Under an acylindrical action on
a hyperbolic `Γ(G,A)` an element whose orbit escapes every bounded set is
loxodromic.

The transport is the one of
`ElementaryMorse.independentOfNoCommonZpow_cayley_of_hyperbolic`: the estimate is
proved in the geodesic model, which `CayleyGeodesicModel.modelQuot` builds from
hyperbolicity alone, and pulled back along the vertex inclusion.  The model is
built on the metric *identification* `PointQuot A`, not on `Point A`: the
realisation `Point A` has distinct points at distance zero --- the two ends of
the loop `Letters A` adjoins at every vertex --- so `IsGeodesicSpace (Point A)`
is false, and `isGeodesicRealisationQuot` is the statement that survives.
`GGT.escapingIsLoxodromic_cayley` asks for a `HullGeneratingSet`, whose
non-elementarity clause a consumer proving non-elementarity cannot supply. -/
theorem escapingIsLoxodromic_cayley_of_hyperbolic (A : Alphabet G) {δ : ℝ}
    (hδ : IsHyperbolicSpace δ (Cayley A)) (hacy : IsAcylindrical G (Cayley A)) :
    Elementary.EscapingIsLoxodromic G (Cayley.base A) := by
  have hM : Nonempty (GeodesicModel G (Cayley A)) :=
    ⟨CayleyGeodesicModel.modelQuot A hδ
      (Elementary.nonneg_of_isHyperbolicSpace hδ (Cayley.base A))
      (CayleyGeodesicModel.isGeodesicRealisationQuot A)⟩
  obtain ⟨M⟩ := hM
  have hacyW : IsAcylindrical G M.W :=
    isAcylindrical_of_additiveDistortion_of_dense M.distortion_nonneg
      M.hasAdditiveDistortion M.hasDenseImage M.equivariant M.isometric hacy
  exact Elementary.escapingIsLoxodromic_of_map M.distortion_nonneg
    M.hasAdditiveDistortion M.equivariant
    (escapingIsLoxodromic_of_geodesic M.hyperbolic M.delta_nonneg M.geodesic
      M.isometric hacyW _)

end Cayley

/-! ## What Corollary 6.12 is now asked for -/

/-- **Osin's Lemma 5.12 from `DGOCorollary612` alone.**

`GGT.relativeCayleyNonElementary_of` needs `DGOTheorem614` as well, and
`GGT.relativeCayleyNonElementary_of_612_of_infiniteOrder` needs an infinite-order
peripheral element.  Neither is needed: the acylindricity hypothesis that
`RelativeCayleyNonElementary` carries supplies the element outside `E(g)` for an
arbitrary infinite peripheral subgroup. -/
theorem relativeCayleyNonElementary_of_612 (h612 : DGOCorollary612.{u}) :
    RelativeCayleyNonElementary.{u} := by
  intro G _inst D hemb hacy hnd
  obtain ⟨δ, hδ⟩ := hemb.hyperbolic
  obtain ⟨g, hg⟩ := h612 G D hemb hnd
  exact actsNonElementarily_of_isLoxodromic_of_infinite_fam D hδ hacy hg hnd.2

/-- **Lemma 5.12 from an escaping element.**  What the citation has to produce is
weaker than a loxodromic: an element whose orbit leaves every bounded set is
enough, Bowditch's dichotomy promoting it under the acylindricity that
`RelativeCayleyNonElementary` already assumes. -/
theorem relativeCayleyNonElementary_of_exists_isEscaping
    (hesc : ∀ (G : Type u) [Group G] (D : RelGenSet G Unit),
      D.IsHyperbolicallyEmbedded → IsNonDegenerate (D.fam ()) →
        ∃ c : G, IsEscaping c (Cayley.base D.alphabet)) :
    RelativeCayleyNonElementary.{u} := by
  intro G _inst D hemb hacy hnd
  obtain ⟨δ, hδ⟩ := hemb.hyperbolic
  obtain ⟨c, hc⟩ := hesc G D hemb hnd
  have hlox : IsLoxodromic c (Cayley.base D.alphabet) :=
    escapingIsLoxodromic_cayley_of_hyperbolic D.alphabet hδ hacy c hc
  exact actsNonElementarily_of_isLoxodromic_of_infinite_fam D hδ hacy hlox hnd.2

/-- The escaping form really is the weaker demand: a loxodromic element
escapes. -/
theorem exists_isEscaping_of_dgoCorollary612 (h612 : DGOCorollary612.{u}) :
    ∀ (G : Type u) [Group G] (D : RelGenSet G Unit),
      D.IsHyperbolicallyEmbedded → IsNonDegenerate (D.fam ()) →
        ∃ c : G, IsEscaping c (Cayley.base D.alphabet) := by
  intro G _inst D hemb hnd
  obtain ⟨g, hg⟩ := h612 G D hemb hnd
  exact ⟨g, hg.isEscaping⟩

end OsinLemma512
end GGT
end GroupApproximation
