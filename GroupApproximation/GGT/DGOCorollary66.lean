import GroupApproximation.GGT.ElementaryFiniteTransversalConsequences

/-!
# DGO Corollary 6.6: one power normalized by the elementary closure

For each element of `E(h)`, the stable-translation argument in
`ElementaryClosure` already gives a possibly element-dependent nonzero power
of `h` that is conjugated to itself or its inverse.  DGO Lemma 6.5 says only
finitely many `⟨h⟩`-cosets cover `E(h)`.  Multiplying the finitely many
representative exponents produces one nonzero power normalized by all of
`E(h)`, which is the uniform conclusion used in Corollary 6.6.
-/

namespace GroupApproximation
namespace GGT
namespace Elementary

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- A representative has a nonzero normalised power if it lies in `E(h)`;
outside `E(h)` the implication is vacuous.  This total form permits finite
choice over a transversal that may contain unused representatives. -/
theorem exists_conj_zpow_eq_or_of_mem_imp
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x) (a : G) :
    ∃ n : ℤ, n ≠ 0 ∧ (a ∈ elementaryClosure h →
      (a * h ^ n * a⁻¹ = h ^ n ∨ a * h ^ n * a⁻¹ = h ^ (-n))) := by
  by_cases ha : a ∈ elementaryClosure h
  · obtain ⟨n, hn, hrel⟩ :=
      conj_zpow_eq_or_of_mem_elementaryClosure hiso hlox ha
    exact ⟨n, hn, fun _ => hrel⟩
  · exact ⟨1, one_ne_zero, fun hmem => (ha hmem).elim⟩

/-- **DGO Corollary 6.6, uniform-power clause.**  If `⟨h⟩` has finite index in
`E(h)`, one nonzero power of `h` is conjugated to itself or its inverse by
every element of `E(h)`. -/
theorem exists_uniform_normal_zpow_of_finiteTransversal
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x)
    (hfin : ElementaryClosureFiniteTransversal h) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ g : G, g ∈ elementaryClosure h →
      (g * h ^ N * g⁻¹ = h ^ N ∨ g * h ^ N * g⁻¹ = h ^ (-N)) := by
  classical
  obtain ⟨F, hF, hcover⟩ := hfin
  choose n hn hrel using fun a : G =>
    exists_conj_zpow_eq_or_of_mem_imp hiso hlox a
  let N : ℤ := ∏ a ∈ hF.toFinset, n a
  have hN : N ≠ 0 := by
    dsimp [N]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hn a
  refine ⟨N, hN, ?_⟩
  intro g hg
  obtain ⟨c, a, haF, rfl⟩ := hcover g hg
  have haE : a ∈ elementaryClosure h := by
    have hhpow : h ^ c ∈ elementaryClosure h :=
      Subgroup.zpow_mem _ (self_mem_elementaryClosure h) c
    exact ((elementaryClosure h).mul_mem_cancel_left hhpow).mp
      (show h ^ c * a ∈ elementaryClosure h from hg)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (hF.mem_toFinset.mpr haF)
  have hNk : N = n a * k := by simpa [N] using hk
  have hconjN :
      a * h ^ N * a⁻¹ = h ^ N ∨ a * h ^ N * a⁻¹ = h ^ (-N) := by
    rcases hrel a haE with hpos | hneg
    · left
      calc
        a * h ^ N * a⁻¹ = a * (h ^ n a) ^ k * a⁻¹ := by rw [hNk, zpow_mul]
        _ = (a * h ^ n a * a⁻¹) ^ k := by rw [conj_zpow_eq]
        _ = (h ^ n a) ^ k := by rw [hpos]
        _ = h ^ N := by rw [← zpow_mul, ← hNk]
    · right
      calc
        a * h ^ N * a⁻¹ = a * (h ^ n a) ^ k * a⁻¹ := by rw [hNk, zpow_mul]
        _ = (a * h ^ n a * a⁻¹) ^ k := by rw [conj_zpow_eq]
        _ = (h ^ (-n a)) ^ k := by rw [hneg]
        _ = h ^ (-N) := by
          rw [← zpow_mul]
          congr 1
          rw [hNk]
          ring
  rcases hconjN with hpos | hneg
  · left
    calc
      (h ^ c * a) * h ^ N * (h ^ c * a)⁻¹ =
          h ^ c * (a * h ^ N * a⁻¹) * h ^ (-c) := by group
      _ = h ^ c * h ^ N * h ^ (-c) := by rw [hpos]
      _ = h ^ N := by rw [← zpow_add, ← zpow_add]; congr 1; ring
  · right
    calc
      (h ^ c * a) * h ^ N * (h ^ c * a)⁻¹ =
          h ^ c * (a * h ^ N * a⁻¹) * h ^ (-c) := by group
      _ = h ^ c * h ^ (-N) * h ^ (-c) := by rw [hneg]
      _ = h ^ (-N) := by rw [← zpow_add, ← zpow_add]; congr 1; ring

/-- The uniform exponent can be chosen to be a positive natural number, as in
the published statement of Corollary 6.6. -/
theorem exists_uniform_normal_positive_pow_of_finiteTransversal
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x)
    (hfin : ElementaryClosureFiniteTransversal h) :
    ∃ r : ℕ, 0 < r ∧ ∀ g : G, g ∈ elementaryClosure h →
      (g * h ^ (r : ℤ) * g⁻¹ = h ^ (r : ℤ) ∨
        g * h ^ (r : ℤ) * g⁻¹ = h ^ (-(r : ℤ))) := by
  obtain ⟨N, hN, hnormal⟩ :=
    exists_uniform_normal_zpow_of_finiteTransversal hiso hlox hfin
  let r := N.natAbs
  have hr : 0 < r := Int.natAbs_pos.mpr hN
  have hsign : N = (r : ℤ) ∨ N = -(r : ℤ) := by
    dsimp [r]
    omega
  refine ⟨r, hr, ?_⟩
  intro g hg
  rcases hnormal g hg with hpos | hneg
  · rcases hsign with hNpos | hNneg
    · left
      simpa only [hNpos] using hpos
    · left
      have hp : g * h ^ (-(r : ℤ)) * g⁻¹ = h ^ (-(r : ℤ)) := by
        simpa only [hNneg] using hpos
      calc
        g * h ^ (r : ℤ) * g⁻¹ = (g * h ^ (-(r : ℤ)) * g⁻¹)⁻¹ := by group
        _ = (h ^ (-(r : ℤ)))⁻¹ := by rw [hp]
        _ = h ^ (r : ℤ) := by group
  · rcases hsign with hNpos | hNneg
    · right
      simpa only [hNpos] using hneg
    · right
      have hn : g * h ^ (-(r : ℤ)) * g⁻¹ = h ^ (r : ℤ) := by
        simpa only [hNneg, neg_neg] using hneg
      calc
        g * h ^ (r : ℤ) * g⁻¹ = (g * h ^ (-(r : ℤ)) * g⁻¹)⁻¹ := by group
        _ = (h ^ (r : ℤ))⁻¹ := by rw [hn]
        _ = h ^ (-(r : ℤ)) := by group

/-- The orientation-preserving part `E⁺(h)`: an element inverse-conjugates
some nonzero power of `h` to itself. -/
def positiveElementaryClosure (h : G) : Set G :=
  {g : G | ∃ n : ℤ, n ≠ 0 ∧ g⁻¹ * h ^ n * g = h ^ n}

/-- **DGO Corollary 6.6, centralizer clause.**  Under the finite-index
conclusion of Lemma 6.5, the orientation-preserving part of `E(h)` is the
centralizer of one positive power of `h`. -/
theorem exists_positiveElementaryClosure_eq_centralizer_pow
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x)
    (hfin : ElementaryClosureFiniteTransversal h) :
    ∃ r : ℕ, 0 < r ∧
      positiveElementaryClosure h = {g : G | Commute g (h ^ (r : ℤ))} := by
  obtain ⟨r, hr, hnormal⟩ :=
    exists_uniform_normal_positive_pow_of_finiteTransversal hiso hlox hfin
  refine ⟨r, hr, Set.ext ?_⟩
  intro g
  constructor
  · rintro ⟨n, hn, hsame⟩
    have hginvE : g⁻¹ ∈ elementaryClosure h :=
      mem_elementaryClosure.mpr ⟨n, n, hn, hn, by simpa only [inv_inv] using hsame⟩
    rcases hnormal g⁻¹ hginvE with hpos | hneg
    · show Commute g (h ^ (r : ℤ))
      have hpos' : g⁻¹ * h ^ (r : ℤ) * g = h ^ (r : ℤ) := by
        simpa only [inv_inv] using hpos
      rw [commute_iff_eq]
      calc
        g * h ^ (r : ℤ) = g * (g⁻¹ * h ^ (r : ℤ) * g) := by rw [hpos']
        _ = h ^ (r : ℤ) * g := by group
    · exfalso
      have hneg' : g⁻¹ * h ^ (r : ℤ) * g = h ^ (-(r : ℤ)) := by
        simpa only [inv_inv] using hneg
      have heqSame :
          g⁻¹ * h ^ ((r : ℤ) * n) * g = h ^ ((r : ℤ) * n) := by
        calc
          g⁻¹ * h ^ ((r : ℤ) * n) * g = g⁻¹ * (h ^ n) ^ (r : ℤ) * g := by
            rw [mul_comm, zpow_mul]
          _ = (g⁻¹ * h ^ n * g) ^ (r : ℤ) := by
            simpa only [inv_inv] using (conj_zpow_eq g⁻¹ (h ^ n) (r : ℤ))
          _ = (h ^ n) ^ (r : ℤ) := by rw [hsame]
          _ = h ^ ((r : ℤ) * n) := by rw [← zpow_mul, mul_comm]
      have heqNeg :
          g⁻¹ * h ^ ((r : ℤ) * n) * g = h ^ (-((r : ℤ) * n)) := by
        calc
          g⁻¹ * h ^ ((r : ℤ) * n) * g =
              g⁻¹ * (h ^ (r : ℤ)) ^ n * g := by rw [zpow_mul]
          _ = (g⁻¹ * h ^ (r : ℤ) * g) ^ n := by
            simpa only [inv_inv] using (conj_zpow_eq g⁻¹ (h ^ (r : ℤ)) n)
          _ = (h ^ (-(r : ℤ))) ^ n := by rw [hneg']
          _ = h ^ (-((r : ℤ) * n)) := by
            rw [← zpow_mul]
            congr 1
            ring
      have hpowers : h ^ ((r : ℤ) * n) = h ^ (-((r : ℤ) * n)) :=
        heqSame.symm.trans heqNeg
      have hinj : Function.Injective (fun k : ℤ => h ^ k) :=
        injective_zpow_iff_not_isOfFinOrder.mpr
          (not_isOfFinOrder_of_isLoxodromic hlox)
      have hexp : (r : ℤ) * n = -((r : ℤ) * n) := hinj hpowers
      let z : ℤ := (r : ℤ) * n
      have hz : z = -z := by simpa only [z] using hexp
      have hz0 : z = 0 := by omega
      have hprod : (r : ℤ) * n = 0 := by simpa only [z] using hz0
      rcases mul_eq_zero.mp hprod with hr0 | hn0
      · have hrz : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
        exact hrz hr0
      · exact hn hn0
  · intro hcomm
    change Commute g (h ^ (r : ℤ)) at hcomm
    refine ⟨r, by exact_mod_cast hr.ne', ?_⟩
    rw [commute_iff_eq] at hcomm
    calc
      g⁻¹ * h ^ (r : ℤ) * g = g⁻¹ * (h ^ (r : ℤ) * g) := by group
      _ = g⁻¹ * (g * h ^ (r : ℤ)) := by rw [hcomm]
      _ = h ^ (r : ℤ) := by group

/-! ## The three equivalent membership conditions -/

/-- **DGO Corollary 6.6, `(a) ↔ (b)`, in integer-power form.**  Membership in
`E(h)` is equivalent to inverse-conjugating one nonzero power of `h` to that
same power or its inverse.  The inverse-conjugation orientation is the one in
the published statement. -/
theorem mem_elementaryClosure_iff_exists_inv_conj_zpow_eq_or
    (hiso : IsIsometricAction G X) {h g : G} {x : X}
    (hlox : IsLoxodromic h x) :
    g ∈ elementaryClosure h ↔
      ∃ n : ℤ, n ≠ 0 ∧
        (g⁻¹ * h ^ n * g = h ^ n ∨ g⁻¹ * h ^ n * g = h ^ (-n)) := by
  constructor
  · intro hg
    have hginv : g⁻¹ ∈ elementaryClosure h :=
      (elementaryClosure h).inv_mem hg
    obtain ⟨n, hn, hrel⟩ :=
      conj_zpow_eq_or_of_mem_elementaryClosure hiso hlox hginv
    exact ⟨n, hn, by simpa only [inv_inv] using hrel⟩
  · rintro ⟨n, hn, hpos | hneg⟩
    · have hginv : g⁻¹ ∈ elementaryClosure h := by
        refine mem_elementaryClosure.mpr ⟨n, n, hn, hn, ?_⟩
        simpa only [inv_inv] using hpos
      simpa only [inv_inv] using (elementaryClosure h).inv_mem hginv
    · have hginv : g⁻¹ ∈ elementaryClosure h := by
        refine mem_elementaryClosure.mpr
          ⟨n, -n, hn, neg_ne_zero.mpr hn, ?_⟩
        simpa only [inv_inv] using hneg
      simpa only [inv_inv] using (elementaryClosure h).inv_mem hginv

/-- **DGO Corollary 6.6, `(a) ↔ (c)`.**  Membership in `E(h)` is equivalent
to inverse-conjugating some nonzero power of `h` to some nonzero power. -/
theorem mem_elementaryClosure_iff_exists_inv_conj_zpow_eq
    {h g : G} :
    g ∈ elementaryClosure h ↔
      ∃ k m : ℤ, k ≠ 0 ∧ m ≠ 0 ∧ g⁻¹ * h ^ k * g = h ^ m := by
  constructor
  · intro hg
    have hginv : g⁻¹ ∈ elementaryClosure h :=
      (elementaryClosure h).inv_mem hg
    obtain ⟨k, m, hk, hm, heq⟩ := mem_elementaryClosure.mp hginv
    exact ⟨k, m, hk, hm, by simpa only [inv_inv] using heq⟩
  · rintro ⟨k, m, hk, hm, heq⟩
    have hginv : g⁻¹ ∈ elementaryClosure h := by
      refine mem_elementaryClosure.mpr ⟨k, m, hk, hm, ?_⟩
      simpa only [inv_inv] using heq
    simpa only [inv_inv] using (elementaryClosure h).inv_mem hginv

end Elementary
end GGT
end GroupApproximation
