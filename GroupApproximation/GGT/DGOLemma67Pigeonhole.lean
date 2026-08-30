import GroupApproximation.GGT.DGOLemma64

/-!
# DGO Lemma 6.7: the WPD pigeonhole core

The geometric input to DGO Lemma 6.7 is a long pair of oriented-close
quasi-axis segments.  Sampling those segments produces monotone exponent
families whose corresponding orbit points are close at two basepoints.  This
file proves the WPD conclusion from exactly that sampled data.

Unlike the existing acylindrical version, only the one element occurring in
the lemma is assumed WPD.  DGO Lemma 6.4 supplies finiteness at every
sufficiently large power, and finite pigeonhole then gives equal positive
powers.  The remaining quasi-axis sampling is kept separate so its constants
and orientation can follow the published statement literally.
-/

namespace GroupApproximation
namespace GGT

open GroupApproximation.HullGeometry

universe u v

variable {G : Type u} [Group G] {X : Type v} [PseudoMetricSpace X]
  [MulAction G X]

/-- A finite coarse stabilizer of two points gives the common-power
pigeonhole conclusion.  This is the finite-set core underlying both
acylindricity and WPD arguments. -/
theorem exists_common_zpow_of_pairStab_finite
    (hiso : IsIsometricAction G X) {ε : ℝ} {x y : X}
    (hfin : (pairStab G ε x y).Finite) {N : ℕ}
    (hcard : (pairStab G ε x y).ncard ≤ N)
    (g k : G) (a b : Fin (N + 1) → ℤ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hclose : ∀ i,
      dist ((g ^ (a i)) • x) ((k ^ (b i)) • x) ≤ ε ∧
      dist ((g ^ (a i)) • y) ((k ^ (b i)) • y) ≤ ε) :
    ∃ i j : Fin (N + 1), i ≠ j ∧
      a i - a j ≠ 0 ∧ b i - b j ≠ 0 ∧
      g ^ (a i - a j) = k ^ (b i - b j) := by
  classical
  let K : Set G := pairStab G ε x y
  have hKfin : K.Finite := hfin
  letI : Fintype K := hKfin.fintype
  let d : Fin (N + 1) → K := fun i =>
    ⟨g ^ (-a i) * k ^ (b i), by
      rw [mem_pairStab, dist_zpow_difference hiso,
        dist_zpow_difference hiso]
      exact hclose i⟩
  have hsmall : Fintype.card K < Fintype.card (Fin (N + 1)) := by
    rw [Set.fintypeCard_eq_ncard, Fintype.card_fin]
    dsimp [K]
    omega
  obtain ⟨i, j, hij, hdij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt d hsmall
  have heq : g ^ (-a i) * k ^ (b i) = g ^ (-a j) * k ^ (b j) :=
    congrArg Subtype.val hdij
  have hpower : g ^ (a i - a j) = k ^ (b i - b j) := by
    calc
      g ^ (a i - a j) =
          g ^ (a i) * (g ^ (-a j) * k ^ (b j)) * k ^ (-b j) := by group
      _ = g ^ (a i) * (g ^ (-a i) * k ^ (b i)) * k ^ (-b j) := by
        exact congrArg (fun z : G => g ^ (a i) * z * k ^ (-b j)) heq.symm
      _ = k ^ (b i - b j) := by group
  refine ⟨i, j, hij, ?_, ?_, hpower⟩
  · intro hz
    apply hij
    apply ha
    omega
  · intro hz
    apply hij
    apply hb
    omega

/-- If both sampled exponent families increase in the same orientation, the
finite-pigeonhole powers can be chosen positive, exactly as in DGO Lemma 6.7. -/
theorem exists_common_positive_zpow_of_pairStab_finite
    (hiso : IsIsometricAction G X) {ε : ℝ} {x y : X}
    (hfin : (pairStab G ε x y).Finite) {N : ℕ}
    (hcard : (pairStab G ε x y).ncard ≤ N)
    (g k : G) (a b : Fin (N + 1) → ℤ)
    (ha : StrictMono a) (hb : StrictMono b)
    (hclose : ∀ i,
      dist ((g ^ (a i)) • x) ((k ^ (b i)) • x) ≤ ε ∧
      dist ((g ^ (a i)) • y) ((k ^ (b i)) • y) ≤ ε) :
    ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ g ^ p = k ^ q := by
  obtain ⟨i, j, hij, -, -, hpower⟩ :=
    exists_common_zpow_of_pairStab_finite hiso hfin hcard g k a b
      ha.injective hb.injective hclose
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · refine ⟨a j - a i, b j - b i, sub_pos.mpr (ha hijlt),
      sub_pos.mpr (hb hijlt), ?_⟩
    calc
      g ^ (a j - a i) = (g ^ (a i - a j))⁻¹ := by group
      _ = (k ^ (b i - b j))⁻¹ := by rw [hpower]
      _ = k ^ (b j - b i) := by group
  · exact ⟨a i - a j, b i - b j, sub_pos.mpr (ha hjilt),
      sub_pos.mpr (hb hjilt), hpower⟩

/-- DGO Lemma 6.4 supplies the finite pair stabilizer at every sufficiently
large power; the preceding theorem converts any monotone matched sampling at
those two basepoints into equal positive powers. -/
theorem isWPDAtEventually_common_positive_zpow
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hwpd : IsWPDAtEventually h x) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ N : ℕ,
      ∀ (g k : G) (a b : Fin (N + 1) → ℤ),
        StrictMono a → StrictMono b →
        (∀ i,
          dist ((g ^ (a i)) • x) ((k ^ (b i)) • x) ≤ ε ∧
          dist ((g ^ (a i)) • ((h ^ M) • x))
            ((k ^ (b i)) • ((h ^ M) • x)) ≤ ε) →
        ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ g ^ p = k ^ q := by
  obtain ⟨M₀, hM₀⟩ := hwpd ε hε
  refine ⟨M₀, ?_⟩
  intro M hM
  have hfin : (pairStab G ε x ((h ^ M) • x)).Finite := hM₀ M hM
  let N := (pairStab G ε x ((h ^ M) • x)).ncard
  refine ⟨N, ?_⟩
  intro g k a b ha hb hclose
  exact exists_common_positive_zpow_of_pairStab_finite hiso hfin
    (N := N) (by exact le_rfl) g k a b ha hb hclose

/-- The monotone WPD pigeonhole threshold is uniform under simultaneous
conjugation of the WPD element and its basepoint.  This is the uniformity needed
when DGO Lemma 6.7 ranges over all translates of one quasi-axis. -/
theorem isWPDAtEventually_common_positive_zpow_conj
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hwpd : IsWPDAtEventually h x) {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ N : ℕ,
      ∀ (u k : G) (a b : Fin (N + 1) → ℤ),
        StrictMono a → StrictMono b →
        (∀ i,
          dist (((u * h * u⁻¹) ^ (a i)) • (u • x))
            ((k ^ (b i)) • (u • x)) ≤ ε ∧
          dist (((u * h * u⁻¹) ^ (a i)) •
              (((u * h * u⁻¹) ^ M) • (u • x)))
            ((k ^ (b i)) • (((u * h * u⁻¹) ^ M) • (u • x))) ≤ ε) →
        ∃ p q : ℤ, 0 < p ∧ 0 < q ∧
          (u * h * u⁻¹) ^ p = k ^ q := by
  obtain ⟨M₀, hM₀⟩ :=
    isWPDAtEventually_common_positive_zpow hiso hwpd hε
  refine ⟨M₀, ?_⟩
  intro M hM
  obtain ⟨N, hN⟩ := hM₀ M hM
  refine ⟨N, ?_⟩
  intro u k a b ha hb hclose
  let k' : G := u⁻¹ * k * u
  have haction (g : G) (e : ℤ) (y : X) :
      u • ((g ^ e) • y) = ((u * g * u⁻¹) ^ e) • (u • y) := by
    rw [← mul_smul, ← mul_smul]
    congr 1
    rw [conj_zpow]
    group
  have hkConj : u * k' * u⁻¹ = k := by
    dsimp [k']
    group
  obtain ⟨p, q, hp, hq, hpq⟩ := hN h k' a b ha hb (fun i => by
    have hfirst :
        dist ((h ^ (a i)) • x) ((k' ^ (b i)) • x) =
          dist (((u * h * u⁻¹) ^ (a i)) • (u • x))
            ((k ^ (b i)) • (u • x)) := by
      calc
        dist ((h ^ (a i)) • x) ((k' ^ (b i)) • x) =
            dist (u • ((h ^ (a i)) • x))
              (u • ((k' ^ (b i)) • x)) := (hiso u _ _).symm
        _ = dist (((u * h * u⁻¹) ^ (a i)) • (u • x))
              ((k ^ (b i)) • (u • x)) := by
            rw [haction, haction, hkConj]
    have hsecond :
        dist ((h ^ (a i)) • ((h ^ M) • x))
            ((k' ^ (b i)) • ((h ^ M) • x)) =
          dist (((u * h * u⁻¹) ^ (a i)) •
              (((u * h * u⁻¹) ^ M) • (u • x)))
            ((k ^ (b i)) • (((u * h * u⁻¹) ^ M) • (u • x))) := by
      have hMaction :
          u • ((h ^ M) • x) = ((u * h * u⁻¹) ^ M) • (u • x) := by
        rw [pow_conj]
        exact (smul_conj u (h ^ M) x).symm
      calc
        dist ((h ^ (a i)) • ((h ^ M) • x))
            ((k' ^ (b i)) • ((h ^ M) • x)) =
          dist (u • ((h ^ (a i)) • ((h ^ M) • x)))
            (u • ((k' ^ (b i)) • ((h ^ M) • x))) := (hiso u _ _).symm
        _ = dist (((u * h * u⁻¹) ^ (a i)) •
              (((u * h * u⁻¹) ^ M) • (u • x)))
            ((k ^ (b i)) • (((u * h * u⁻¹) ^ M) • (u • x))) := by
          rw [haction, haction, hkConj, hMaction]
    rw [hfirst, hsecond]
    exact hclose i)
  refine ⟨p, q, hp, hq, ?_⟩
  have hconjEq := congrArg (fun g : G => u * g * u⁻¹) hpq
  dsimp [k'] at hconjEq
  rw [← conj_zpow, ← conj_zpow] at hconjEq
  have hk' : u * (u⁻¹ * k * u) * u⁻¹ = k := by group
  rwa [hk'] at hconjEq

/-- **The WPD pigeonhole core of DGO Lemma 6.7.**  For a loxodromic WPD
element in a geodesic hyperbolic space, all sufficiently long sampled
oriented overlaps force the corresponding two elements to have equal positive
powers. -/
theorem dgoLemma67_pigeonhole {δ : ℝ}
    (hδ : IsHyperbolicSpace δ X) (hδ0 : 0 ≤ δ) (hgeo : IsGeodesicSpace X)
    (hiso : IsIsometricAction G X) {h : G} {x : X}
    (hlox : IsLoxodromic h x) (hwpd : IsWPDAt h x)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ N : ℕ,
      ∀ (g k : G) (a b : Fin (N + 1) → ℤ),
        StrictMono a → StrictMono b →
        (∀ i,
          dist ((g ^ (a i)) • x) ((k ^ (b i)) • x) ≤ ε ∧
          dist ((g ^ (a i)) • ((h ^ M) • x))
            ((k ^ (b i)) • ((h ^ M) • x)) ≤ ε) →
        ∃ p q : ℤ, 0 < p ∧ 0 < q ∧ g ^ p = k ^ q :=
  isWPDAtEventually_common_positive_zpow hiso
    (isWPDAtEventually_of_geodesic hδ hδ0 hgeo hiso hlox hwpd) hε

end GGT
end GroupApproximation
