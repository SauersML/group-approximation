import GroupApproximation.Sofic.NormUltraproductSequentialExtraction

/-!
# Operator-norm MF groups and the cofinite norm-matrix corona

This file formalizes the group property called MF by
Carrión--Dadarlat--Eckhardt: a group embeds in the unitary quotient of a
sequence of finite complex matrix algebras by operator-norm-null sequences.

The quotient below is built directly from sequences of unitary matrices.  Its
null subgroup uses the cofinite filter, so it is the unitary-sequence model of
the usual `ℓ∞/c₀` norm matrix corona, rather than an ultrafilter quotient.
`Analysis.NormMatrixCoronaUnitary` constructs the genuine complex C-star
quotient, proves by coordinatewise polar correction that every quotient
unitary has a unitary-sequence lift, and bundles the canonical multiplicative
equivalence.  `Sofic.CDEOperatorMF` states the literal CDE predicate and proves
its equivalence with `IsOperatorMF` below.

The extraction theorem is deliberately direct.  If a marked element survives
in a cofinite corona, a choice of unitary lifts is asymptotically
multiplicative, while nontriviality means that the marked distance is bounded
below frequently.  Intersecting each eventual finite multiplication test with
that frequent separation set produces a sequential marked almost
representation.  Thus the analytic kill theorem can obstruct the standard MF
property without appealing to an informal equivalence with `IsWeakMF`.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G]

/-! ## The cofinite norm-matrix corona -/

variable (X : ℕ → FiniteModel)

/-- A unitary sequence converges to the identity in operator norm along the
cofinite filter. -/
def IsNullCofiniteOpSeq
    (v : ∀ n, Matrix.unitaryGroup (X n) ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.cofinite,
    opLength (X n) (v n) < ε

/-- Operator-norm-null unitary sequences form a normal subgroup. -/
def nullCofiniteOpSubgroup :
    Subgroup (∀ n, Matrix.unitaryGroup (X n) ℂ) where
  carrier := {v | IsNullCofiniteOpSeq X v}
  one_mem' := by
    intro ε hε
    filter_upwards with n
    simpa using hε
  mul_mem' := by
    intro v w hv hw ε hε
    filter_upwards [hv (ε / 2) (by linarith), hw (ε / 2) (by linarith)]
      with n hvn hwn
    exact (opLength_mul_le (X n) (v n) (w n)).trans_lt (by linarith)
  inv_mem' := by
    intro v hv ε hε
    filter_upwards [hv ε hε] with n hn
    change opLength (X n) (v n)⁻¹ < ε
    rwa [opLength_inv]

instance nullCofiniteOpSubgroup_normal :
    (nullCofiniteOpSubgroup X).Normal where
  conj_mem := by
    intro v hv t ε hε
    filter_upwards [hv ε hε] with n hn
    change opLength (X n) (t n * v n * (t n)⁻¹) < ε
    rwa [opLength_conj]

/-- The unitary-sequence presentation of the unitary group of the norm matrix
corona `∏ Mₙ / ⊕ Mₙ`.

The canonical isomorphism with the unitary group of the C-star quotient is
`normMatrixCoronaUnitaryEquiv`.

The matrix sizes are required to be positive in `IsOperatorMF`; keeping that
condition on the embedding predicate makes this quotient reusable for
intermediate constructions that may contain empty coordinates. -/
abbrev NormMatrixCoronaUnitary : Type _ :=
  (∀ n, Matrix.unitaryGroup (X n) ℂ) ⧸ nullCofiniteOpSubgroup X

/-- Operator-norm MF in the standard group sense: faithful representation in
the unitary-sequence quotient of a cofinite norm matrix corona. -/
def IsOperatorMF (G : Type u) [Group G] : Prop :=
  ∃ X : ℕ → FiniteModel,
    (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ rho : G →* NormMatrixCoronaUnitary X, Function.Injective rho

/-! ## A surviving mark yields a sequential marked model -/

/-- A lift of a homomorphism into the cofinite corona is eventually
multiplicative at every positive tolerance. -/
theorem normMatrixCorona_lift_eventually_multiplicative
    (rho : G →* NormMatrixCoronaUnitary X)
    (lift : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g) :
    ∀ g h ε, 0 < ε → ∀ᶠ n in Filter.cofinite,
      ‖(lift (g * h) n : Matrix (X n) (X n) ℂ) -
        (lift g n : Matrix (X n) (X n) ℂ) * lift h n‖ ≤ ε := by
  intro g h ε hε
  have heq :
      (QuotientGroup.mk (lift g * lift h) : NormMatrixCoronaUnitary X) =
        QuotientGroup.mk (lift (g * h)) := by
    rw [QuotientGroup.mk_mul, hlift, hlift, hlift, map_mul]
  have hnull :
      (lift g * lift h)⁻¹ * lift (g * h) ∈ nullCofiniteOpSubgroup X :=
    QuotientGroup.eq.mp heq
  filter_upwards [hnull ε hε] with n hn
  change opLength (X n) ((lift g n * lift h n)⁻¹ * lift (g * h) n) < ε at hn
  rw [opLength_inv_mul] at hn
  exact hn.le

/-- Nontriviality in the cofinite corona gives a fixed positive marked gap on
infinitely many coordinates. -/
theorem normMatrixCorona_lift_frequently_marked_separated
    (rho : G →* NormMatrixCoronaUnitary X)
    (lift : G → ∀ n, Matrix.unitaryGroup (X n) ℂ)
    (hlift : ∀ g, QuotientGroup.mk (lift g) = rho g)
    {z : G} (hz : rho z ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ᶠ n in Filter.cofinite,
      δ ≤ ‖(lift z n : Matrix (X n) (X n) ℂ) - lift 1 n‖ := by
  have hz1 : rho z ≠ rho 1 := by simpa using hz
  have hnot : (lift 1)⁻¹ * lift z ∉ nullCofiniteOpSubgroup X := by
    intro hc
    apply hz1
    rw [← hlift z, ← hlift 1]
    exact (QuotientGroup.eq.mpr hc).symm
  have hex : ∃ δ : ℝ, 0 < δ ∧
      ¬ (∀ᶠ n in Filter.cofinite,
        opLength (X n) (((lift 1)⁻¹ * lift z) n) < δ) := by
    by_contra hcon
    apply hnot
    intro δ hδ
    by_contra hbad
    exact hcon ⟨δ, hδ, hbad⟩
  obtain ⟨δ, hδ, hfrequent⟩ := hex
  refine ⟨δ, hδ, ?_⟩
  show ¬ ∀ᶠ n in Filter.cofinite,
    ¬ δ ≤ ‖(lift z n : Matrix (X n) (X n) ℂ) - lift 1 n‖
  simpa only [Pi.mul_apply, Pi.inv_apply, not_le, opLength_inv_mul] using hfrequent

/-- A marked element surviving in a standard norm matrix corona yields a
sequential operator-norm almost representation with a uniform marked gap. -/
theorem exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one
    [Countable G] (rho : G →* NormMatrixCoronaUnitary X)
    {z : G} (hz : rho z ≠ 1) :
    Nonempty (MarkedOpAlmostRepresentation G z) := by
  classical
  choose lift hlift using fun g : G ↦ QuotientGroup.mk_surjective (rho g)
  have hmul :=
    normMatrixCorona_lift_eventually_multiplicative X rho lift hlift
  obtain ⟨δ, hδ, hsep⟩ :=
    normMatrixCorona_lift_frequently_marked_separated X rho lift hlift hz
  obtain ⟨e, he⟩ := exists_surjective_nat G
  let F : ℕ → Finset G := fun n ↦ insert 1 ((Finset.range (n + 1)).image e)
  have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
    intro m n hmn
    refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hFmem : ∀ g : G, ∃ N, ∀ n ≥ N, g ∈ F n := by
    intro g
    obtain ⟨k, rfl⟩ := he g
    exact ⟨k, fun n hn ↦ hFmono hn (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨k, Finset.self_mem_range_succ k, rfl⟩))⟩
  let η : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hη (n : ℕ) : 0 < η n := by dsimp [η]; positivity
  have hall : ∀ n : ℕ, ∃ i : ℕ,
      (∀ p ∈ F n ×ˢ F n,
        ‖(lift (p.1 * p.2) i : Matrix (X i) (X i) ℂ) -
          (lift p.1 i : Matrix (X i) (X i) ℂ) * lift p.2 i‖ ≤ η n) ∧
      δ ≤ ‖(lift z i : Matrix (X i) (X i) ℂ) - lift 1 i‖ := by
    intro n
    have hm : ∀ᶠ i in Filter.cofinite, ∀ p ∈ F n ×ˢ F n,
        ‖(lift (p.1 * p.2) i : Matrix (X i) (X i) ℂ) -
          (lift p.1 i : Matrix (X i) (X i) ℂ) * lift p.2 i‖ ≤ η n := by
      rw [eventually_all_finset]
      intro p _
      exact hmul p.1 p.2 (η n) (hη n)
    obtain ⟨i, hsi, hmi⟩ := (hsep.and_eventually hm).exists
    exact ⟨i, hmi, hsi⟩
  let stage : ℕ → ℕ := fun n ↦ Classical.choose (hall n)
  have hstage (n : ℕ) :
      (∀ p ∈ F n ×ˢ F n,
        ‖(lift (p.1 * p.2) (stage n) : Matrix (X (stage n)) (X (stage n)) ℂ) -
          (lift p.1 (stage n) : Matrix (X (stage n)) (X (stage n)) ℂ) *
            lift p.2 (stage n)‖ ≤ η n) ∧
      δ ≤ ‖(lift z (stage n) : Matrix (X (stage n)) (X (stage n)) ℂ) -
        lift 1 (stage n)‖ := Classical.choose_spec (hall n)
  have hmodelPos (n : ℕ) : 0 < Fintype.card (X (stage n)) := by
    rw [Fintype.card_pos_iff]
    by_contra hempty
    haveI : IsEmpty (X (stage n)) := not_nonempty_iff.mp hempty
    have heq : (lift z (stage n) : Matrix (X (stage n)) (X (stage n)) ℂ) =
        lift 1 (stage n) := by
      ext i
      exact isEmptyElim i
    have := (hstage n).2
    rw [heq, sub_self, norm_zero] at this
    exact (not_lt_of_ge this) hδ
  refine ⟨{
    separation := δ
    separation_pos := hδ
    model := fun n ↦ X (stage n)
    modelNonempty := hmodelPos
    map := fun n g ↦ lift g (stage n)
    asymptoticallyMultiplicative := ?_
    marked_separated := fun n ↦ (hstage n).2 }⟩
  intro g h ε hε
  obtain ⟨Ng, hNg⟩ := hFmem g
  obtain ⟨Nh, hNh⟩ := hFmem h
  obtain ⟨Ne, hNe⟩ := exists_nat_gt (1 / ε)
  refine ⟨max (max Ng Nh) Ne, fun n hn ↦ ?_⟩
  have hg : g ∈ F n := hNg n ((le_max_left _ _).trans
    ((le_max_left _ _).trans hn))
  have hh : h ∈ F n := hNh n ((le_max_right _ _).trans
    ((le_max_left _ _).trans hn))
  have hsmall : η n ≤ ε := by
    dsimp [η]
    have hNen : (Ne : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (le_max_right (max Ng Nh) Ne).trans hn
    have hlt : (1 : ℝ) / ε < (n : ℝ) + 1 := by linarith
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hlt
    linarith
  exact ((hstage n).1 (g, h) (Finset.mem_product.mpr ⟨hg, hh⟩)).trans hsmall

/-- A sequential marked-model obstruction excludes the standard cofinite
operator-norm MF property. -/
theorem not_isOperatorMF_of_no_markedOpAlmostRepresentation
    [Countable G] {z : G}
    (hkill : MarkedOpAlmostRepresentation G z → False) (hz : z ≠ 1) :
    ¬ IsOperatorMF G := by
  rintro ⟨X, _hX, rho, hrho⟩
  have hρz : rho z ≠ 1 := by
    intro h
    apply hz
    apply hrho
    simpa using h
  obtain ⟨A⟩ :=
    exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one X rho hρz
  exact hkill A

end GroupApproximation
