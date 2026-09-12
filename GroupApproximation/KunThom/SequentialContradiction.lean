import GroupApproximation.KunThom.NormalizationFromCriterion
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.WellFounded

/-!
# Sequential statements by contradiction: subsequences and slow diagonals

Kun--Thom argue in the ultraproduct `𝒮_𝒰`, where almost commutation is exact
commutation.  The sequential form `SeqNormalizes Γ t` asks instead that a
normalized Hamming defect vanish along `Filter.atTop`.  This module supplies the
glue between the two readings.

*Extraction.*  A property holding at arbitrarily large indices holds along a
strictly increasing subsequence (`exists_strictMono_of_frequently`), and one
witness per such index can be chosen along it (`exists_strictMono_choice`).  A
nonvanishing sequence stays at least some `ε > 0` away from zero along a
strictly increasing subsequence (`exists_strictMono_le_abs_of_not_vanishing`).
Conversely a sequence vanishes once no subsequence is bounded below
(`vanishing_of_forall_strictMono`), or once every subsequence has a further
subsequence along which it vanishes (`vanishing_of_forall_strictMono_exists`).

*Diagonals.*  Finitely many vanishing sequences are eventually uniformly small
(`eventually_forall_finset_abs_lt`).  For countably many eventual properties,
`exists_diagonal_of_eventually` chooses `j n → ∞` below any prescribed
`f n → ∞` such that the first `j n` properties all hold at index `n`.
`exists_diagonal_vanishing` is the same choice for vanishing sequences, with a
uniform `ε`-bound on the first `j n` of them.

*Sofic approximations.*  `SoficApproximation.reindex` along a strictly
increasing map is again a sofic approximation, so freeness and approximate
multiplicativity pass to the subsequence by construction.  Almost commutation
passes by `SoficApproximation.almostCommutes_reindex`.  Hence:

* `seqNormalizes_of_forall_not_uniform_lower_bound`: `SeqNormalizes Γ g` holds
  as soon as no sofic approximation `A` carries an almost-centralizer `v` of
  `Γ` whose conjugate by `A(g)` keeps its commutator with some `A(γ)`, `γ ∈ Γ`,
  at least `ε > 0` at every index.  The finite argument may therefore assume a
  uniform lower bound at every index.  It may also pass to further
  subsequences, since the hypothesis quantifies over all sofic approximations.
* `seqNormalizes_of_exists_strictMono_vanishing`: it suffices that the defect
  vanishes along some strictly increasing subsequence.
* `seqNormalizes_of_eventually_uniform`: the eventually-bounds form, argued
  directly.  For each `γ ∈ Γ` and `ε > 0` there are a tolerance `δ > 0`, a
  finite `F ⊆ Γ` and a threshold `N`.  Every permutation `w` of the `n`-th
  model, `n ≥ N`, that `δ`-commutes with `A(F)` has a conjugate by `A(g)` that
  `ε`-commutes with `A(γ)`.
-/

namespace GroupApproximation

namespace SequentialContradiction

/-! ## Extraction of subsequences -/

/-- A strictly increasing self-map of `ℕ` dominates the identity, in the
pointwise form consumed by `SoficApproximation.reindex`. -/
theorem le_apply_of_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) (n : ℕ) : n ≤ φ n :=
  hφ.id_le n

/-- A property holding at arbitrarily large indices holds along a strictly
increasing subsequence. -/
theorem exists_strictMono_of_frequently {P : ℕ → Prop}
    (h : ∀ N : ℕ, ∃ n ≥ N, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, P (φ k) := by
  refine Nat.exists_strictMono_subsequence (P := P) fun N ↦ ?_
  obtain ⟨n, hn, hP⟩ := h (N + 1)
  exact ⟨n, by omega, hP⟩

/-- One witness per index, along a strictly increasing subsequence of the
indices at which a witness exists. -/
theorem exists_strictMono_choice {X : ℕ → Type*} {Q : ∀ n, X n → Prop}
    (h : ∀ N : ℕ, ∃ n ≥ N, ∃ x : X n, Q n x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ∀ k, X (φ k), ∀ k, Q (φ k) (x k) := by
  obtain ⟨φ, hφ, hex⟩ :=
    exists_strictMono_of_frequently (P := fun n ↦ ∃ x : X n, Q n x) h
  have hex' : ∀ k, ∃ x : X (φ k), Q (φ k) x := hex
  choose x hx using hex'
  exact ⟨φ, hφ, x, hx⟩

/-- Failure of eventual truth gives a strictly increasing subsequence of
counterexamples. -/
theorem exists_strictMono_of_not_eventually {P : ℕ → Prop}
    (h : ¬ ∃ N : ℕ, ∀ n ≥ N, P n) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ¬ P (φ k) := by
  refine exists_strictMono_of_frequently (P := fun n ↦ ¬ P n) fun N ↦ ?_
  by_contra hN
  apply h
  refine ⟨N, fun n hn ↦ ?_⟩
  by_contra hP
  exact hN ⟨n, hn, hP⟩

/-- **Eventual truth by contradiction.**  To prove that `P` holds eventually it
suffices to refute every strictly increasing subsequence of counterexamples. -/
theorem eventually_of_forall_strictMono {P : ℕ → Prop}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → (∀ k, ¬ P (φ k)) → False) :
    ∃ N : ℕ, ∀ n ≥ N, P n := by
  by_contra hP
  obtain ⟨φ, hφ, hbad⟩ := exists_strictMono_of_not_eventually hP
  exact h φ hφ hbad

/-- A nonvanishing sequence stays at least some `ε > 0` away from zero along a
strictly increasing subsequence. -/
theorem exists_strictMono_le_abs_of_not_vanishing {a : ℕ → ℝ} (h : ¬ Vanishing a) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, ε ≤ |a (φ k)| := by
  by_contra hno
  apply h
  intro ε hε
  by_contra hev
  obtain ⟨φ, hφ, hbad⟩ :=
    exists_strictMono_of_not_eventually (P := fun n ↦ |a n| < ε) hev
  exact hno ⟨ε, hε, φ, hφ, fun k ↦ not_lt.mp (hbad k)⟩

/-- **Vanishing by contradiction.**  A sequence vanishes as soon as no strictly
increasing subsequence stays at least a fixed `ε > 0` away from zero. -/
theorem vanishing_of_forall_strictMono {a : ℕ → ℝ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ ε : ℝ, 0 < ε →
      (∀ k, ε ≤ |a (φ k)|) → False) :
    Vanishing a := by
  by_contra hno
  obtain ⟨ε, hε, φ, hφ, hbound⟩ := exists_strictMono_le_abs_of_not_vanishing hno
  exact h φ hφ ε hε hbound

/-- A vanishing sequence vanishes along every strictly increasing
subsequence. -/
theorem vanishing_comp_strictMono {a : ℕ → ℝ} (ha : Vanishing a) {φ : ℕ → ℕ}
    (hφ : StrictMono φ) : Vanishing fun k ↦ a (φ k) :=
  ha.reindex φ (le_apply_of_strictMono hφ)

/-- **Subsequence principle.**  If every strictly increasing subsequence has a
further strictly increasing subsequence along which `a` vanishes, then `a`
vanishes. -/
theorem vanishing_of_forall_strictMono_exists {a : ℕ → ℝ}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Vanishing fun k ↦ a (φ (ψ k))) :
    Vanishing a := by
  refine vanishing_of_forall_strictMono fun φ hφ ε hε hbound ↦ ?_
  obtain ⟨ψ, _, hψ⟩ := h φ hφ
  obtain ⟨N, hN⟩ := hψ ε hε
  have h₁ : ε ≤ |a (φ (ψ N))| := hbound (ψ N)
  have h₂ : |a (φ (ψ N))| < ε := hN N le_rfl
  linarith

/-! ## Uniformity over finite sets and slow diagonals -/

/-- Finitely many vanishing sequences are eventually uniformly small. -/
theorem eventually_forall_finset_abs_lt {ι : Type*} (s : Finset ι) (a : ι → ℕ → ℝ)
    (ha : ∀ i ∈ s, Vanishing (a i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ s, |a i n| < ε :=
  eventually_finset s (fun i n ↦ |a i n| < ε) fun i hi ↦ ha i hi ε hε

/-- **Slow diagonal.**  Let each `P i` hold eventually, and let `f` tend to
infinity.  Some `j ≤ f` tends to infinity with `P i n` for every `i < j n`, at
every index `n`. -/
theorem exists_diagonal_of_eventually (P : ℕ → ℕ → Prop)
    (hP : ∀ i : ℕ, ∃ N : ℕ, ∀ n ≥ N, P i n) (f : ℕ → ℕ)
    (hf : ∀ K : ℕ, ∃ N : ℕ, ∀ n ≥ N, K ≤ f n) :
    ∃ j : ℕ → ℕ, (∀ n, j n ≤ f n) ∧ (∀ K : ℕ, ∃ N : ℕ, ∀ n ≥ N, K ≤ j n) ∧
      ∀ n, ∀ i < j n, P i n := by
  classical
  choose M hM using hP
  refine ⟨fun n ↦ Nat.findGreatest (fun k ↦ ∀ i < k, M i ≤ n) (f n),
    fun n ↦ Nat.findGreatest_le (f n), fun K ↦ ?_, fun n i hi ↦ ?_⟩
  · obtain ⟨N, hN⟩ := hf K
    refine ⟨max N (∑ i ∈ Finset.range K, M i), fun n hn ↦ ?_⟩
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hnM : ∑ i ∈ Finset.range K, M i ≤ n := (le_max_right _ _).trans hn
    refine Nat.le_findGreatest (P := fun k ↦ ∀ i < k, M i ≤ n) (hN n hnN) fun i hi ↦ ?_
    exact (Finset.single_le_sum (f := M) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr hi)).trans hnM
  · have hspec : ∀ i < Nat.findGreatest (fun k ↦ ∀ i < k, M i ≤ n) (f n), M i ≤ n :=
      Nat.findGreatest_spec (P := fun k ↦ ∀ i < k, M i ≤ n) (Nat.zero_le (f n))
        fun i hi ↦ absurd hi (Nat.not_lt_zero i)
    exact hM i n (hspec i hi)

/-- **Slow diagonal for vanishing sequences.**  For countably many vanishing
sequences `a i` and any `f` tending to infinity, some `j ≤ f` tends to infinity
with the first `j n` sequences uniformly small at index `n`: for every `ε > 0`,
eventually `|a i n| < ε` for all `i < j n`. -/
theorem exists_diagonal_vanishing (a : ℕ → ℕ → ℝ) (ha : ∀ i, Vanishing (a i))
    (f : ℕ → ℕ) (hf : ∀ K : ℕ, ∃ N : ℕ, ∀ n ≥ N, K ≤ f n) :
    ∃ j : ℕ → ℕ, (∀ n, j n ≤ f n) ∧ (∀ K : ℕ, ∃ N : ℕ, ∀ n ≥ N, K ≤ j n) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ i < j n, |a i n| < ε := by
  have hev : ∀ i : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ i' ≤ i, |a i' n| < 1 / ((i : ℝ) + 1) := by
    intro i
    have hpos : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
    obtain ⟨N, hN⟩ := eventually_forall_finset_abs_lt (Finset.range (i + 1)) a
      (fun i' _ ↦ ha i') hpos
    exact ⟨N, fun n hn i' hi' ↦ hN n hn i' (Finset.mem_range.mpr (by omega))⟩
  obtain ⟨j, hjf, hjinf, hjP⟩ := exists_diagonal_of_eventually
    (fun i n ↦ ∀ i' ≤ i, |a i' n| < 1 / ((i : ℝ) + 1)) hev f hf
  refine ⟨j, hjf, hjinf, fun ε hε ↦ ?_⟩
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hjinf (K + 1)
  refine ⟨N, fun n hn i hi ↦ ?_⟩
  have hKj : K < j n := by
    have hKn := hN n hn
    omega
  rcases le_total i K with hiK | hKi
  · have h₁ : |a i n| < 1 / ((K : ℝ) + 1) := hjP n K hKj i hiK
    linarith
  · have h₁ : |a i n| < 1 / ((i : ℝ) + 1) := hjP n i hi i le_rfl
    have hKi' : (K : ℝ) ≤ i := by exact_mod_cast hKi
    have h₂ : 1 / ((i : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith

end SequentialContradiction

namespace SoficApproximation

/-- Almost commutation passes to a reindexed approximation, for the reindexed
sequence. -/
theorem almostCommutes_reindex {G : Type} [Group G] (A : SoficApproximation G)
    (φ : ℕ → ℕ) (hφ : ∀ n, n ≤ φ n) {v : ∀ n, Equiv.Perm (A.model n)} {g : G}
    (hv : A.AlmostCommutes v g) :
    (A.reindex φ hφ).AlmostCommutes (fun k ↦ v (φ k)) g :=
  Vanishing.reindex hv φ hφ

/-- The conjugated sequence of a reindexed approximation is the reindexed
conjugated sequence. -/
theorem conjSeq_reindex {G : Type} [Group G] (A : SoficApproximation G) (φ : ℕ → ℕ)
    (hφ : ∀ n, n ≤ φ n) (g : G) (v : ∀ n, Equiv.Perm (A.model n)) (k : ℕ) :
    (A.reindex φ hφ).conjSeq g (fun k ↦ v (φ k)) k = A.conjSeq g v (φ k) :=
  rfl

/-- A sequence almost commuting with every element of a finite set is
eventually uniformly `δ`-commuting with all of them. -/
theorem almostCommutes_eventually_finset {G : Type} [Group G] (A : SoficApproximation G)
    {v : ∀ n, Equiv.Perm (A.model n)} (F : Finset G)
    (hF : ∀ x ∈ F, A.AlmostCommutes v x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ F,
      hammingDistance (A.model n) (v n * A.map n x) (A.map n x * v n) < δ := by
  obtain ⟨N, hN⟩ := SequentialContradiction.eventually_forall_finset_abs_lt F
    (fun x n ↦ hammingDistance (A.model n) (v n * A.map n x) (A.map n x * v n)) hF hδ
  exact ⟨N, fun n hn x hx ↦ lt_of_abs_lt (hN n hn x hx)⟩

end SoficApproximation

/-- **Sequential normalization by contradiction.**  `g` normalizes the
sequential almost-centralizer of `Γ` as soon as no sofic approximation `A` of
`G` carries an almost-centralizer `v` of `Γ` whose conjugate `A(g) v A(g)⁻¹`
keeps its commutator with some `A(γ)`, `γ ∈ Γ`, at least a fixed `ε > 0` at
every index.

A nonvanishing defect stays above some `ε` along a strictly increasing
subsequence `φ`; the hypothesis is then applied to `A.reindex φ` and `v ∘ φ`. -/
theorem seqNormalizes_of_forall_not_uniform_lower_bound {G : Type} [Group G]
    {Γ : Subgroup G} {g : G}
    (h : ∀ (A : SoficApproximation G) (v : ∀ n, Equiv.Perm (A.model n)),
      (∀ γ ∈ Γ, A.AlmostCommutes v γ) → ∀ γ ∈ Γ, ∀ ε : ℝ, 0 < ε →
        (∀ n, ε ≤ hammingDistance (A.model n) (A.conjSeq g v n * A.map n γ)
          (A.map n γ * A.conjSeq g v n)) → False) :
    SeqNormalizes Γ g := by
  intro A v hv γ hγ
  by_contra hno
  obtain ⟨ε, hε, φ, hφ, hbound⟩ :=
    SequentialContradiction.exists_strictMono_le_abs_of_not_vanishing hno
  have hφle := SequentialContradiction.le_apply_of_strictMono hφ
  refine h (A.reindex φ hφle) (fun k ↦ v (φ k))
    (fun γ' hγ' ↦ A.almostCommutes_reindex φ hφle (hv γ' hγ')) γ hγ ε hε fun k ↦ ?_
  have hk : ε ≤ |hammingDistance (A.model (φ k)) (A.conjSeq g v (φ k) * A.map (φ k) γ)
      (A.map (φ k) γ * A.conjSeq g v (φ k))| := hbound k
  rw [abs_of_nonneg (hammingDistance_nonnegative _ _ _)] at hk
  exact hk

/-- **Sequential normalization from subsequences.**  It suffices that, for every
sofic approximation and almost-centralizer `v` of `Γ`, the commutator defect of
`A(g) v A(g)⁻¹` with `A(γ)` vanishes along some strictly increasing
subsequence. -/
theorem seqNormalizes_of_exists_strictMono_vanishing {G : Type} [Group G]
    {Γ : Subgroup G} {g : G}
    (h : ∀ (A : SoficApproximation G) (v : ∀ n, Equiv.Perm (A.model n)),
      (∀ γ ∈ Γ, A.AlmostCommutes v γ) → ∀ γ ∈ Γ,
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Vanishing fun k ↦
          hammingDistance (A.model (ψ k)) (A.conjSeq g v (ψ k) * A.map (ψ k) γ)
            (A.map (ψ k) γ * A.conjSeq g v (ψ k))) :
    SeqNormalizes Γ g := by
  refine seqNormalizes_of_forall_not_uniform_lower_bound fun A v hv γ hγ ε hε hbound ↦ ?_
  obtain ⟨ψ, _, hψ⟩ := h A v hv γ hγ
  obtain ⟨N, hN⟩ := hψ ε hε
  have h₁ : ε ≤ hammingDistance (A.model (ψ N)) (A.conjSeq g v (ψ N) * A.map (ψ N) γ)
      (A.map (ψ N) γ * A.conjSeq g v (ψ N)) := hbound (ψ N)
  have h₂ : hammingDistance (A.model (ψ N)) (A.conjSeq g v (ψ N) * A.map (ψ N) γ)
      (A.map (ψ N) γ * A.conjSeq g v (ψ N)) < ε := lt_of_abs_lt (hN N le_rfl)
  linarith

/-- **Sequential normalization from uniform finite estimates.**  Suppose that
for every sofic approximation `A`, every `γ ∈ Γ` and every `ε > 0` there are a
tolerance `δ > 0`, a finite set `F ⊆ Γ` and a threshold `N`.  Every permutation
`w` of the `n`-th model, `n ≥ N`, that `δ`-commutes with `A(x)` for all `x ∈ F`
has a conjugate `A(g) w A(g)⁻¹` that `ε`-commutes with `A(γ)`.  Then `g`
normalizes. -/
theorem seqNormalizes_of_eventually_uniform {G : Type} [Group G]
    {Γ : Subgroup G} {g : G}
    (h : ∀ (A : SoficApproximation G), ∀ γ ∈ Γ, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∃ F : Finset G, (∀ x ∈ F, x ∈ Γ) ∧ ∃ N : ℕ, ∀ n ≥ N,
        ∀ w : Equiv.Perm (A.model n),
          (∀ x ∈ F, hammingDistance (A.model n) (w * A.map n x) (A.map n x * w) < δ) →
            hammingDistance (A.model n) (A.map n g * w * (A.map n g)⁻¹ * A.map n γ)
              (A.map n γ * (A.map n g * w * (A.map n g)⁻¹)) < ε) :
    SeqNormalizes Γ g := by
  intro A v hv γ hγ
  unfold SoficApproximation.AlmostCommutes
  refine SequentialNormalization.vanishing_of_eventually_lt
    (fun _ ↦ hammingDistance_nonnegative _ _ _) fun ε hε ↦ ?_
  obtain ⟨δ, hδ, F, hF, N₀, hN₀⟩ := h A γ hγ ε hε
  obtain ⟨N₁, hN₁⟩ := A.almostCommutes_eventually_finset F (fun x hx ↦ hv x (hF x hx)) hδ
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  exact hN₀ n ((le_max_left _ _).trans hn) (v n)
    (hN₁ n ((le_max_right _ _).trans hn))

end GroupApproximation
