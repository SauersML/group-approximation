import GroupApproximation.Sofic.NormTraceGap
import GroupApproximation.Sofic.NormMFUniversalQuotient
import GroupApproximation.Sofic.OperatorMF

/-!
# The norm-MF universal quotient is MF

For a countable group, pointwise detection of every nonidentity element by
possibly different norm-matrix ultraproducts can be diagonalized into one
faithful representation in a cofinite norm matrix corona.  At stage `k` we
take a block sum of detectors for the first `k + 1` nonidentity elements and
choose each detector far enough out to control the first `k + 1` group
elements.  Operator norm turns block sum into a finite maximum, so the
resulting sequence is asymptotically multiplicative, while every marked
element retains its own positive gap on all sufficiently late stages.

Applied to `normMFQuotient G`, whose residual is already known to be trivial,
this proves the three assertions in manuscript Proposition `prop:univquot`:
the residual is the kernel of a single corona representation, the quotient
is MF, and every map to an MF group factors uniquely through it.
-/

namespace GroupApproximation

open Filter Matrix
open scoped Matrix.Norms.L2Operator

universe u v

variable {G : Type u} [Group G]

/-! ## Finite operator-norm block diagonals -/

/-- The finite model underlying a binary block sum. -/
abbrev blockSumModel (Y Z : FiniteModel) : FiniteModel :=
  ⟨Y ⊕ Z, inferInstance, inferInstance⟩

/-- A binary block-diagonal matrix. -/
def blockDiagMatrix (Y Z : FiniteModel)
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    Matrix (blockSumModel Y Z) (blockSumModel Y Z) ℂ :=
  Matrix.fromBlocks A 0 0 B

theorem blockDiagMatrix_mul (Y Z : FiniteModel)
    (A C : Matrix Y Y ℂ) (B D : Matrix Z Z ℂ) :
    blockDiagMatrix Y Z A B * blockDiagMatrix Y Z C D =
      blockDiagMatrix Y Z (A * C) (B * D) := by
  unfold blockDiagMatrix
  rw [Matrix.fromBlocks_multiply]
  congr 1 <;> simp

theorem blockDiagMatrix_one (Y Z : FiniteModel) :
    blockDiagMatrix Y Z (1 : Matrix Y Y ℂ) (1 : Matrix Z Z ℂ) = 1 := by
  exact Matrix.fromBlocks_one

theorem blockDiagMatrix_conjTranspose (Y Z : FiniteModel)
    (A : Matrix Y Y ℂ) (B : Matrix Z Z ℂ) :
    (blockDiagMatrix Y Z A B)ᴴ = blockDiagMatrix Y Z Aᴴ Bᴴ := by
  unfold blockDiagMatrix
  rw [Matrix.fromBlocks_conjTranspose]
  congr 1 <;> simp

theorem blockDiagMatrix_sub (Y Z : FiniteModel)
    (A C : Matrix Y Y ℂ) (B D : Matrix Z Z ℂ) :
    blockDiagMatrix Y Z A B - blockDiagMatrix Y Z C D =
      blockDiagMatrix Y Z (A - C) (B - D) := by
  ext p q
  cases p <;> cases q <;>
    simp [blockDiagMatrix, Matrix.fromBlocks, Matrix.sub_apply]

theorem blockDiagMatrix_mem_unitaryGroup (Y Z : FiniteModel)
    {A : Matrix Y Y ℂ} {B : Matrix Z Z ℂ}
    (hA : A ∈ Matrix.unitaryGroup Y ℂ)
    (hB : B ∈ Matrix.unitaryGroup Z ℂ) :
    blockDiagMatrix Y Z A B ∈
      Matrix.unitaryGroup (blockSumModel Y Z) ℂ := by
  have hAA : A * Aᴴ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hA
    exact hA
  have hBB : B * Bᴴ = 1 := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] at hB
    exact hB
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    blockDiagMatrix_conjTranspose, blockDiagMatrix_mul, hAA, hBB,
    blockDiagMatrix_one]

/-- The operator norm of a binary block diagonal is the maximum of the two
block norms. -/
theorem l2_opNorm_blockDiag (Y Z : FiniteModel)
    (C : Matrix Y Y ℂ) (D : Matrix Z Z ℂ) :
    ‖blockDiagMatrix Y Z C D‖ = max ‖C‖ ‖D‖ := by
  classical
  set F : Matrix (blockSumModel Y Z) (blockSumModel Y Z) ℂ :=
    blockDiagMatrix Y Z C D with hF
  have hmv : ∀ x : (Y ⊕ Z) → ℂ,
      F *ᵥ x = Sum.elim (C *ᵥ (x ∘ Sum.inl))
        (D *ᵥ (x ∘ Sum.inr)) := by
    intro x
    rw [hF]
    unfold blockDiagMatrix
    rw [Matrix.fromBlocks_mulVec]
    congr 1 <;> simp
  apply le_antisymm
  · refine l2_opNorm_le_of_sum_normSq (blockSumModel Y Z) F
      ((norm_nonneg C).trans (le_max_left _ _)) fun x ↦ ?_
    have hsplit :
        ∑ p : Y ⊕ Z, Complex.normSq ((F *ᵥ x) p) =
          (∑ i : Y, Complex.normSq ((C *ᵥ (x ∘ Sum.inl)) i)) +
          ∑ j : Z, Complex.normSq ((D *ᵥ (x ∘ Sum.inr)) j) := by
      rw [Fintype.sum_sum_type]
      congr 1
      · exact Finset.sum_congr rfl fun i _ ↦ by rw [hmv]; rfl
      · exact Finset.sum_congr rfl fun j _ ↦ by rw [hmv]; rfl
    rw [hsplit]
    have hC := sum_normSq_mulVec_le Y C (x ∘ Sum.inl)
    have hD := sum_normSq_mulVec_le Z D (x ∘ Sum.inr)
    have hCmax : ‖C‖ ^ 2 ≤ max ‖C‖ ‖D‖ ^ 2 := by
      nlinarith [norm_nonneg C, norm_nonneg D, le_max_left ‖C‖ ‖D‖]
    have hDmax : ‖D‖ ^ 2 ≤ max ‖C‖ ‖D‖ ^ 2 := by
      nlinarith [norm_nonneg C, norm_nonneg D, le_max_right ‖C‖ ‖D‖]
    have hxC : 0 ≤ ∑ i : Y, Complex.normSq ((x ∘ Sum.inl) i) :=
      Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _
    have hxD : 0 ≤ ∑ j : Z, Complex.normSq ((x ∘ Sum.inr) j) :=
      Finset.sum_nonneg fun j _ ↦ Complex.normSq_nonneg _
    calc
      (∑ i : Y, Complex.normSq ((C *ᵥ (x ∘ Sum.inl)) i)) +
          ∑ j : Z, Complex.normSq ((D *ᵥ (x ∘ Sum.inr)) j)
          ≤ ‖C‖ ^ 2 * (∑ i : Y, Complex.normSq ((x ∘ Sum.inl) i)) +
            ‖D‖ ^ 2 * (∑ j : Z, Complex.normSq ((x ∘ Sum.inr) j)) :=
        add_le_add hC hD
      _ ≤ max ‖C‖ ‖D‖ ^ 2 *
          ((∑ i : Y, Complex.normSq ((x ∘ Sum.inl) i)) +
            ∑ j : Z, Complex.normSq ((x ∘ Sum.inr) j)) := by
        nlinarith
      _ = max ‖C‖ ‖D‖ ^ 2 *
          ∑ p : Y ⊕ Z, Complex.normSq (x p) := by
        congr 1
        rw [Fintype.sum_sum_type]
        rfl
  · apply max_le
    · refine l2_opNorm_le_of_sum_normSq Y C (norm_nonneg F) fun x ↦ ?_
      set xhat : (Y ⊕ Z) → ℂ := Sum.elim x 0 with hxhat
      have hcomp : xhat ∘ Sum.inl = x := rfl
      have hval : ∀ i : Y,
          (C *ᵥ x) i = (F *ᵥ xhat) (Sum.inl i) := by
        intro i
        rw [hmv, hcomp]
        rfl
      have hxsum : ∑ p : Y ⊕ Z, Complex.normSq (xhat p) =
          ∑ i : Y, Complex.normSq (x i) := by
        rw [Fintype.sum_sum_type]
        simp [hxhat]
      calc
        ∑ i : Y, Complex.normSq ((C *ᵥ x) i) =
            ∑ i : Y, Complex.normSq ((F *ᵥ xhat) (Sum.inl i)) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [hval i]
        _ ≤ ∑ p : Y ⊕ Z, Complex.normSq ((F *ᵥ xhat) p) := by
          rw [Fintype.sum_sum_type]
          exact le_add_of_nonneg_right
            (Finset.sum_nonneg fun j _ ↦ Complex.normSq_nonneg _)
        _ ≤ ‖F‖ ^ 2 * ∑ p : Y ⊕ Z, Complex.normSq (xhat p) :=
          sum_normSq_mulVec_le (blockSumModel Y Z) F xhat
        _ = ‖F‖ ^ 2 * ∑ i : Y, Complex.normSq (x i) := by rw [hxsum]
    · refine l2_opNorm_le_of_sum_normSq Z D (norm_nonneg F) fun x ↦ ?_
      set xhat : (Y ⊕ Z) → ℂ := Sum.elim 0 x with hxhat
      have hcomp : xhat ∘ Sum.inr = x := rfl
      have hval : ∀ j : Z,
          (D *ᵥ x) j = (F *ᵥ xhat) (Sum.inr j) := by
        intro j
        rw [hmv, hcomp]
        rfl
      have hxsum : ∑ p : Y ⊕ Z, Complex.normSq (xhat p) =
          ∑ j : Z, Complex.normSq (x j) := by
        rw [Fintype.sum_sum_type]
        simp [hxhat]
      calc
        ∑ j : Z, Complex.normSq ((D *ᵥ x) j) =
            ∑ j : Z, Complex.normSq ((F *ᵥ xhat) (Sum.inr j)) :=
          Finset.sum_congr rfl fun j _ ↦ by rw [hval j]
        _ ≤ ∑ p : Y ⊕ Z, Complex.normSq ((F *ᵥ xhat) p) := by
          rw [Fintype.sum_sum_type]
          exact le_add_of_nonneg_left
            (Finset.sum_nonneg fun i _ ↦ Complex.normSq_nonneg _)
        _ ≤ ‖F‖ ^ 2 * ∑ p : Y ⊕ Z, Complex.normSq (xhat p) :=
          sum_normSq_mulVec_le (blockSumModel Y Z) F xhat
        _ = ‖F‖ ^ 2 * ∑ j : Z, Complex.normSq (x j) := by rw [hxsum]

/-! ## Finite heterogeneous lists of unitary blocks -/

/-- One finite-dimensional unitary-valued family.  No multiplicativity is
assumed; this is the coordinate object combined by the block-list API. -/
structure UnitaryBlock (G : Type*) where
  model : FiniteModel
  map : G → Matrix.unitaryGroup model ℂ

/-- The nested sum carrier of a heterogeneous block list. -/
@[reducible] def blockListCarrier {G : Type*} : List (UnitaryBlock G) → Type
  | [] => Fin 0
  | B :: Bs => B.model.carrier ⊕ blockListCarrier Bs

/-- Canonical finite instance on the nested sum carrier. -/
@[reducible] def blockListFintype {G : Type*} :
    (Bs : List (UnitaryBlock G)) → Fintype (blockListCarrier Bs)
  | [] => inferInstance
  | B :: Bs => by
      letI : Fintype B.model.carrier := B.model.fintype
      letI : Fintype (blockListCarrier Bs) := blockListFintype Bs
      exact inferInstance

/-- Canonical decidable equality on the nested sum carrier. -/
@[reducible] def blockListDecidableEq {G : Type*} :
    (Bs : List (UnitaryBlock G)) → DecidableEq (blockListCarrier Bs)
  | [] => inferInstance
  | B :: Bs => by
      letI : DecidableEq B.model.carrier := B.model.decidableEq
      letI : DecidableEq (blockListCarrier Bs) := blockListDecidableEq Bs
      exact inferInstance

@[reducible, instance] def blockListCarrierFintype {G : Type*}
    (Bs : List (UnitaryBlock G)) : Fintype (blockListCarrier Bs) :=
  blockListFintype Bs

@[reducible, instance] def blockListCarrierDecidableEq {G : Type*}
    (Bs : List (UnitaryBlock G)) : DecidableEq (blockListCarrier Bs) :=
  blockListDecidableEq Bs

/-- The finite model on the nested sum carrier.  The empty list uses no
spurious identity coordinate. -/
@[reducible] def blockListModel {G : Type*}
    (Bs : List (UnitaryBlock G)) : FiniteModel where
  carrier := blockListCarrier Bs
  fintype := blockListFintype Bs
  decidableEq := blockListDecidableEq Bs

@[simp] theorem card_blockListModel_cons {G : Type*}
    (B : UnitaryBlock G) (Bs : List (UnitaryBlock G)) :
    Fintype.card (blockListModel (B :: Bs)) =
      Fintype.card B.model + Fintype.card (blockListModel Bs) := by
  simp [blockListModel, blockListCarrier, blockListFintype]

/-- Any positive-dimensional member makes the whole block-list model
positive-dimensional. -/
theorem card_blockListModel_pos_of_mem {G : Type*}
    {B : UnitaryBlock G} {Bs : List (UnitaryBlock G)}
    (hB : B ∈ Bs) (hpos : 0 < Fintype.card B.model) :
    0 < Fintype.card (blockListModel Bs) := by
  induction Bs with
  | nil => simp at hB
  | cons C Cs ih =>
      rw [List.mem_cons] at hB
      rw [card_blockListModel_cons]
      rcases hB with rfl | hB
      · omega
      · have := ih hB
        omega

/-- The block diagonal associated to a finite list of unitary-valued
families. -/
def blockListMap {G : Type*} :
    (Bs : List (UnitaryBlock G)) → G →
      Matrix (blockListModel Bs) (blockListModel Bs) ℂ
  | [], _ => 1
  | B :: Bs, g =>
      blockDiagMatrix B.model (blockListModel Bs) (B.map g) (blockListMap Bs g)

theorem blockListMap_mem_unitaryGroup {G : Type*}
    (Bs : List (UnitaryBlock G)) (g : G) :
    blockListMap Bs g ∈ Matrix.unitaryGroup (blockListModel Bs) ℂ := by
  induction Bs with
  | nil =>
      rw [blockListMap]
      exact one_mem _
  | cons B Bs ih =>
      rw [blockListMap]
      exact blockDiagMatrix_mem_unitaryGroup B.model (blockListModel Bs)
        (B.map g).2 ih

/-- If every coordinate multiplication defect is at most `ε`, then so is the
defect of their block diagonal. -/
theorem norm_blockListMap_mul_sub_le (G : Type*) [Mul G]
    (Bs : List (UnitaryBlock G)) (g h : G) {ε : ℝ} (hε : 0 ≤ ε)
    (hdefect : ∀ B ∈ Bs,
      ‖(B.map (g * h) : Matrix B.model B.model ℂ) -
        (B.map g : Matrix B.model B.model ℂ) *
          (B.map h : Matrix B.model B.model ℂ)‖ ≤ ε) :
    ‖blockListMap Bs (g * h) - blockListMap Bs g * blockListMap Bs h‖ ≤ ε := by
  induction Bs with
  | nil => simpa [blockListMap] using hε
  | cons B Bs ih =>
      have hhead := hdefect B (by simp)
      have htail := ih (fun C hC ↦ hdefect C (by simp [hC]))
      change
        ‖blockDiagMatrix B.model (blockListModel Bs)
              (B.map (g * h)) (blockListMap Bs (g * h)) -
            blockDiagMatrix B.model (blockListModel Bs)
                (B.map g) (blockListMap Bs g) *
              blockDiagMatrix B.model (blockListModel Bs)
                (B.map h) (blockListMap Bs h)‖ ≤ ε
      rw [blockDiagMatrix_mul, blockDiagMatrix_sub, l2_opNorm_blockDiag]
      exact max_le hhead htail

/-- A block occurring in the list gives a lower bound for the operator norm
of the whole block diagonal difference. -/
theorem norm_blockListMap_sub_ge_of_mem {G : Type*}
    {B : UnitaryBlock G} {Bs : List (UnitaryBlock G)}
    (hB : B ∈ Bs) (g h : G) :
    ‖(B.map g : Matrix B.model B.model ℂ) - B.map h‖ ≤
      ‖blockListMap Bs g - blockListMap Bs h‖ := by
  induction Bs with
  | nil => simp at hB
  | cons C Cs ih =>
      rw [List.mem_cons] at hB
      change ‖(B.map g : Matrix B.model B.model ℂ) - B.map h‖ ≤
        ‖blockDiagMatrix C.model (blockListModel Cs) (C.map g) (blockListMap Cs g) -
          blockDiagMatrix C.model (blockListModel Cs) (C.map h) (blockListMap Cs h)‖
      rw [blockDiagMatrix_sub, l2_opNorm_blockDiag]
      rcases hB with rfl | hB
      · exact le_max_left _ _
      · exact (ih hB).trans (le_max_right _ _)

/-- Package the matrix of a block list as a unitary-group element. -/
def blockListUnitary {G : Type*} (Bs : List (UnitaryBlock G)) (g : G) :
    Matrix.unitaryGroup (blockListModel Bs) ℂ :=
  ⟨blockListMap Bs g, blockListMap_mem_unitaryGroup Bs g⟩

/-- Uniformize an eventual bound over a finite set. -/
private theorem eventually_forall_finset_bound {I : Type*}
    (S : Finset I) (f : I → ℕ → ℝ)
    (h : ∀ s ∈ S, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n ≥ N, f s n ≤ ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, ∀ s ∈ S, f s n ≤ ε := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    exact ⟨0, by simp⟩
  · intro i s _ ih h
    obtain ⟨N₁, h₁⟩ := h i (Finset.mem_insert_self i s) ε hε
    obtain ⟨N₂, h₂⟩ := ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)
    refine ⟨max N₁ N₂, fun n hn j hj ↦ ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact h₁ n ((le_max_left _ _).trans hn)
    · exact h₂ n ((le_max_right _ _).trans hn) j hj

/-- A countable group with trivial norm-MF residual embeds in one standard
cofinite norm matrix corona.  This is the simultaneous-diagonalization step
missing from pointwise residual detection. -/
theorem isOperatorMF_of_normMFResidual_eq_bot [Countable G]
    (hres : normMFResidual G = ⊥) : IsOperatorMF G := by
  classical
  by_cases htriv : ∀ g : G, g = 1
  · let X : ℕ → FiniteModel :=
      fun _ ↦ ⟨PUnit, inferInstance, inferInstance⟩
    refine ⟨X, fun n ↦ by simp [X], 1, ?_⟩
    intro g h _
    rw [htriv g, htriv h]
  · let Gne : Type u := {g : G // g ≠ 1}
    haveI : Nonempty Gne := by
      push Not at htriv
      obtain ⟨g, hg⟩ := htriv
      exact ⟨⟨g, hg⟩⟩
    obtain ⟨mark, hmark⟩ := exists_surjective_nat Gne
    have hdetect (i : ℕ) :
        ∃ (I : Type) (U : Ultrafilter I) (X : I → FiniteModel)
          (rho : G →* UniversalWeakMF U X), rho (mark i : G) ≠ 1 := by
      have hnot : (mark i : G) ∉ normMFResidual G := by
        rw [hres]
        simpa using (mark i).property
      rw [mem_normMFResidual_iff] at hnot
      unfold NormMFInvisible at hnot
      push Not at hnot
      exact hnot
    choose I U Y detector hdetector using hdetect
    let A : ∀ i : ℕ, MarkedOpAlmostRepresentation G (mark i : G) :=
      fun i ↦ Classical.choice
        (exists_markedOpAlmostRepresentation_of_ne_one
          (U i) (Y i) (detector i) (hdetector i))
    obtain ⟨enumerate, henumerate⟩ := exists_surjective_nat G
    let F : ℕ → Finset G :=
      fun k ↦ insert 1 ((Finset.range (k + 1)).image enumerate)
    have hFmono : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := by
      intro m n hmn
      refine Finset.insert_subset_insert _ (Finset.image_subset_image ?_)
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    have hFmem : ∀ g : G, ∃ N, ∀ n ≥ N, g ∈ F n := by
      intro g
      obtain ⟨k, rfl⟩ := henumerate g
      exact ⟨k, fun n hn ↦ hFmono hn (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨k, Finset.self_mem_range_succ k, rfl⟩))⟩
    let η : ℕ → ℝ := fun k ↦ 1 / ((k : ℝ) + 1)
    have hη (k : ℕ) : 0 < η k := by
      dsimp [η]
      positivity
    have hstageExists (i k : ℕ) : ∃ n : ℕ,
        ∀ p ∈ F k ×ˢ F k,
          ‖((A i).map n (p.1 * p.2) :
              Matrix ((A i).model n) ((A i).model n) ℂ) -
            ((A i).map n p.1 : Matrix ((A i).model n) ((A i).model n) ℂ) *
              (A i).map n p.2‖ ≤ η k := by
      obtain ⟨N, hN⟩ := eventually_forall_finset_bound (F k ×ˢ F k)
        (fun p n ↦
          ‖((A i).map n (p.1 * p.2) :
              Matrix ((A i).model n) ((A i).model n) ℂ) -
            ((A i).map n p.1 : Matrix ((A i).model n) ((A i).model n) ℂ) *
              (A i).map n p.2‖)
        (fun p _ ↦ (A i).asymptoticallyMultiplicative p.1 p.2)
        (hη k)
      exact ⟨N, hN N le_rfl⟩
    let stage : ℕ → ℕ → ℕ :=
      fun i k ↦ Classical.choose (hstageExists i k)
    have hstage (i k : ℕ) :
        ∀ p ∈ F k ×ˢ F k,
          ‖((A i).map (stage i k) (p.1 * p.2) :
              Matrix ((A i).model (stage i k)) ((A i).model (stage i k)) ℂ) -
            ((A i).map (stage i k) p.1 :
              Matrix ((A i).model (stage i k)) ((A i).model (stage i k)) ℂ) *
              (A i).map (stage i k) p.2‖ ≤ η k :=
      Classical.choose_spec (hstageExists i k)
    let B : ℕ → ℕ → UnitaryBlock G := fun i k ↦ {
      model := (A i).model (stage i k)
      map := fun g ↦ (A i).map (stage i k) g }
    let blocks : ℕ → List (UnitaryBlock G) :=
      fun k ↦ (List.range (k + 1)).map fun i ↦ B i k
    have hBmem {i k : ℕ} (hik : i ≤ k) : B i k ∈ blocks k := by
      apply List.mem_map.mpr
      exact ⟨i, by simp; omega, rfl⟩
    have hblockDefect (k : ℕ) {C : UnitaryBlock G}
        (hC : C ∈ blocks k) {g h : G} (hg : g ∈ F k) (hh : h ∈ F k) :
        ‖(C.map (g * h) : Matrix C.model C.model ℂ) -
          (C.map g : Matrix C.model C.model ℂ) * C.map h‖ ≤ η k := by
      rcases List.mem_map.mp hC with ⟨i, hi, rfl⟩
      exact hstage i k (g, h) (Finset.mem_product.mpr ⟨hg, hh⟩)
    let X : ℕ → FiniteModel := fun k ↦ blockListModel (blocks k)
    let φ : ∀ k, G → Matrix.unitaryGroup (X k) ℂ :=
      fun k g ↦ blockListUnitary (blocks k) g
    have hXpos (k : ℕ) : 0 < Fintype.card (X k) := by
      apply card_blockListModel_pos_of_mem (hBmem (i := 0) (Nat.zero_le k))
      change 0 < Fintype.card ((A 0).model (stage 0 k))
      exact (A 0).modelNonempty (stage 0 k)
    have hmul : ∀ g h : G, ∀ ε : ℝ, 0 < ε → ∃ N, ∀ k ≥ N,
        ‖(φ k (g * h) : Matrix (X k) (X k) ℂ) -
          (φ k g : Matrix (X k) (X k) ℂ) * φ k h‖ ≤ ε := by
      intro g h ε hε
      obtain ⟨Ng, hNg⟩ := hFmem g
      obtain ⟨Nh, hNh⟩ := hFmem h
      obtain ⟨Ne, hNe⟩ := exists_nat_gt (1 / ε)
      refine ⟨max (max Ng Nh) Ne, fun k hk ↦ ?_⟩
      have hg : g ∈ F k := hNg k ((le_max_left _ _).trans
        ((le_max_left _ _).trans hk))
      have hh : h ∈ F k := hNh k ((le_max_right _ _).trans
        ((le_max_left _ _).trans hk))
      have hsmall : η k ≤ ε := by
        dsimp [η]
        have hNek : (Ne : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast (le_max_right (max Ng Nh) Ne).trans hk
        have hlt : (1 : ℝ) / ε < (k : ℝ) + 1 := by linarith
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ hε] at hlt
        linarith
      change ‖blockListMap (blocks k) (g * h) -
        blockListMap (blocks k) g * blockListMap (blocks k) h‖ ≤ ε
      exact (norm_blockListMap_mul_sub_le G (blocks k) g h (hη k).le
        (fun C hC ↦ hblockDefect k hC hg hh)).trans hsmall
    have hnull : ∀ g h : G,
        (fun k ↦ φ k g * φ k h)⁻¹ * (fun k ↦ φ k (g * h)) ∈
          nullCofiniteOpSubgroup X := by
      intro g h ε hε
      obtain ⟨N, hN⟩ := hmul g h (ε / 2) (by linarith)
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_ge_atTop N] with k hk
      change opLength (X k) ((φ k g * φ k h)⁻¹ * φ k (g * h)) < ε
      rw [opLength_inv_mul]
      exact (hN k hk).trans_lt (by linarith)
    let rho : G →* NormMatrixCoronaUnitary X :=
      MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun k ↦ φ k g))
        (fun g h ↦ by
          rw [← QuotientGroup.mk_mul]
          exact (QuotientGroup.eq.mpr (hnull g h)).symm)
    refine ⟨X, hXpos, rho, ?_⟩
    intro g h hgh
    by_contra hne
    have hz : h⁻¹ * g ≠ 1 := by
      intro hz
      apply hne
      calc
        g = h * (h⁻¹ * g) := by group
        _ = h := by rw [hz, mul_one]
    obtain ⟨i, hi⟩ := hmark ⟨h⁻¹ * g, hz⟩
    have himark : (mark i : G) = h⁻¹ * g :=
      congrArg Subtype.val hi
    have hrho : rho (h⁻¹ * g) = rho 1 := by
      rw [map_mul, map_inv, hgh, inv_mul_cancel, map_one]
    have hmem : (fun k ↦ φ k 1)⁻¹ * (fun k ↦ φ k (h⁻¹ * g)) ∈
        nullCofiniteOpSubgroup X := by
      exact QuotientGroup.eq.mp hrho.symm
    have hclose := hmem (A i).separation (A i).separation_pos
    have hge : ∀ᶠ k in Filter.cofinite, i ≤ k := by
      rw [Nat.cofinite_eq_atTop]
      exact eventually_ge_atTop i
    obtain ⟨k, hik, hkclose⟩ := (hge.and hclose).exists
    have hblockFar : (A i).separation ≤
        ‖((B i k).map (h⁻¹ * g) : Matrix (B i k).model (B i k).model ℂ) -
          (B i k).map 1‖ := by
      simpa only [B, himark] using (A i).marked_separated (stage i k)
    have hfar : (A i).separation ≤
        ‖blockListMap (blocks k) (h⁻¹ * g) - blockListMap (blocks k) 1‖ :=
      hblockFar.trans
        (norm_blockListMap_sub_ge_of_mem (hBmem hik) (h⁻¹ * g) 1)
    change opLength (X k) ((φ k 1)⁻¹ * φ k (h⁻¹ * g)) <
      (A i).separation at hkclose
    rw [opLength_inv_mul] at hkclose
    exact (not_lt_of_ge hfar) hkclose

/-- A marked sequential almost representation produces an ultraproduct
homomorphism in which its mark survives. -/
theorem exists_ultraproduct_detector_of_markedOpAlmostRepresentation
    {z : G} (A : MarkedOpAlmostRepresentation G z) :
    ∃ rho : G →* UniversalWeakMF (Ultrafilter.of Filter.cofinite) A.model,
      rho z ≠ 1 := by
  have hcof :
      (((Ultrafilter.of Filter.cofinite : Ultrafilter ℕ) : Filter ℕ) ≤
        Filter.cofinite) := Ultrafilter.of_le _
  have hnull : ∀ g h : G,
      (fun n ↦ A.map n g * A.map n h)⁻¹ * (fun n ↦ A.map n (g * h)) ∈
        nullOpSubgroup (Ultrafilter.of Filter.cofinite) A.model := by
    intro g h ε hε
    obtain ⟨N, hN⟩ := A.asymptoticallyMultiplicative g h (ε / 2) (by linarith)
    refine eventually_of_atTop hcof N (fun n hn ↦ ?_)
    change opLength (A.model n)
      ((A.map n g * A.map n h)⁻¹ * A.map n (g * h)) < ε
    rw [opLength_inv_mul]
    exact (hN n hn).trans_lt (by linarith)
  let rho : G →* UniversalWeakMF
      (Ultrafilter.of Filter.cofinite) A.model :=
    MonoidHom.mk' (fun g ↦ QuotientGroup.mk (fun n ↦ A.map n g))
      (fun g h ↦ by
        rw [← QuotientGroup.mk_mul]
        exact (QuotientGroup.eq.mpr (hnull g h)).symm)
  refine ⟨rho, ?_⟩
  intro hz
  have heq : rho z = rho 1 := by simpa using hz
  have hmem : (fun n ↦ A.map n 1)⁻¹ * (fun n ↦ A.map n z) ∈
      nullOpSubgroup (Ultrafilter.of Filter.cofinite) A.model :=
    QuotientGroup.eq.mp heq.symm
  obtain ⟨n, hn⟩ := (hmem A.separation A.separation_pos).exists
  change opLength (A.model n) ((A.map n 1)⁻¹ * A.map n z) <
    A.separation at hn
  rw [opLength_inv_mul] at hn
  exact (not_lt_of_ge (A.marked_separated n)) hn

/-- A countable operator-MF group has trivial norm-MF residual.  Faithfulness
of one cofinite-corona representation is converted into an ultraproduct
detector for any hypothetical nontrivial residual element. -/
theorem normMFResidual_eq_bot_of_isOperatorMF [Countable G]
    (hMF : IsOperatorMF G) : normMFResidual G = ⊥ := by
  obtain ⟨X, _hX, rho, hrho⟩ := hMF
  apply Subgroup.eq_bot_iff_forall (normMFResidual G) |>.2
  intro g hg
  by_contra hne
  have hrhohne : rho g ≠ 1 := by
    intro heq
    exact hne (hrho (by simpa using heq))
  obtain ⟨A⟩ :=
    exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one
      X rho hrhohne
  obtain ⟨detector, hdetector⟩ :=
    exists_ultraproduct_detector_of_markedOpAlmostRepresentation A
  exact hdetector (map_eq_one_of_mem_normMFResidual
    (Ultrafilter.of Filter.cofinite) A.model detector hg)

/-- For countable groups, the standard operator-MF property is exactly
triviality of the universal norm-MF residual. -/
theorem isOperatorMF_iff_normMFResidual_eq_bot [Countable G] :
    IsOperatorMF G ↔ normMFResidual G = ⊥ :=
  ⟨normMFResidual_eq_bot_of_isOperatorMF,
    isOperatorMF_of_normMFResidual_eq_bot⟩

/-- The universal pointwise norm-matrix quotient of a countable group is an MF
group in the standard cofinite-corona sense. -/
theorem normMFQuotient_isOperatorMF [Countable G] :
    IsOperatorMF (normMFQuotient G) := by
  letI : Countable (normMFQuotient G) :=
    Function.Surjective.countable
      (QuotientGroup.mk'_surjective (normMFResidual G))
  exact isOperatorMF_of_normMFResidual_eq_bot
    normMFResidual_normMFQuotient_eq_bot

/-- The norm-MF residual is the kernel of one representation into one
standard norm matrix corona. -/
theorem exists_normMatrixCoronaRepresentation_ker_eq_normMFResidual
    [Countable G] :
    ∃ (X : ℕ → FiniteModel), (∀ n, 0 < Fintype.card (X n)) ∧
      ∃ rho : G →* NormMatrixCoronaUnitary X,
        rho.ker = normMFResidual G := by
  obtain ⟨X, hX, embed, hembed⟩ := normMFQuotient_isOperatorMF (G := G)
  refine ⟨X, hX, embed.comp (normMFQuotientMk G), ?_⟩
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro hg
    have : normMFQuotientMk G g = 1 := hembed (by simpa using hg)
    exact (QuotientGroup.eq_one_iff g).mp this
  · intro hg
    change embed (QuotientGroup.mk g) = 1
    rw [(QuotientGroup.eq_one_iff g).mpr hg, map_one]

/-- Every homomorphism from `G` to an operator-norm MF group factors uniquely
through the universal MF quotient. -/
theorem existsUnique_normMFQuotient_factorization_to_isOperatorMF
    [Countable G] {H : Type v} [Group H]
    (f : G →* H) (hH : IsOperatorMF H) :
    ∃! fBar : normMFQuotient G →* H,
      fBar.comp (normMFQuotientMk G) = f := by
  obtain ⟨X, _hX, rho, hrho⟩ := hH
  have hker : normMFResidual G ≤ f.ker := by
    intro g hg
    apply MonoidHom.mem_ker.mpr
    by_contra hfg
    have hcorona : (rho.comp f) g ≠ 1 := by
      intro heq
      exact hfg (hrho (by simpa using heq))
    obtain ⟨A⟩ :=
      exists_markedOpAlmostRepresentation_of_normMatrixCorona_ne_one
        X (rho.comp f) hcorona
    obtain ⟨detector, hdetector⟩ :=
      exists_ultraproduct_detector_of_markedOpAlmostRepresentation A
    exact hdetector (map_eq_one_of_mem_normMFResidual
      (Ultrafilter.of Filter.cofinite) A.model detector hg)
  refine ⟨QuotientGroup.lift (normMFResidual G) f hker,
    QuotientGroup.lift_comp_mk' (normMFResidual G) f hker, ?_⟩
  intro k hk
  exact normMFQuotient_hom_ext
    (hk.trans (QuotientGroup.lift_comp_mk'
      (normMFResidual G) f hker).symm)

end GroupApproximation
