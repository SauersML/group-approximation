import GroupApproximation.Sofic.AmplifiedBlockNorms
import GroupApproximation.Sofic.OperatorMF

/-!
# Section 49 for the MF radical: inducing a corona representation

A finite-index subgroup induces representations upward.  Section 49.1 does this
for norm matrix coronas; here the construction is carried out on the *lifts*,
where it is an entirely finite-dimensional matter, and the corona statement
follows because the multiplicative defect of the induced family is the maximum
of finitely many defects of the inducing one.

Everything runs on two total functions of a pair of group elements: the cocycle
`cocycle a b`, which is `a⁻¹b` whenever that lies in the subgroup, and the
coefficient `coeffOf π a b`, which is `π (cocycle a b)` on that same condition
and `0` otherwise.  The block-monomial pattern, unitarity, and the defect bound
are properties of these two functions, so no dependent case distinction enters a
matrix index.
-/

namespace GroupApproximation

namespace InducedCorona

open Matrix AmplifiedBlocks
open scoped Matrix.Norms.L2Operator

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

/-- Transversal data for a finite-index subgroup: representatives and the index
map, related by the defining membership condition. -/
structure Transversal (G : Type u) [Group G] (H : Subgroup G) (m : ℕ) where
  /-- The chosen representative of each coset. -/
  rep : Fin m → G
  /-- The index of the coset of a group element. -/
  idx : G → Fin m
  /-- Membership characterizes the index. -/
  spec : ∀ (i : Fin m) (b : G), idx b = i ↔ (rep i)⁻¹ * b ∈ H

namespace Transversal

variable {m : ℕ} (T : Transversal G H m)

theorem mem_idx (b : G) : (T.rep (T.idx b))⁻¹ * b ∈ H :=
  (T.spec (T.idx b) b).mp rfl

theorem idx_rep (i : Fin m) : T.idx (T.rep i) = i := by
  refine (T.spec i (T.rep i)).mpr ?_
  rw [inv_mul_cancel]
  exact H.one_mem

theorem idx_eq_of_mem {b : G} {i : Fin m} (h : (T.rep i)⁻¹ * b ∈ H) :
    T.idx b = i := (T.spec i b).mpr h

/-- Left translation permutes the coset indices. -/
theorem idx_mul_injective (g : G) :
    Function.Injective (fun j : Fin m => T.idx (g * T.rep j)) := by
  intro j₁ j₂ h
  simp only [] at h
  have h₁ := T.mem_idx (g * T.rep j₁)
  have h₂ := T.mem_idx (g * T.rep j₂)
  rw [show T.idx (g * T.rep j₁) = T.idx (g * T.rep j₂) from h] at h₁
  have hmul : (T.rep j₁)⁻¹ * T.rep j₂ ∈ H := by
    have hcalc : (T.rep j₁)⁻¹ * T.rep j₂
        = (g * T.rep j₁)⁻¹ * (T.rep (T.idx (g * T.rep j₂)))
          * ((T.rep (T.idx (g * T.rep j₂)))⁻¹ * (g * T.rep j₂)) := by
      group
    have h₁' : (g * T.rep j₁)⁻¹ * T.rep (T.idx (g * T.rep j₂)) ∈ H := by
      have hinv := H.inv_mem h₁
      simpa [_root_.mul_inv_rev] using hinv
    rw [hcalc]
    exact H.mul_mem h₁' h₂
  have := T.idx_eq_of_mem hmul
  rw [T.idx_rep] at this
  exact this.symm

/-- Left translation as a permutation of the coset indices. -/
noncomputable def perm (g : G) : Equiv.Perm (Fin m) :=
  Equiv.ofBijective (fun j => T.idx (g * T.rep j))
    ((Finite.injective_iff_bijective).mp (T.idx_mul_injective g))

@[simp] theorem perm_apply (g : G) (j : Fin m) :
    T.perm g j = T.idx (g * T.rep j) := rfl

theorem idx_eq_of_mem' {x y : G} (h : x⁻¹ * y ∈ H) : T.idx x = T.idx y := by
  refine (T.idx_eq_of_mem ?_).symm
  have hrw : (T.rep (T.idx x))⁻¹ * y
      = ((T.rep (T.idx x))⁻¹ * x) * (x⁻¹ * y) := by group
  rw [hrw]
  exact H.mul_mem (T.mem_idx x) h

/-- Coset indices compose: the index permutation is a homomorphism. -/
theorem perm_mul (g₁ g₂ : G) :
    T.perm (g₁ * g₂) = T.perm g₁ * T.perm g₂ := by
  refine Equiv.ext fun j => ?_
  show T.idx (g₁ * g₂ * T.rep j) = T.idx (g₁ * T.rep (T.idx (g₂ * T.rep j)))
  refine (T.idx_eq_of_mem' ?_).symm
  have hrw : (g₁ * T.rep (T.idx (g₂ * T.rep j)))⁻¹ * (g₁ * g₂ * T.rep j)
      = (T.rep (T.idx (g₂ * T.rep j)))⁻¹ * (g₂ * T.rep j) := by group
  rw [hrw]
  exact T.mem_idx _

end Transversal

/-! ## The coefficient calculus for an arbitrary unitary family -/

open scoped Classical in
/-- The cocycle of a pair of group elements, made total. -/
noncomputable def cocycle (H : Subgroup G) (a b : G) : H :=
  if h : a⁻¹ * b ∈ H then ⟨a⁻¹ * b, h⟩ else 1

theorem cocycle_val {a b : G} (h : a⁻¹ * b ∈ H) :
    ((cocycle H a b : H) : G) = a⁻¹ * b := by
  rw [cocycle, dif_pos h]

open scoped Classical in
/-- The matrix coefficient of a family indexed by the subgroup. -/
noncomputable def coeffOf {Y : FiniteModel} (π : H → Matrix Y Y ℂ) (a b : G) :
    Matrix Y Y ℂ :=
  if a⁻¹ * b ∈ H then π (cocycle H a b) else 0

variable {Y : FiniteModel} (π : H → Matrix Y Y ℂ)

theorem coeffOf_of_mem {a b : G} (h : a⁻¹ * b ∈ H) :
    coeffOf π a b = π (cocycle H a b) := by
  rw [coeffOf, if_pos h]

theorem coeffOf_of_not_mem {a b : G} (h : a⁻¹ * b ∉ H) : coeffOf π a b = 0 := by
  rw [coeffOf, if_neg h]

theorem cocycle_congr {a b c d : G} (h : a⁻¹ * b = c⁻¹ * d) :
    cocycle H a b = cocycle H c d := by
  classical
  by_cases hmem : a⁻¹ * b ∈ H
  · have hmem' : c⁻¹ * d ∈ H := by rw [← h]; exact hmem
    refine Subtype.ext ?_
    rw [cocycle_val hmem, cocycle_val hmem', h]
  · have hmem' : c⁻¹ * d ∉ H := by rw [← h]; exact hmem
    rw [cocycle, dif_neg hmem, cocycle, dif_neg hmem']

theorem cocycle_mul {a b d : G} (hab : a⁻¹ * b ∈ H) (hbd : b⁻¹ * d ∈ H) :
    cocycle H a b * cocycle H b d = cocycle H a d := by
  have had : a⁻¹ * d ∈ H := by
    have hrw : a⁻¹ * d = (a⁻¹ * b) * (b⁻¹ * d) := by group
    rw [hrw]
    exact H.mul_mem hab hbd
  refine Subtype.ext ?_
  show ((cocycle H a b : H) : G) * ((cocycle H b d : H) : G) = _
  rw [cocycle_val hab, cocycle_val hbd, cocycle_val had]
  group

theorem mem_of_mem_mul {a b d : G} (hbd : b⁻¹ * d ∈ H) (had : a⁻¹ * d ∈ H) :
    a⁻¹ * b ∈ H := by
  have hrw : a⁻¹ * b = (a⁻¹ * d) * (b⁻¹ * d)⁻¹ := by group
  rw [hrw]
  exact H.mul_mem had (H.inv_mem hbd)

theorem mem_mul_of_mem {a b d : G} (hab : a⁻¹ * b ∈ H) (hbd : b⁻¹ * d ∈ H) :
    a⁻¹ * d ∈ H := by
  have hrw : a⁻¹ * d = (a⁻¹ * b) * (b⁻¹ * d) := by group
  rw [hrw]
  exact H.mul_mem hab hbd

/-! ## The induced matrix -/

variable {m : ℕ}

/-- The induced matrix of a unitary family along a transversal. -/
noncomputable def indMat (T : Transversal G H m) (π : H → Matrix Y Y ℂ)
    (g : G) : Matrix (ampModel m Y) (ampModel m Y) ℂ :=
  Matrix.of fun p q => coeffOf π (T.rep p.1) (g * T.rep q.1) p.2 q.2

@[simp] theorem indMat_apply (T : Transversal G H m) (π : H → Matrix Y Y ℂ) (g : G)
    (p q : Fin m × Y.carrier) :
    indMat T π g p q = coeffOf π (T.rep p.1) (g * T.rep q.1) p.2 q.2 := rfl

/-- Off the block-monomial pattern the coefficient vanishes. -/
theorem coeffOf_eq_zero_of_ne (T : Transversal G H m) (π : H → Matrix Y Y ℂ)
    (g : G) {i j : Fin m} (h : T.perm g j ≠ i) :
    coeffOf π (T.rep i) (g * T.rep j) = 0 := by
  refine coeffOf_of_not_mem π ?_
  intro hcon
  exact h (T.idx_eq_of_mem hcon)

/-- **The induced matrix is block-monomial.** -/
theorem indMat_eq_monomial (T : Transversal G H m) (π : H → Matrix Y Y ℂ)
    (g : G) (p q : Fin m × Y.carrier) :
    indMat T π g p q
      = if T.perm g q.1 = p.1 then
          coeffOf π (T.rep (T.perm g q.1)) (g * T.rep q.1) p.2 q.2 else 0 := by
  by_cases hpq : T.perm g q.1 = p.1
  · rw [if_pos hpq, indMat_apply, hpq]
  · rw [if_neg hpq, indMat_apply, coeffOf_eq_zero_of_ne T π g hpq]
    rfl

/-- The induced family is unitary. -/
theorem indMat_mem_unitaryGroup (T : Transversal G H m)
    (π : H → Matrix Y Y ℂ) (hπ : ∀ h : H, π h ∈ Matrix.unitaryGroup Y ℂ)
    (g : G) : indMat T π g ∈ Matrix.unitaryGroup (ampModel m Y) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff']
  ext p q
  rw [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Fintype.sum_prod_type]
  by_cases hpq : p.1 = q.1
  · rw [Finset.sum_eq_single (T.perm g p.1)]
    · -- the surviving diagonal block is unitary
      set h : H := cocycle H (T.rep (T.perm g p.1)) (g * T.rep p.1) with hh
      have hmemp : (T.rep (T.perm g p.1))⁻¹ * (g * T.rep p.1) ∈ H := T.mem_idx _
      have hmemq : (T.rep (T.perm g p.1))⁻¹ * (g * T.rep q.1) ∈ H := by
        rw [← hpq]
        exact hmemp
      have hcp : coeffOf π (T.rep (T.perm g p.1)) (g * T.rep p.1) = π h :=
        coeffOf_of_mem π hmemp
      have hcq : coeffOf π (T.rep (T.perm g p.1)) (g * T.rep q.1) = π h := by
        rw [coeffOf_of_mem π hmemq, hh, hpq]
      have hentry : ∀ y : Y.carrier,
          (indMat T π g)ᴴ p (T.perm g p.1, y) * indMat T π g (T.perm g p.1, y) q
            = (starRingEnd ℂ) (π h y p.2) * π h y q.2 := by
        intro y
        rw [Matrix.conjTranspose_apply, indMat_apply, indMat_apply, hcp, hcq]
        rfl
      rw [Finset.sum_congr rfl fun y _ => hentry y]
      have hunit := (Matrix.mem_unitaryGroup_iff').mp (hπ h)
      rw [Matrix.star_eq_conjTranspose] at hunit
      have hval : ((π h)ᴴ * π h) p.2 q.2 = (1 : Matrix Y Y ℂ) p.2 q.2 := by
        rw [hunit]
      rw [Matrix.mul_apply] at hval
      have hcong : ∑ y : Y.carrier,
          (starRingEnd ℂ) (π h y p.2) * π h y q.2
          = ∑ y : Y.carrier, ((π h)ᴴ) p.2 y * (π h) y q.2 := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Matrix.conjTranspose_apply]
        rfl
      rw [hcong, hval, Matrix.one_apply, Matrix.one_apply]
      by_cases hy : p.2 = q.2
      · rw [if_pos hy, if_pos (Prod.ext hpq hy)]
      · rw [if_neg hy, if_neg (fun hcon => hy (congrArg Prod.snd hcon))]
    · intro i _ hi
      refine Finset.sum_eq_zero fun y _ => ?_
      have hzero : coeffOf π (T.rep i) (g * T.rep p.1) = 0 :=
        coeffOf_eq_zero_of_ne T π g (fun hcon => hi hcon.symm)
      rw [Matrix.conjTranspose_apply, indMat_apply, hzero]
      simp
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · -- different row blocks: the two supports are disjoint
    have hzero : ∀ i : Fin m, ∑ y : Y.carrier,
        (indMat T π g)ᴴ p (i, y) * indMat T π g (i, y) q = 0 := by
      intro i
      refine Finset.sum_eq_zero fun y _ => ?_
      by_cases hi : T.perm g p.1 = i
      · have hne : T.perm g q.1 ≠ i := by
          intro hcon
          have heq : T.perm g p.1 = T.perm g q.1 := hi.trans hcon.symm
          exact hpq (Equiv.injective (T.perm g) heq)
        have hzq : coeffOf π (T.rep i) (g * T.rep q.1) = 0 :=
          coeffOf_eq_zero_of_ne T π g hne
        rw [indMat_apply, hzq]
        simp
      · have hzp : coeffOf π (T.rep i) (g * T.rep p.1) = 0 :=
          coeffOf_eq_zero_of_ne T π g (fun hcon => hi hcon)
        rw [Matrix.conjTranspose_apply, indMat_apply, hzp]
        simp
    rw [Finset.sum_congr rfl fun i _ => hzero i, Finset.sum_const_zero,
      Matrix.one_apply, if_neg (fun hcon => hpq (congrArg Prod.fst hcon))]

/-! ## The multiplicative defect of the induced family -/

/-- The product of two induced matrices has a single surviving intermediate
block. -/
theorem indMat_mul_apply (T : Transversal G H m) (π : H → Matrix Y Y ℂ)
    (g₁ g₂ : G) (p q : Fin m × Y.carrier) :
    (indMat T π g₁ * indMat T π g₂) p q
      = (coeffOf π (T.rep p.1) (g₁ * T.rep (T.perm g₂ q.1))
          * coeffOf π (T.rep (T.perm g₂ q.1)) (g₂ * T.rep q.1)) p.2 q.2 := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (T.perm g₂ q.1)]
  · rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun y _ => rfl
  · intro i _ hi
    refine Finset.sum_eq_zero fun y _ => ?_
    have hzero : coeffOf π (T.rep i) (g₂ * T.rep q.1) = 0 :=
      coeffOf_eq_zero_of_ne T π g₂ (fun hcon => hi hcon.symm)
    simp only [indMat_apply]
    rw [hzero]
    simp
  · intro hcon
    exact absurd (Finset.mem_univ _) hcon

/-- **The induced defect is the maximum of the inducing defects.** -/
theorem norm_indMat_defect_le (T : Transversal G H m) (π : H → Matrix Y Y ℂ)
    (g₁ g₂ : G) {ε : ℝ} (hε : 0 ≤ ε)
    (hdef : ∀ j : Fin m,
      ‖π (cocycle H (T.rep (T.perm (g₁ * g₂) j)) (g₁ * T.rep (T.perm g₂ j))
            * cocycle H (T.rep (T.perm g₂ j)) (g₂ * T.rep j))
          - π (cocycle H (T.rep (T.perm (g₁ * g₂) j))
              (g₁ * T.rep (T.perm g₂ j)))
            * π (cocycle H (T.rep (T.perm g₂ j)) (g₂ * T.rep j))‖ ≤ ε) :
    ‖indMat T π (g₁ * g₂) - indMat T π g₁ * indMat T π g₂‖ ≤ ε := by
  classical
  set E : Fin m → Matrix Y Y ℂ := fun j =>
    π (cocycle H (T.rep (T.perm (g₁ * g₂) j)) (g₁ * T.rep (T.perm g₂ j))
        * cocycle H (T.rep (T.perm g₂ j)) (g₂ * T.rep j))
      - π (cocycle H (T.rep (T.perm (g₁ * g₂) j)) (g₁ * T.rep (T.perm g₂ j)))
        * π (cocycle H (T.rep (T.perm g₂ j)) (g₂ * T.rep j)) with hE
  refine l2_opNorm_monomialBlocks_le (T.perm (g₁ * g₂)) E hε hdef _ ?_
  intro p q
  -- the two intermediate memberships
  set j₀ : Fin m := T.perm g₂ q.1 with hj₀
  have hmem₂ : (T.rep j₀)⁻¹ * (g₂ * T.rep q.1) ∈ H := T.mem_idx _
  have hperm : T.perm (g₁ * g₂) q.1 = T.perm g₁ j₀ := by
    rw [T.perm_mul]
    rfl
  have hmem₁ : (T.rep (T.perm (g₁ * g₂) q.1))⁻¹ * (g₁ * T.rep j₀) ∈ H := by
    rw [hperm]
    exact T.mem_idx _
  have hmem₃ : (g₁ * T.rep j₀)⁻¹ * (g₁ * g₂ * T.rep q.1) ∈ H := by
    have hrw : (g₁ * T.rep j₀)⁻¹ * (g₁ * g₂ * T.rep q.1)
        = (T.rep j₀)⁻¹ * (g₂ * T.rep q.1) := by group
    rw [hrw]
    exact hmem₂
  rw [Matrix.sub_apply, indMat_eq_monomial, indMat_mul_apply]
  by_cases hpq : T.perm (g₁ * g₂) q.1 = p.1
  · rw [if_pos hpq, if_pos hpq, hE]
    have hmem₄ : (T.rep (T.perm (g₁ * g₂) q.1))⁻¹ * (g₁ * g₂ * T.rep q.1) ∈ H :=
      mem_mul_of_mem hmem₁ hmem₃
    have hleft : coeffOf π (T.rep (T.perm (g₁ * g₂) q.1)) (g₁ * g₂ * T.rep q.1)
        = π (cocycle H (T.rep (T.perm (g₁ * g₂) q.1)) (g₁ * T.rep j₀)
            * cocycle H (T.rep j₀) (g₂ * T.rep q.1)) := by
      have hcongr : cocycle H (g₁ * T.rep j₀) (g₁ * g₂ * T.rep q.1)
          = cocycle H (T.rep j₀) (g₂ * T.rep q.1) := by
        refine cocycle_congr ?_
        group
      rw [coeffOf_of_mem π hmem₄]
      congr 1
      rw [← cocycle_mul hmem₁ hmem₃, hcongr]
    have hright₁ : coeffOf π (T.rep p.1) (g₁ * T.rep j₀)
        = π (cocycle H (T.rep (T.perm (g₁ * g₂) q.1)) (g₁ * T.rep j₀)) := by
      rw [← hpq, coeffOf_of_mem π hmem₁]
    have hright₂ : coeffOf π (T.rep j₀) (g₂ * T.rep q.1)
        = π (cocycle H (T.rep j₀) (g₂ * T.rep q.1)) := coeffOf_of_mem π hmem₂
    rw [hleft, hright₁, hright₂]
    rfl
  · rw [if_neg hpq, if_neg hpq]
    have hz₁ : coeffOf π (T.rep p.1) (g₁ * g₂ * T.rep q.1) = 0 :=
      coeffOf_eq_zero_of_ne T π (g₁ * g₂) hpq
    have hz₂ : coeffOf π (T.rep p.1) (g₁ * T.rep j₀) = 0 := by
      refine coeffOf_eq_zero_of_ne T π g₁ ?_
      rw [← hperm]
      exact hpq
    rw [hz₂, Matrix.zero_mul]
    simp

/-! ## Reading the base block back -/

theorem l2_opNorm_one_eq (Z : FiniteModel) (hZ : 0 < Fintype.card Z) :
    ‖(1 : Matrix Z Z ℂ)‖ = 1 := by
  haveI : Nonempty Z.carrier := Fintype.card_pos_iff.mp hZ
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  simp

/-- At a transversal index whose representative is the identity, the induced
matrix returns the inducing family. -/
theorem indMat_base_block (T : Transversal G H m) (π : H → Matrix Y Y ℂ)
    {i₀ : Fin m} (h₀ : T.rep i₀ = 1) (h : G) (hh : h ∈ H) (y z : Y.carrier) :
    indMat T π h (i₀, y) (i₀, z) = π ⟨h, hh⟩ y z := by
  rw [indMat_apply, h₀]
  have hmem : (1 : G)⁻¹ * (h * 1) ∈ H := by simpa using hh
  rw [coeffOf_of_mem π hmem]
  have harg : cocycle H (1 : G) (h * 1) = ⟨h, hh⟩ := by
    refine Subtype.ext ?_
    rw [cocycle_val hmem]
    simp
  rw [harg]

/-- A moved transversal index forces the induced matrix to stay a full unit
away from the identity. -/
theorem one_le_norm_indMat_sub_one (T : Transversal G H m)
    (π : H → Matrix Y Y ℂ) (hY : 0 < Fintype.card Y) (g : G) {j : Fin m}
    (hj : T.perm g j ≠ j) : 1 ≤ ‖indMat T π g - 1‖ := by
  classical
  have hblock : (indMat T π g - 1).submatrix
      (fun y : Y.carrier => ((j, y) : Fin m × Y.carrier))
      (fun y : Y.carrier => ((j, y) : Fin m × Y.carrier))
      = - (1 : Matrix Y Y ℂ) := by
    ext y z
    rw [Matrix.submatrix_apply, Matrix.sub_apply, indMat_eq_monomial,
      if_neg hj, Matrix.neg_apply, Matrix.one_apply, Matrix.one_apply]
    by_cases hyz : y = z
    · subst hyz
      simp
    · rw [if_neg hyz, if_neg (fun hcon => hyz (congrArg Prod.snd hcon))]
      ring
  have hle := l2_opNorm_block_le (Y := Y) j (indMat T π g - 1)
  rw [hblock, norm_neg, l2_opNorm_one_eq Y hY] at hle
  exact hle

/-! ## Finite-index extensions of MF groups -/

/-- A finite-index subgroup has a transversal whose base representative is the
identity. -/
theorem exists_transversal (H : Subgroup G) [H.FiniteIndex] :
    ∃ (m : ℕ) (T : Transversal G H m) (i₀ : Fin m), 0 < m ∧ T.rep i₀ = 1 := by
  classical
  haveI : Finite (G ⧸ H) := H.finite_quotient_of_finiteIndex
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set m : ℕ := Fintype.card (G ⧸ H) with hm
  set e : (G ⧸ H) ≃ Fin m := Fintype.equivFin _ with he
  have hmpos : 0 < m := Fintype.card_pos
  set i₀ : Fin m := e (QuotientGroup.mk 1) with hi₀
  set r : Fin m → G := fun i => if i = i₀ then 1 else (e.symm i).out with hr
  have hrmk : ∀ i : Fin m, (QuotientGroup.mk (r i) : G ⧸ H) = e.symm i := by
    intro i
    by_cases hi : i = i₀
    · have h1 : r i = 1 := by
        rw [hr]
        simp [hi]
      rw [h1, hi, hi₀, Equiv.symm_apply_apply]
    · have h1 : r i = (e.symm i).out := by
        rw [hr]
        simp [hi]
      rw [h1]
      exact Quotient.out_eq _
  refine ⟨m, ⟨r, fun b => e (QuotientGroup.mk b), ?_⟩, i₀, hmpos, ?_⟩
  · intro i b
    show e (QuotientGroup.mk b) = i ↔ (r i)⁻¹ * b ∈ H
    constructor
    · intro hb
      refine (QuotientGroup.eq (s := H)).mp ?_
      rw [hrmk i, ← hb, Equiv.symm_apply_apply]
    · intro hb
      have heq := (QuotientGroup.eq (s := H)).mpr hb
      rw [hrmk i] at heq
      rw [← heq, Equiv.apply_symm_apply]
  · show r i₀ = 1
    rw [hr]
    simp

/-- **Section 49.1 for coronas.**  A corona representation of a finite-index
subgroup induces one of the whole group: the induced family kills only elements
of the subgroup, and on the subgroup it reproduces the original. -/
theorem exists_induced_corona (H : Subgroup G) [H.FiniteIndex]
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (Θ : H →* NormMatrixCoronaUnitary X) :
    ∃ (X' : ℕ → FiniteModel) (_ : ∀ n, 0 < Fintype.card (X' n))
      (Φ : G →* NormMatrixCoronaUnitary X'),
      (∀ g : G, Φ g = 1 → g ∈ H) ∧
        ∀ (x : G) (hx : x ∈ H), Φ x = 1 → Θ ⟨x, hx⟩ = 1 := by
  classical
  obtain ⟨m, T, i₀, hm, hrep₀⟩ := exists_transversal H
  choose lift hlift using fun h : H => QuotientGroup.mk_surjective (Θ h)
  set πn : ∀ n : ℕ, H → Matrix (X n) (X n) ℂ :=
    fun n h => (lift h n : Matrix (X n) (X n) ℂ) with hπn
  set U : G → ∀ n, Matrix.unitaryGroup (ampModel m (X n)) ℂ := fun g n =>
    ⟨indMat T (πn n) g,
      indMat_mem_unitaryGroup T (πn n) (fun h => (lift h n).2) g⟩ with hU
  have hX'pos : ∀ n, 0 < Fintype.card (ampModel m (X n)) := by
    intro n
    show 0 < Fintype.card (Fin m × (X n).carrier)
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_pos hm (hX n)
  have hdefect : ∀ (g₁ g₂ : G) (ε : ℝ), 0 < ε → ∀ᶠ n in Filter.cofinite,
      ‖indMat T (πn n) (g₁ * g₂)
        - indMat T (πn n) g₁ * indMat T (πn n) g₂‖ ≤ ε := by
    intro g₁ g₂ ε hε
    have hall : ∀ j : Fin m, ∀ᶠ n in Filter.cofinite,
        ‖πn n (cocycle H (T.rep (T.perm (g₁ * g₂) j))
              (g₁ * T.rep (T.perm g₂ j))
            * cocycle H (T.rep (T.perm g₂ j)) (g₂ * T.rep j))
          - πn n (cocycle H (T.rep (T.perm (g₁ * g₂) j))
              (g₁ * T.rep (T.perm g₂ j)))
            * πn n (cocycle H (T.rep (T.perm g₂ j)) (g₂ * T.rep j))‖ ≤ ε := by
      intro j
      exact normMatrixCorona_lift_eventually_multiplicative X Θ lift hlift _ _ ε hε
    rw [← Filter.eventually_all] at hall
    filter_upwards [hall] with n hn
    exact norm_indMat_defect_le T (πn n) g₁ g₂ hε.le hn
  refine ⟨fun n => ampModel m (X n), hX'pos,
    MonoidHom.mk' (fun g => QuotientGroup.mk (U g)) ?_, ?_, ?_⟩
  · -- multiplicativity in the corona
    intro g₁ g₂
    refine (QuotientGroup.eq (s := nullCofiniteOpSubgroup _)).mpr ?_
    intro ε hε
    filter_upwards [hdefect g₁ g₂ (ε / 2) (by linarith)] with n hn
    have hval : opLength (ampModel m (X n))
        (((U (g₁ * g₂))⁻¹ * (U g₁ * U g₂)) n)
        = ‖indMat T (πn n) g₁ * indMat T (πn n) g₂
            - indMat T (πn n) (g₁ * g₂)‖ := by
      show opLength (ampModel m (X n))
        ((U (g₁ * g₂) n)⁻¹ * (U g₁ n * U g₂ n)) = _
      rw [opLength_inv_mul]
      rfl
    rw [hval, norm_sub_rev]
    linarith
  · -- a killed element lies in the subgroup: its coset permutation is trivial
    intro g hg
    have hnull : U g ∈ nullCofiniteOpSubgroup (fun n => ampModel m (X n)) :=
      (QuotientGroup.eq_one_iff (U g)).mp hg
    have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.cofinite,
        ‖indMat T (πn n) g - 1‖ < ε := by
      intro ε hε
      filter_upwards [hnull ε hε] with n hn
      exact hn
    have hperm : ∀ j : Fin m, T.perm g j = j := by
      intro j
      by_contra hj
      have hbig : ∀ n : ℕ, (1 : ℝ) ≤ ‖indMat T (πn n) g - 1‖ := fun n =>
        one_le_norm_indMat_sub_one T (πn n) (hX n) g hj
      have hlt := hsmall 1 one_pos
      rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop] at hlt
      obtain ⟨N, hN⟩ := hlt
      exact absurd (hN N (le_refl N)) (not_lt.mpr (hbig N))
    have hj := hperm i₀
    have hmem := T.mem_idx (g * T.rep i₀)
    rw [show T.idx (g * T.rep i₀) = i₀ from hj] at hmem
    rw [hrep₀] at hmem
    simpa using hmem
  · -- on the subgroup the base block reproduces the original representation
    intro x hx hxg
    have hnull : U x ∈ nullCofiniteOpSubgroup (fun n => ampModel m (X n)) :=
      (QuotientGroup.eq_one_iff (U x)).mp hxg
    have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in Filter.cofinite,
        ‖indMat T (πn n) x - 1‖ < ε := by
      intro ε hε
      filter_upwards [hnull ε hε] with n hn
      exact hn
    have hsub : ∀ n : ℕ, ((indMat T (πn n) x - 1).submatrix
        (fun y : (X n).carrier => ((i₀, y) : Fin m × (X n).carrier))
        (fun y : (X n).carrier => ((i₀, y) : Fin m × (X n).carrier)))
        = (lift ⟨x, hx⟩ n : Matrix (X n) (X n) ℂ) - 1 := by
      intro n
      ext y z
      rw [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.sub_apply,
        indMat_base_block T (πn n) hrep₀ x hx, Matrix.one_apply,
        Matrix.one_apply]
      by_cases hyz : y = z
      · subst hyz
        simp [hπn]
      · rw [if_neg hyz, if_neg (fun hcon => hyz (congrArg Prod.snd hcon))]
    rw [← hlift ⟨x, hx⟩]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    intro ε hε
    filter_upwards [hsmall ε hε] with n hn
    have hle := l2_opNorm_block_le (Y := X n) i₀ (indMat T (πn n) x - 1)
    rw [hsub n] at hle
    show opLength (X n) (lift ⟨x, hx⟩ n) < ε
    rw [opLength]
    exact lt_of_le_of_lt hle hn

/-- **Corollary 49.2A.**  The MF property passes from a finite-index subgroup to
the whole group. -/
theorem isOperatorMF_of_finiteIndex_subgroup (H : Subgroup G) [H.FiniteIndex]
    (hH : IsOperatorMF H) : IsOperatorMF G := by
  obtain ⟨X, hX, Θ, hΘ⟩ := hH
  obtain ⟨X', hX', Φ, hker, hbase⟩ := exists_induced_corona H X hX Θ
  refine ⟨X', hX', Φ, ?_⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgH : g ∈ H := hker g hg
  have hΘg : Θ ⟨g, hgH⟩ = 1 := hbase g hgH hg
  have hone : Θ ⟨g, hgH⟩ = Θ 1 := by rw [hΘg, map_one]
  have heq := hΘ hone
  have hval := congrArg (fun z : H => (z : G)) heq
  simpa using hval

/-- **Theorem 49.2, the inductive direction.**  An element of a finite-index
subgroup invisible to every corona representation of the ambient group is
invisible to every corona representation of the subgroup. -/
theorem corona_invisible_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    {x : G} (hx : x ∈ H)
    (hinv : ∀ (X : ℕ → FiniteModel), (∀ n, 0 < Fintype.card (X n)) →
      ∀ rho : G →* NormMatrixCoronaUnitary X, rho x = 1)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (Θ : H →* NormMatrixCoronaUnitary X) : Θ ⟨x, hx⟩ = 1 := by
  obtain ⟨X', hX', Φ, -, hbase⟩ := exists_induced_corona H X hX Θ
  exact hbase x hx (hinv X' hX' Φ)

/-- The restriction direction is immediate: a corona representation of the
ambient group restricts to one of the subgroup. -/
theorem corona_invisible_restrict (H : Subgroup G) {x : G} (hx : x ∈ H)
    (hinv : ∀ (X : ℕ → FiniteModel), (∀ n, 0 < Fintype.card (X n)) →
      ∀ Θ : H →* NormMatrixCoronaUnitary X, Θ ⟨x, hx⟩ = 1)
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : G →* NormMatrixCoronaUnitary X) : rho x = 1 := by
  have := hinv X hX (rho.comp H.subtype)
  simpa using this

end InducedCorona

end GroupApproximation
