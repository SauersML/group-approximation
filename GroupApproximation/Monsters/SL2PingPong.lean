import GroupApproximation.Monsters.MoebiusIrrationalAction
import GroupApproximation.GroupTheory.FiniteCyclicHom
import Mathlib.GroupTheory.CoprodI

/-!
# Ping-pong for the modular pair on the irrational line

The signed swap `S = e₁₂(1) e₂₁(-1) e₁₂(1)` and the rotation
`R = e₁₂(1) e₂₁(-1)` act on the irrational reals by

  `S : x ↦ -1/x` ,  `R : x ↦ 1/(1-x)` ,  `R² : x ↦ (x-1)/x` .

Both matrices square (resp. cube) to `-1`, which acts trivially, so
they generate a `ℤ/2` and a `ℤ/3` inside `Equiv.Perm Irr`.  The
nontrivial power of `S` maps the positive irrationals into the negative
ones, and the two nontrivial powers of `R` map the negative irrationals
into the positive ones.  By the Ping-Pong-Lemma the induced map

  `ψ : (ℤ/2) ∗ (ℤ/3) →* Equiv.Perm Irr`

is injective.  This is the classical free-product decomposition of the
modular group, keyed to the exact generators of the rank-two braid
presentation; the completeness argument threads its kernel chase
through `ψ`.
-/

namespace GroupApproximation
namespace SL2PingPong

open SL2BraidPresentation MoebiusIrrationalAction FiniteCyclicHom
open scoped Pointwise

noncomputable section

/-! ## The two matrices and their permutations -/

/-- The matrix of the first braid generator. -/
def Amat : SL2 := sl2Elem 0

/-- The matrix of the second braid generator. -/
def Bmat : SL2 := sl2Elem 1

/-- The signed swap `A B A`. -/
def Smat : SL2 := Amat * Bmat * Amat

/-- The rotation `A B`. -/
def Rmat : SL2 := Amat * Bmat

/-- Minus the identity. -/
def negOne : SL2 := ⟨!![-1, 0; 0, -1], by decide⟩

theorem Smat_coe : ((Smat : SL2) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![0, 1; -1, 0] := by
  show ((Amat * Bmat * Amat : SL2) : Matrix (Fin 2) (Fin 2) ℤ) = _
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  decide

theorem Rmat_coe : ((Rmat : SL2) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![0, 1; -1, 1] := by
  show ((Amat * Bmat : SL2) : Matrix (Fin 2) (Fin 2) ℤ) = _
  rw [Matrix.SpecialLinearGroup.coe_mul]
  decide

theorem RmatSq_coe : ((Rmat * Rmat : SL2) : Matrix (Fin 2) (Fin 2) ℤ) =
    !![-1, 1; -1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Rmat_coe]
  decide

/-- Minus the identity acts trivially on the boundary. -/
theorem rep_negOne : rep negOne = 1 := by
  apply Equiv.ext
  intro x
  show moebius negOne x = x
  apply Subtype.ext
  show moebiusVal negOne x.1 = x.1
  simp [moebiusVal, ent, negOne]

/-- The boundary permutation of the signed swap. -/
def sigmaPerm : Equiv.Perm Irr := rep Smat

/-- The boundary permutation of the rotation. -/
def rhoPerm : Equiv.Perm Irr := rep Rmat

theorem Smat_sq : Smat * Smat = negOne := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Smat_coe]
  decide

theorem Rmat_cube : Rmat * Rmat * Rmat = negOne := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, RmatSq_coe, Rmat_coe]
  decide

theorem sigmaPerm_sq : sigmaPerm ^ 2 = 1 := by
  rw [pow_two]
  show rep Smat * rep Smat = 1
  rw [← map_mul, Smat_sq, rep_negOne]

theorem rhoPerm_cube : rhoPerm ^ 3 = 1 := by
  rw [pow_succ, pow_two]
  show rep Rmat * rep Rmat * rep Rmat = 1
  rw [← map_mul, ← map_mul, Rmat_cube, rep_negOne]

/-! ## Value formulas and the sign ping-pong -/

/-- Reading the fractional-linear value off a computed coercion. -/
theorem moebiusVal_of_coe {M : SL2} {a b c d : ℤ}
    (h : (M : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d]) (x : ℝ) :
    moebiusVal M x =
      (((a : ℤ) : ℝ) * x + ((b : ℤ) : ℝ)) /
        (((c : ℤ) : ℝ) * x + ((d : ℤ) : ℝ)) := by
  have e00 : (M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = a := by rw [h]; simp
  have e01 : (M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = b := by rw [h]; simp
  have e10 : (M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = c := by rw [h]; simp
  have e11 : (M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = d := by rw [h]; simp
  show (((M : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) * x +
      ((M : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ)) /
    (((M : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * x +
      ((M : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ)) = _
  rw [e00, e01, e10, e11]

/-- The swap sends positive irrationals to negative ones. -/
theorem sigma_neg_of_pos {x : Irr} (hx : 0 < x.1) :
    (sigmaPerm x).1 < 0 := by
  show moebiusVal Smat x.1 < 0
  rw [moebiusVal_of_coe Smat_coe]
  push_cast
  rw [show (0 : ℝ) * x.1 + 1 = 1 from by ring,
    show (-1 : ℝ) * x.1 + 0 = -x.1 from by ring]
  exact div_neg_of_pos_of_neg one_pos (neg_lt_zero.mpr hx)

/-- The rotation sends negative irrationals to positive ones. -/
theorem rho_pos_of_neg {x : Irr} (hx : x.1 < 0) :
    0 < (rhoPerm x).1 := by
  show 0 < moebiusVal Rmat x.1
  rw [moebiusVal_of_coe Rmat_coe]
  push_cast
  rw [show (0 : ℝ) * x.1 + 1 = 1 from by ring,
    show (-1 : ℝ) * x.1 + 1 = 1 - x.1 from by ring]
  exact div_pos one_pos (sub_pos.mpr (hx.trans zero_lt_one))

/-- The squared rotation sends negative irrationals to positive ones. -/
theorem rho_sq_pos_of_neg {x : Irr} (hx : x.1 < 0) :
    0 < ((rhoPerm * rhoPerm) x).1 := by
  have hmul : rhoPerm * rhoPerm = rep (Rmat * Rmat) :=
    (map_mul rep Rmat Rmat).symm
  rw [hmul]
  show 0 < moebiusVal (Rmat * Rmat) x.1
  rw [moebiusVal_of_coe RmatSq_coe]
  push_cast
  rw [show (-1 : ℝ) * x.1 + 1 = 1 - x.1 from by ring,
    show (-1 : ℝ) * x.1 + 0 = -x.1 from by ring]
  exact div_pos (sub_pos.mpr (hx.trans zero_lt_one)) (neg_pos.mpr hx)

/-! ## The free-product family -/

/-- The two cyclic factors `ℤ/2` and `ℤ/3`. -/
abbrev fam : Fin 2 → Type
  | 0 => Multiplicative (ZMod 2)
  | 1 => Multiplicative (ZMod 3)

instance famGroup : ∀ i, Group (fam i) := fun i =>
  match i with
  | 0 => inferInstance
  | 1 => inferInstance

/-- The generator images: swap and rotation. -/
noncomputable def pingHom : ∀ i : Fin 2, fam i →* Equiv.Perm Irr :=
  fun i =>
    match i with
    | 0 => cyclicHom 2 sigmaPerm sigmaPerm_sq
    | 1 => cyclicHom 3 rhoPerm rhoPerm_cube

/-- The ping-pong sets: the negative and positive irrationals. -/
def pingSet : Fin 2 → Set Irr
  | 0 => {x : Irr | x.1 < 0}
  | 1 => {x : Irr | 0 < x.1}

theorem pingSet_nonempty : ∀ i, (pingSet i).Nonempty := by
  intro i
  have h2 : (0 : ℝ) < Real.sqrt 2 :=
    Real.sqrt_pos.mpr (by norm_num)
  match i with
  | 0 => exact ⟨⟨-Real.sqrt 2, irrational_sqrt_two.neg⟩, by
      show -Real.sqrt 2 < 0
      exact neg_lt_zero.mpr h2⟩
  | 1 => exact ⟨⟨Real.sqrt 2, irrational_sqrt_two⟩, h2⟩

theorem pingSet_disjoint : Pairwise (Function.onFun Disjoint pingSet) := by
  intro i j hij
  match i, j, hij with
  | 0, 0, hij => exact absurd rfl hij
  | 0, 1, _ =>
      refine Set.disjoint_left.mpr ?_
      intro x hx0 hx1
      have h0 : x.1 < 0 := hx0
      have h1 : 0 < x.1 := hx1
      exact (not_lt_of_ge h1.le) h0
  | 1, 0, _ =>
      refine Set.disjoint_left.mpr ?_
      intro x hx1 hx0
      have h0 : x.1 < 0 := hx0
      have h1 : 0 < x.1 := hx1
      exact (not_lt_of_ge h1.le) h0
  | 1, 1, hij => exact absurd rfl hij

theorem card_fam_one : 3 ≤ Cardinal.mk (fam 1) := by
  rw [Cardinal.mk_fintype]
  norm_num

private theorem zmod2_cases : ∀ k : ZMod 2,
    k = 0 ∨ k = ((1 : ℤ) : ZMod 2) := by decide

private theorem zmod3_cases : ∀ k : ZMod 3,
    k = 0 ∨ k = ((1 : ℤ) : ZMod 3) ∨ k = ((2 : ℤ) : ZMod 3) := by decide

/-- The ping-pong condition for the two factors. -/
theorem pingPong_pairwise : Pairwise fun i j =>
    ∀ h : fam i, h ≠ 1 → pingHom i h • pingSet j ⊆ pingSet i := by
  intro i j hij
  match i, j, hij with
  | 0, 0, hij => exact absurd rfl hij
  | 1, 1, hij => exact absurd rfl hij
  | 0, 1, _ =>
      intro h hne
      rcases zmod2_cases h.toAdd with h0 | h1
      · exact absurd (by
          rw [← ofAdd_toAdd h, h0]
          rfl) hne
      · have hval : pingHom 0 h = sigmaPerm := by
          rw [← ofAdd_toAdd h, h1]
          exact cyclicHom_one_val 2 sigmaPerm sigmaPerm_sq
        rw [hval]
        intro y hy
        obtain ⟨x, hxmem, rfl⟩ := hy
        show (sigmaPerm • x).1 < 0
        exact sigma_neg_of_pos hxmem
  | 1, 0, _ =>
      intro h hne
      rcases zmod3_cases h.toAdd with h0 | h1 | h2
      · exact absurd (by
          rw [← ofAdd_toAdd h, h0]
          rfl) hne
      · have hval : pingHom 1 h = rhoPerm := by
          rw [← ofAdd_toAdd h, h1]
          exact cyclicHom_one_val 3 rhoPerm rhoPerm_cube
        rw [hval]
        intro y hy
        obtain ⟨x, hxmem, rfl⟩ := hy
        show 0 < (rhoPerm • x).1
        exact rho_pos_of_neg hxmem
      · have hval : pingHom 1 h = rhoPerm * rhoPerm := by
          rw [← ofAdd_toAdd h, h2]
          show cyclicHom 3 rhoPerm rhoPerm_cube
            (Multiplicative.ofAdd ((2 : ℤ) : ZMod 3)) = rhoPerm * rhoPerm
          rw [cyclicHom_intCast 3 rhoPerm rhoPerm_cube 2,
            show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]
        rw [hval]
        intro y hy
        obtain ⟨x, hxmem, rfl⟩ := hy
        show 0 < ((rhoPerm * rhoPerm) • x).1
        exact rho_sq_pos_of_neg hxmem

/-! ## The injective free-product map -/

/-- The comparison map from the free product `ℤ/2 ∗ ℤ/3` to the
boundary permutations. -/
noncomputable def psi : Monoid.CoprodI fam →* Equiv.Perm Irr :=
  Monoid.CoprodI.lift pingHom

/-- **Ping-pong injectivity.**  The free product `ℤ/2 ∗ ℤ/3` embeds in
the boundary permutations through the swap and the rotation. -/
theorem psi_injective : Function.Injective psi :=
  Monoid.CoprodI.lift_injective_of_ping_pong pingHom
    (Or.inr ⟨1, card_fam_one⟩) pingSet pingSet_nonempty
    pingSet_disjoint pingPong_pairwise

end

end SL2PingPong
end GroupApproximation
