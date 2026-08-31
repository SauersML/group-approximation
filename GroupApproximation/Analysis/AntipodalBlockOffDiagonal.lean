import GroupApproximation.Analysis.AntipodalHomogeneousBlock

namespace GroupApproximation
namespace STW22

open GroupApproximation.ThirdParty.HamSandwich.SphereOddDegree

noncomputable section

open scoped CStarAlgebra ComplexOrder Matrix

/-! ## Entrywise form of the antipodal covariance -/

/-- Conjugation by the block involution multiplies the `(i,j)` entry by the
two diagonal signs. -/
theorem blockInvolution_conjugation_apply {s : ℕ}
    (a : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ)
    (i j : Fin (s + 1)) :
    (blockInvolution s * a * blockInvolution s) i j =
      blockSign i * a i j * blockSign j := by
  change
    ((Matrix.diagonal (blockSign (s := s)) * CStarMatrix.ofMatrix.symm a) *
      Matrix.diagonal (blockSign (s := s))) i j =
      blockSign i * a i j * blockSign j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rfl

/-- Antipodal covariance of a real-projective block, entry by entry. -/
theorem realProjectiveBlock_entry_neg {d s : ℕ}
    (a : RealProjectiveBlock d s) (x : Sphere d)
    (i j : Fin (s + 1)) :
    a.1 (-x) i j = blockSign i * a.1 x i j * blockSign j := by
  have hcov := a.2 x
  have hentry := congrArg (fun m => m i j) hcov
  simpa only [blockInvolution_conjugation_apply] using hentry

/-! ## Continuous odd off-diagonal entries -/

/-- Evaluation at one matrix entry, bundled as a continuous map. -/
def matrixEntryMap {s : ℕ} (i j : Fin (s + 1)) :
    C(CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ, ℂ) where
  toFun a := a i j
  continuous_toFun := (continuous_apply j).comp (continuous_apply i)

@[simp] theorem matrixEntryMap_apply {s : ℕ} (i j : Fin (s + 1))
    (a : CStarMatrix (Fin (s + 1)) (Fin (s + 1)) ℂ) :
    matrixEntryMap i j a = a i j := rfl

/-- The lower-left entry in tautological row `k` and the distinguished
trivial column.  Its bundled codomain records continuity. -/
def offDiagonalColumnEntry {d s : ℕ} (a : RealProjectiveBlock d s)
    (k : Fin s) : C(Sphere d, ℂ) :=
  (matrixEntryMap k.succ 0).comp a.1

/-- The upper-right entry in the distinguished trivial row and tautological
column `k`.  Its bundled codomain records continuity. -/
def offDiagonalRowEntry {d s : ℕ} (a : RealProjectiveBlock d s)
    (k : Fin s) : C(Sphere d, ℂ) :=
  (matrixEntryMap 0 k.succ).comp a.1

@[simp] theorem offDiagonalColumnEntry_apply {d s : ℕ}
    (a : RealProjectiveBlock d s) (k : Fin s) (x : Sphere d) :
    offDiagonalColumnEntry a k x = a.1 x k.succ 0 := rfl

@[simp] theorem offDiagonalRowEntry_apply {d s : ℕ}
    (a : RealProjectiveBlock d s) (k : Fin s) (x : Sphere d) :
    offDiagonalRowEntry a k x = a.1 x 0 k.succ := rfl

/-- Every lower-left entry is odd under the antipodal action. -/
theorem offDiagonalColumnEntry_neg {d s : ℕ}
    (a : RealProjectiveBlock d s) (k : Fin s) (x : Sphere d) :
    offDiagonalColumnEntry a k (-x) = -offDiagonalColumnEntry a k x := by
  rw [offDiagonalColumnEntry_apply, offDiagonalColumnEntry_apply,
    realProjectiveBlock_entry_neg]
  simp [blockSign]

/-- Every upper-right entry is odd under the antipodal action. -/
theorem offDiagonalRowEntry_neg {d s : ℕ}
    (a : RealProjectiveBlock d s) (k : Fin s) (x : Sphere d) :
    offDiagonalRowEntry a k (-x) = -offDiagonalRowEntry a k x := by
  rw [offDiagonalRowEntry_apply, offDiagonalRowEntry_apply,
    realProjectiveBlock_entry_neg]
  simp [blockSign]

/-- Indices for all off-diagonal entries in a family: `inl k` denotes the
lower-left column entry and `inr k` the upper-right row entry. -/
abbrev OffDiagonalIndex (ι : Type*) (s : ℕ) := ι × (Fin s ⊕ Fin s)

/-- All lower-left and upper-right entries of a family of block elements,
assembled into one continuous map.  This is the map to which the
Borsuk--Ulam common-zero theorem is applied. -/
def simultaneousOffDiagonalMap {ι : Type*} {d s : ℕ}
    (a : ι → RealProjectiveBlock d s) :
    C(Sphere d, OffDiagonalIndex ι s → ℂ) where
  toFun x p :=
    match p.2 with
    | Sum.inl k => offDiagonalColumnEntry (a p.1) k x
    | Sum.inr k => offDiagonalRowEntry (a p.1) k x
  continuous_toFun := by
    apply continuous_pi
    rintro ⟨r, k⟩
    cases k with
    | inl k => exact (offDiagonalColumnEntry (a r) k).continuous
    | inr k => exact (offDiagonalRowEntry (a r) k).continuous

@[simp] theorem simultaneousOffDiagonalMap_apply_inl
    {ι : Type*} {d s : ℕ} (a : ι → RealProjectiveBlock d s)
    (x : Sphere d) (r : ι) (k : Fin s) :
    simultaneousOffDiagonalMap a x (r, Sum.inl k) = (a r).1 x k.succ 0 := rfl

@[simp] theorem simultaneousOffDiagonalMap_apply_inr
    {ι : Type*} {d s : ℕ} (a : ι → RealProjectiveBlock d s)
    (x : Sphere d) (r : ι) (k : Fin s) :
    simultaneousOffDiagonalMap a x (r, Sum.inr k) = (a r).1 x 0 k.succ := rfl

/-- The simultaneous off-diagonal map is odd. -/
theorem simultaneousOffDiagonalMap_neg
    {ι : Type*} {d s : ℕ} (a : ι → RealProjectiveBlock d s)
    (x : Sphere d) :
    simultaneousOffDiagonalMap a (-x) = -simultaneousOffDiagonalMap a x := by
  funext p
  rcases p with ⟨r, k⟩
  cases k with
  | inl k => exact offDiagonalColumnEntry_neg (a r) k x
  | inr k => exact offDiagonalRowEntry_neg (a r) k x

/-- A zero of the assembled map simultaneously zeros every lower-left and
upper-right entry in the family. -/
theorem offDiagonal_entries_eq_zero_of_simultaneous_eq_zero
    {ι : Type*} {d s : ℕ} (a : ι → RealProjectiveBlock d s)
    {x : Sphere d} (hx : simultaneousOffDiagonalMap a x = 0) :
    (∀ (r : ι) (k : Fin s), (a r).1 x k.succ 0 = 0) ∧
      ∀ (r : ι) (k : Fin s), (a r).1 x 0 k.succ = 0 := by
  constructor
  · intro r k
    have h := congrFun hx (r, Sum.inl k)
    simpa using h
  · intro r k
    have h := congrFun hx (r, Sum.inr k)
    simpa using h

/-- Conversely, simultaneous vanishing of the two off-diagonal corners is
exactly vanishing of the assembled map. -/
theorem simultaneousOffDiagonalMap_eq_zero_of_entries
    {ι : Type*} {d s : ℕ} (a : ι → RealProjectiveBlock d s)
    (x : Sphere d)
    (hcol : ∀ (r : ι) (k : Fin s), (a r).1 x k.succ 0 = 0)
    (hrow : ∀ (r : ι) (k : Fin s), (a r).1 x 0 k.succ = 0) :
    simultaneousOffDiagonalMap a x = 0 := by
  funext p
  rcases p with ⟨r, k⟩
  cases k with
  | inl k => exact hcol r k
  | inr k => exact hrow r k

end

end STW22
end GroupApproximation
