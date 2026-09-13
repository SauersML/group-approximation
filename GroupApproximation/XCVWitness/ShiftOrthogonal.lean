import GroupApproximation.XCVWitness.KishimotoSimple

/-!
# Shift models and orthogonal products

`ShiftModel Z C` records what the simplicity proof uses about an infinite tensor product
`C = ⊗_{j∈ℤ} Z` with its shift:
* coordinate embeddings `coord k : Z →⋆ₐ[ℂ] C` and blocks `block S`, the ⋆-subalgebra carried by
  the coordinates in `S ⊆ ℤ`;
* blocks over disjoint index sets commute, and their products multiply norms (the cross-norm
  property of the minimal tensor product);
* the central blocks `block [-M, M]` are dense;
* a group of ⋆-endomorphisms `shift n` moving coordinate `k` to `k + n`.

`hprod z a m = z_a · z_{a+1} ⋯ z_{a+m-1}` is a product of copies of `z` in consecutive coordinates.
For `g h : Z` of norm one with `h⋆g = 0`, the element `F = g_j · h_{j+1} ⋯ h_{j+N}` has norm
one, lies in `block [j, ∞)`, and satisfies `F⋆ · shift n F = 0` for `0 < |n| ≤ N`. For `n > 0`,
the factor `h⋆` of `F⋆` at coordinate `j + n` meets the factor `g` of `shift n F`. Negative `n`
follow by applying `shift n` to the adjoint.
-/

namespace GroupApproximation
namespace XCVWitness

/-- An infinite tensor product `C = ⊗_{j∈ℤ} Z` with its shift, as the simplicity proof uses it. -/
structure ShiftModel (Z C : Type*) [CStarAlgebra Z] [CStarAlgebra C] where
  /-- The coordinate embedding at `k`. -/
  coord : ℤ → Z →⋆ₐ[ℂ] C
  /-- The ⋆-subalgebra carried by the coordinates in a set of indices. -/
  block : Set ℤ → StarSubalgebra ℂ C
  coord_mem : ∀ k z, coord k z ∈ block {k}
  block_mono : ∀ {S T : Set ℤ}, S ⊆ T → ∀ x ∈ block S, x ∈ block T
  commute_of_disjoint : ∀ {S T : Set ℤ}, Disjoint S T →
    ∀ x ∈ block S, ∀ y ∈ block T, Commute x y
  norm_mul_of_disjoint : ∀ {S T : Set ℤ}, Disjoint S T →
    ∀ x ∈ block S, ∀ y ∈ block T, ‖x * y‖ = ‖x‖ * ‖y‖
  norm_coord : ∀ k z, ‖coord k z‖ = ‖z‖
  dense : ∀ (c : C) (ε : ℝ), 0 < ε →
    ∃ M : ℕ, ∃ c' ∈ block (Set.Icc (-(M : ℤ)) M), ‖c - c'‖ ≤ ε
  /-- The shift by `n`. -/
  shift : ℤ → C →⋆ₐ[ℂ] C
  shift_coord : ∀ n k z, shift n (coord k z) = coord (k + n) z
  shift_add : ∀ m n c, shift m (shift n c) = shift (m + n) c
  shift_zero : ∀ c, shift 0 c = c

theorem disjoint_singleton_Ici (a : ℤ) : Disjoint ({a} : Set ℤ) (Set.Ici (a + 1)) :=
  Set.disjoint_left.2 fun x hx hx' => by
    rw [Set.mem_singleton_iff] at hx
    rw [Set.mem_Ici] at hx'
    omega

namespace ShiftModel

/-- Model test: `ℂ` with every block `⊤` and the identity shift is a shift model over `ℂ`. -/
noncomputable def complex : ShiftModel ℂ ℂ where
  coord _ := StarAlgHom.id ℂ ℂ
  block _ := ⊤
  coord_mem _ _ := StarSubalgebra.mem_top
  block_mono _ _ _ := StarSubalgebra.mem_top
  commute_of_disjoint _ x _ y _ := Commute.all x y
  norm_mul_of_disjoint _ x _ y _ := norm_mul x y
  norm_coord _ _ := rfl
  dense c _ hε := ⟨0, c, StarSubalgebra.mem_top, by rw [sub_self, norm_zero]; exact hε.le⟩
  shift _ := StarAlgHom.id ℂ ℂ
  shift_coord _ _ _ := rfl
  shift_add _ _ _ := rfl
  shift_zero _ := rfl

variable {Z C : Type*} [CStarAlgebra Z] [CStarAlgebra C] (S : ShiftModel Z C)

theorem commute_coord {k l : ℤ} (hkl : k ≠ l) (x y : Z) :
    Commute (S.coord k x) (S.coord l y) :=
  S.commute_of_disjoint (Set.disjoint_singleton.2 hkl) _ (S.coord_mem k x) _ (S.coord_mem l y)

include S in
theorem nontrivial_of_norm_eq_one {z : Z} (hz : ‖z‖ = 1) : Nontrivial C :=
  ⟨⟨S.coord 0 z, 0, fun h0 => by
    have h := S.norm_coord 0 z
    rw [h0, norm_zero, hz] at h
    exact zero_ne_one h⟩⟩

/-- `hprod z a m = z_a · z_{a+1} ⋯ z_{a+m-1}`. -/
def hprod (z : Z) : ℤ → ℕ → C
  | _, 0 => 1
  | a, m + 1 => S.coord a z * hprod z (a + 1) m

theorem hprod_zero (z : Z) (a : ℤ) : S.hprod z a 0 = 1 := rfl

theorem hprod_succ (z : Z) (a : ℤ) (m : ℕ) :
    S.hprod z a (m + 1) = S.coord a z * S.hprod z (a + 1) m := rfl

theorem hprod_mem (z : Z) (a : ℤ) (m : ℕ) : S.hprod z a m ∈ S.block (Set.Ici a) := by
  induction m generalizing a with
  | zero => rw [S.hprod_zero]; exact one_mem _
  | succ m ih =>
    rw [S.hprod_succ]
    refine mul_mem (S.block_mono ?_ _ (S.coord_mem a z)) (S.block_mono ?_ _ (ih (a + 1)))
    · intro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [Set.mem_Ici]
      omega
    · intro x hx
      rw [Set.mem_Ici] at hx ⊢
      omega

theorem norm_hprod {z : Z} (hz : ‖z‖ = 1) (a : ℤ) (m : ℕ) : ‖S.hprod z a m‖ = 1 := by
  haveI := S.nontrivial_of_norm_eq_one hz
  induction m generalizing a with
  | zero => rw [S.hprod_zero, norm_one]
  | succ m ih =>
    rw [S.hprod_succ, S.norm_mul_of_disjoint (disjoint_singleton_Ici a) _ (S.coord_mem a z) _
      (S.hprod_mem z (a + 1) m), S.norm_coord, hz, ih, one_mul]

/-- Any factor of `hprod z a m` can be moved to the front. -/
theorem hprod_eq_coord_mul (z : Z) (a : ℤ) (i m : ℕ) (hi : i < m) :
    ∃ X : C, S.hprod z a m = S.coord (a + i) z * X := by
  induction m generalizing a i with
  | zero => exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    cases i with
    | zero => exact ⟨S.hprod z (a + 1) m, by simp only [S.hprod_succ, Nat.cast_zero, add_zero]⟩
    | succ i =>
      obtain ⟨X, hX⟩ := ih (a + 1) i (by omega)
      have hk : a + ((i + 1 : ℕ) : ℤ) = a + 1 + i := by push_cast; ring
      have hne : a ≠ a + 1 + i := by omega
      refine ⟨S.coord a z * X, ?_⟩
      rw [S.hprod_succ, hX, hk]
      exact (S.commute_coord hne z z).left_comm X

theorem coord_mul_hprod_mem (g h : Z) (j : ℤ) (N : ℕ) :
    S.coord j g * S.hprod h (j + 1) N ∈ S.block (Set.Ici j) := by
  refine mul_mem (S.block_mono ?_ _ (S.coord_mem j g))
    (S.block_mono ?_ _ (S.hprod_mem h (j + 1) N))
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [Set.mem_Ici]
    omega
  · intro x hx
    rw [Set.mem_Ici] at hx ⊢
    omega

theorem norm_coord_mul_hprod {g h : Z} (hg : ‖g‖ = 1) (hh : ‖h‖ = 1) (j : ℤ) (N : ℕ) :
    ‖S.coord j g * S.hprod h (j + 1) N‖ = 1 := by
  rw [S.norm_mul_of_disjoint (disjoint_singleton_Ici j) _ (S.coord_mem j g) _
    (S.hprod_mem h (j + 1) N), S.norm_coord, hg, S.norm_hprod hh, one_mul]

theorem star_coord_mul_mul_coord_mul (k : ℤ) (x y : Z) (X Y : C) :
    star (S.coord k x * X) * (S.coord k y * Y) = star X * S.coord k (star x * y) * Y := by
  simp only [star_mul, map_mul, map_star, mul_assoc]

/-- **Orthogonality under the shift.** `F⋆ · shift (i+1) F = 0` for
`F = g_j · h_{j+1} ⋯ h_{j+N}`, `i < N` and `h⋆g = 0`. -/
theorem star_mul_shift_eq_zero {g h : Z} (hhg : star h * g = 0) (j : ℤ) (N i : ℕ) (hi : i < N) :
    star (S.coord j g * S.hprod h (j + 1) N) *
      S.shift ((i : ℤ) + 1) (S.coord j g * S.hprod h (j + 1) N) = 0 := by
  obtain ⟨X, hX⟩ := S.hprod_eq_coord_mul h (j + 1) i N hi
  have hne : j ≠ j + 1 + i := by omega
  have hF : S.coord j g * S.hprod h (j + 1) N = S.coord (j + 1 + i) h * (S.coord j g * X) := by
    rw [hX]; exact (S.commute_coord hne g h).left_comm X
  have hk : j + ((i : ℤ) + 1) = j + 1 + i := by ring
  rw [map_mul, S.shift_coord, hk, hF, S.star_coord_mul_mul_coord_mul, hhg, map_zero, mul_zero,
    zero_mul]

/-- Orthogonality under `shift m` gives orthogonality under `shift (-m)`. -/
theorem star_mul_shift_neg {F : C} {m : ℤ} (hF : star F * S.shift m F = 0) :
    star F * S.shift (-m) F = 0 := by
  have h : S.shift (-m) (star (star F * S.shift m F)) = star F * S.shift (-m) F := by
    rw [star_mul, star_star, map_mul, map_star, S.shift_add, neg_add_cancel, S.shift_zero]
  rw [← h, hF, star_zero, map_zero]

end ShiftModel

end XCVWitness
end GroupApproximation
