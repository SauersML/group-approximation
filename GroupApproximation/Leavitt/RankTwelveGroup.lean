import GroupApproximation.Leavitt.RankTwelveCompressor
import GroupApproximation.Leavitt.ElementaryRoots

/-!
# The rank-twelve Leavitt self-compression: the group layer

`non_mf_groups_exist.tex`, Section `The binary Leavitt self-compression`.
`Leavitt.RankTwelveCompressor` carries out the block calculations over an
arbitrary ring `A` with a `LeavittFamily`; this module turns them into
statements about the elementary group `EL₁₂(A)`.

The twelve coordinates are the nested index type

`Idx = (Fin 2 × Fin 2) × Fin 3`,   `((a, b), c) ↦ 6a + 3b + c`,

so `Matrix Idx Idx A` is the flattening of `Full A = M₂(M₂(M₃(A)))`.  The
Kazhdan corner of the manuscript is the set of coordinates `((0, 0), ·)`.

What is proved here:

* `tauUnit_eq_six_elementary`, `tauUnit_mem` — the printed Whitehead
  factorization `eq:whitehead-factorization` exhibits `τ` as a product of six
  block transvections, hence `τ ∈ EL₂(M₆(A))`;
* `flatten` — the flattening isomorphism `EL₂(M₆(A)) ≃* EL₁₂(A)`, obtained by
  applying `elementaryBlockEquiv` twice, and `tauTwelve`, the image of `τ`;
* `cornerSubgroup` — the manuscript's `L = EL₃(A) ≤ H = EL₁₂(A)`, together
  with `cornerEquiv : EL₃(A) ≃* cornerSubgroup A`;
* `tauTwelve_conj_cornerRoot` — `eq:corner-conjugation` on generators, i.e.
  `τ e_{ij}(a) τ⁻¹ = e_{ij}(s₀ a t₀)` inside the corner;
* `tauTwelve_compresses_corner` — the containment `eq:compresses-L`,
  `τ L τ⁻¹ ≤ L`.

Nothing here is specific to the binary Leavitt algebra: only the
`LeavittFamily` relations are used.
-/

namespace GroupApproximation
namespace RankTwelve

variable {A : Type*} [Ring A]

/-! ## The twelve flat coordinates -/

/-- The manuscript's index set `{0, …, 11}`, carried as the nested type
`(Fin 2 × Fin 2) × Fin 3`. -/
abbrev Idx : Type := (Fin 2 × Fin 2) × Fin 3

/-- The Kazhdan corner `{0, 1, 2}` inside the twelve coordinates. -/
def cornerIndex (i : Fin 3) : Idx := ((0, 0), i)

theorem cornerIndex_injective : Function.Injective cornerIndex := by
  intro i j h
  exact congrArg Prod.snd h

/-! ## The block transvections of the Whitehead factorization -/

theorem upperNe : (0 : Fin 2) ≠ 1 := by decide

theorem lowerNe : (1 : Fin 2) ≠ 0 := by decide

/-- The upper block-unipotent of `eq:whitehead-factorization` is the
elementary matrix `x_{01}(N)` of `M₂(M₆(A))`. -/
theorem upperUnit_val (N : Half A) :
    ((elementaryUnit (0 : Fin 2) 1 upperNe N : (Full A)ˣ) : Full A) =
      upperBlock N := by
  show (1 : Full A) + Matrix.single (0 : Fin 2) 1 N = upperBlock N
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [upperBlock, Matrix.single, Matrix.one_apply]

/-- The lower block-unipotent of `eq:whitehead-factorization` is the
elementary matrix `x_{10}(N)` of `M₂(M₆(A))`. -/
theorem lowerUnit_val (N : Half A) :
    ((elementaryUnit (1 : Fin 2) 0 lowerNe N : (Full A)ˣ) : Full A) =
      lowerBlock N := by
  show (1 : Full A) + Matrix.single (1 : Fin 2) 0 N = lowerBlock N
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [lowerBlock, Matrix.single, Matrix.one_apply]

/-- **`eq:whitehead-factorization` as a word in transvections.**  The
compressor `τ = diag(X, Y)` is the printed product of six elementary matrices
of `M₂(M₆(A))`. -/
theorem tauUnit_eq_six_elementary (L : LeavittFamily A) :
    tauUnit L =
      elementaryUnit (0 : Fin 2) 1 upperNe (shift L) *
        elementaryUnit (1 : Fin 2) 0 lowerNe (-(shiftInv L)) *
        elementaryUnit (0 : Fin 2) 1 upperNe (shift L) *
        elementaryUnit (1 : Fin 2) 0 lowerNe 1 *
        elementaryUnit (0 : Fin 2) 1 upperNe (-1) *
        elementaryUnit (1 : Fin 2) 0 lowerNe 1 := by
  apply Units.ext
  rw [tauUnit_val, tau_eq_whitehead_product L]
  simp only [Units.val_mul, upperUnit_val, lowerUnit_val]

/-- **`τ ∈ EL₁₂`, in block form.** -/
theorem tauUnit_mem (L : LeavittFamily A) :
    tauUnit L ∈ elementaryGroup (Fin 2) (Half A) := by
  rw [tauUnit_eq_six_elementary]
  exact mul_mem (mul_mem (mul_mem (mul_mem (mul_mem
    (elementaryUnit_mem _ _ upperNe (shift L))
    (elementaryUnit_mem _ _ lowerNe (-(shiftInv L))))
    (elementaryUnit_mem _ _ upperNe (shift L)))
    (elementaryUnit_mem _ _ lowerNe 1))
    (elementaryUnit_mem _ _ upperNe (-1)))
    (elementaryUnit_mem _ _ lowerNe 1)

/-! ## Flattening `M₂(M₂(M₃(A)))` to `M₁₂(A)` -/

private theorem finTwoNontrivial : Nontrivial (Fin 2) := ⟨0, 1, by decide⟩

private theorem prodNontrivial : Nontrivial (Fin 2 × Fin 2) :=
  ⟨(0, 0), (1, 0), by decide⟩

/-- The flattening isomorphism of unit groups
`M₂(M₂(M₃(A)))ˣ ≃* M₁₂(A)ˣ`, applied one block level at a time. -/
def flattenUnit (A : Type*) [Ring A] : (Full A)ˣ ≃* (Matrix Idx Idx A)ˣ :=
  (elementaryBlockUnitEquiv (ι := Fin 2) (κ := Fin 2) (R := Cell A)).trans
    (elementaryBlockUnitEquiv (ι := Fin 2 × Fin 2) (κ := Fin 3) (R := A))

theorem flattenUnit_toMonoidHom (A : Type*) [Ring A] :
    (flattenUnit A).toMonoidHom =
      (elementaryBlockUnitEquiv (ι := Fin 2 × Fin 2) (κ := Fin 3)
          (R := A)).toMonoidHom.comp
        (elementaryBlockUnitEquiv (ι := Fin 2) (κ := Fin 2)
          (R := Cell A)).toMonoidHom :=
  MonoidHom.ext fun _ ↦ rfl

/-- Flattening carries `EL₂(M₆(A))` exactly onto `EL₁₂(A)`. -/
theorem flattenUnit_map (A : Type*) [Ring A] :
    (elementaryGroup (Fin 2) (Half A)).map (flattenUnit A).toMonoidHom =
      elementaryGroup Idx A := by
  haveI := finTwoNontrivial
  haveI := prodNontrivial
  rw [flattenUnit_toMonoidHom, ← Subgroup.map_map,
    elementaryBlockGroup_map (ι := Fin 2) (κ := Fin 2) (R := Cell A),
    elementaryBlockGroup_map (ι := Fin 2 × Fin 2) (κ := Fin 3) (R := A)]

/-- **The flattening `EL₂(M₆(A)) ≃* EL₁₂(A)`.** -/
def flatten (A : Type*) [Ring A] :
    elementaryGroup (Fin 2) (Half A) ≃* elementaryGroup Idx A :=
  ((flattenUnit A).subgroupMap (elementaryGroup (Fin 2) (Half A))).trans
    (MulEquiv.subgroupCongr (flattenUnit_map A))

/-- The compressor `τ`, flattened to a `12 × 12` unit. -/
def tauTwelveUnit (L : LeavittFamily A) : (Matrix Idx Idx A)ˣ :=
  flattenUnit A (tauUnit L)

theorem tauTwelveUnit_mem (L : LeavittFamily A) :
    tauTwelveUnit L ∈ elementaryGroup Idx A := by
  rw [← flattenUnit_map A]
  exact ⟨tauUnit L, tauUnit_mem L, rfl⟩

/-- **The compressor `τ` as an element of `H = EL₁₂(A)`.** -/
def tauTwelve (L : LeavittFamily A) : elementaryGroup Idx A :=
  ⟨tauTwelveUnit L, tauTwelveUnit_mem L⟩

theorem flatten_tauUnit (L : LeavittFamily A) :
    flatten A ⟨tauUnit L, tauUnit_mem L⟩ = tauTwelve L :=
  Subtype.ext rfl

/-! ## The Kazhdan corner as a subgroup of `EL₁₂(A)` -/

/-- `diag(A, I₉)` on units. -/
def fullCornerHom (A : Type*) [Ring A] : Cell A →* Full A where
  toFun := fullCorner
  map_one' := fullCorner_one
  map_mul' M N := (fullCorner_mul M N).symm

/-- The corner embedding on unit groups, `M₃(A)ˣ → M₁₂(A)ˣ` in block form. -/
def fullCornerUnits (A : Type*) [Ring A] : (Cell A)ˣ →* (Full A)ˣ :=
  Units.map (fullCornerHom A)

@[simp] theorem fullCornerUnits_val (u : (Cell A)ˣ) :
    ((fullCornerUnits A u : (Full A)ˣ) : Full A) = fullCorner (u : Cell A) :=
  rfl

/-- The corner embedding on unit groups, in flat coordinates. -/
def flatCornerUnits (A : Type*) [Ring A] :
    (Cell A)ˣ →* (Matrix Idx Idx A)ˣ :=
  (flattenUnit A).toMonoidHom.comp (fullCornerUnits A)

/-! ### The corner of an elementary matrix is an elementary matrix -/

theorem cornerBlock_add_single {B : Type*} [Ring B] (N : B) :
    (!![1 + N, 0; 0, 1] : Matrix (Fin 2) (Fin 2) B) =
      1 + Matrix.single (0 : Fin 2) 0 N := by
  ext r c
  fin_cases r <;> fin_cases c <;>
    simp [Matrix.single, Matrix.one_apply]

theorem halfCorner_add_single (N : Cell A) :
    halfCorner (1 + N) = 1 + Matrix.single (0 : Fin 2) 0 N :=
  cornerBlock_add_single N

theorem fullCorner_add_single (N : Cell A) :
    fullCorner (1 + N) =
      1 + Matrix.single (0 : Fin 2) 0 (Matrix.single (0 : Fin 2) 0 N) := by
  have h1 : fullCorner (1 + N) = !![halfCorner (1 + N), 0; 0, 1] := rfl
  rw [h1, halfCorner_add_single]
  exact cornerBlock_add_single (Matrix.single (0 : Fin 2) 0 N)

/-- The flattened corner of `x_{ij}(a)` is the flat elementary matrix
`x_{((0,0),i),((0,0),j)}(a)`. -/
theorem flattenUnit_fullCornerUnits_elementaryUnit
    (i j : Fin 3) (hij : i ≠ j) (a : A) :
    flattenUnit A (fullCornerUnits A (elementaryUnit i j hij a)) =
      elementaryUnit (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a := by
  apply Units.ext
  show Matrix.compRingEquiv (Fin 2 × Fin 2) (Fin 3) A
      (Matrix.compRingEquiv (Fin 2) (Fin 2) (Cell A)
        (fullCorner ((1 : Cell A) + Matrix.single i j a))) =
    1 + Matrix.single (cornerIndex i) (cornerIndex j) a
  rw [fullCorner_add_single, map_add, map_one,
    show (Matrix.compRingEquiv (Fin 2) (Fin 2) (Cell A))
        (Matrix.single (0 : Fin 2) 0
          (Matrix.single (0 : Fin 2) 0 (Matrix.single i j a))) =
      Matrix.single ((0 : Fin 2), (0 : Fin 2)) ((0 : Fin 2), (0 : Fin 2))
        (Matrix.single i j a) from Matrix.comp_single_single _ _ _ _ _,
    map_add, map_one,
    show (Matrix.compRingEquiv (Fin 2 × Fin 2) (Fin 3) A)
        (Matrix.single ((0 : Fin 2), (0 : Fin 2))
          ((0 : Fin 2), (0 : Fin 2)) (Matrix.single i j a)) =
      Matrix.single (cornerIndex i) (cornerIndex j) a from
        Matrix.comp_single_single _ _ _ _ _]

theorem flatCornerUnits_elementaryUnit (i j : Fin 3) (hij : i ≠ j) (a : A) :
    flatCornerUnits A (elementaryUnit i j hij a) =
      elementaryUnit (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a :=
  flattenUnit_fullCornerUnits_elementaryUnit i j hij a

theorem flatCornerUnits_mem_elementary (g : (Cell A)ˣ)
    (hg : g ∈ elementaryGroup (Fin 3) A) :
    flatCornerUnits A g ∈ elementaryGroup Idx A := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [flatCornerUnits_elementaryUnit]
      exact elementaryUnit_mem _ _ _ _
  | one => simp
  | mul x y _ _ hx hy => simpa using (elementaryGroup Idx A).mul_mem hx hy
  | inv x _ hx => simpa using (elementaryGroup Idx A).inv_mem hx

/-- **The manuscript's `EL₃(A) ≤ EL₁₂(A)`**, as a homomorphism. -/
def cornerEmbedding (A : Type*) [Ring A] :
    elementaryGroup (Fin 3) A →* elementaryGroup Idx A :=
  ((flatCornerUnits A).comp (elementaryGroup (Fin 3) A).subtype).codRestrict
    (elementaryGroup Idx A) fun g ↦
      flatCornerUnits_mem_elementary (g : (Cell A)ˣ) g.property

@[simp] theorem cornerEmbedding_elementaryRoot
    (i j : Fin 3) (hij : i ≠ j) (a : A) :
    cornerEmbedding A (elementaryRoot i j hij a) =
      elementaryRoot (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a :=
  Subtype.ext (flatCornerUnits_elementaryUnit i j hij a)

/-- The generating set of the Kazhdan corner: elementary matrices with both
indices in `{((0,0), i)}`. -/
def cornerRootSet (A : Type*) [Ring A] : Set (elementaryGroup Idx A) :=
  {x | ∃ (i j : Fin 3) (hij : i ≠ j) (a : A),
    elementaryRoot (cornerIndex i) (cornerIndex j)
      (cornerIndex_injective.ne hij) a = x}

/-- **The manuscript's `L = EL₃(R) ≤ H`.** -/
def cornerSubgroup (A : Type*) [Ring A] : Subgroup (elementaryGroup Idx A) :=
  Subgroup.closure (cornerRootSet A)

theorem cornerRoot_mem (i j : Fin 3) (hij : i ≠ j) (a : A) :
    elementaryRoot (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a ∈ cornerSubgroup A :=
  Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩

/-! ### The corner is a copy of `EL₃(A)` -/

theorem fullCorner_injective (A : Type*) [Ring A] :
    Function.Injective (fullCorner (A := A)) := by
  intro M N h
  have h1 : (fullCorner M) 0 0 = (fullCorner N) 0 0 := by rw [h]
  have h2 : halfCorner M = halfCorner N := by
    simpa [fullCorner] using h1
  have h3 : (halfCorner M) 0 0 = (halfCorner N) 0 0 := by rw [h2]
  simpa [halfCorner] using h3

theorem fullCornerUnits_injective (A : Type*) [Ring A] :
    Function.Injective (fullCornerUnits A) := by
  intro u v h
  have h' : fullCorner (u : Cell A) = fullCorner (v : Cell A) :=
    congrArg Units.val h
  exact Units.ext (fullCorner_injective A h')

theorem flatCornerUnits_injective (A : Type*) [Ring A] :
    Function.Injective (flatCornerUnits A) := by
  intro u v h
  have h' : flattenUnit A (fullCornerUnits A u) =
      flattenUnit A (fullCornerUnits A v) := h
  exact fullCornerUnits_injective A ((flattenUnit A).injective h')

theorem cornerEmbedding_injective (A : Type*) [Ring A] :
    Function.Injective (cornerEmbedding A) := by
  intro x y h
  have h' : flatCornerUnits A (x : (Cell A)ˣ) =
      flatCornerUnits A (y : (Cell A)ˣ) := congrArg Subtype.val h
  exact Subtype.ext (flatCornerUnits_injective A h')

theorem cornerEmbedding_range (A : Type*) [Ring A] :
    (cornerEmbedding A).range = cornerSubgroup A := by
  apply le_antisymm
  · rintro x ⟨g, rfl⟩
    obtain ⟨g, hg⟩ := g
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨i, j, hij, a, rfl⟩ := hy
        have hmem := cornerRoot_mem (A := A) i j hij a
        rwa [← cornerEmbedding_elementaryRoot i j hij a] at hmem
    | one =>
        rw [show (⟨1, _⟩ : elementaryGroup (Fin 3) A) = 1 from Subtype.ext rfl,
          map_one]
        exact (cornerSubgroup A).one_mem
    | mul x y hxmem hymem hx hy =>
        rw [show (⟨x * y, _⟩ : elementaryGroup (Fin 3) A) =
            (⟨x, hxmem⟩ : elementaryGroup (Fin 3) A) * ⟨y, hymem⟩ from
          Subtype.ext rfl, map_mul]
        exact (cornerSubgroup A).mul_mem hx hy
    | inv x hxmem hx =>
        rw [show (⟨x⁻¹, _⟩ : elementaryGroup (Fin 3) A) =
            (⟨x, hxmem⟩ : elementaryGroup (Fin 3) A)⁻¹ from
          Subtype.ext rfl, map_inv]
        exact (cornerSubgroup A).inv_mem hx
  · rw [cornerSubgroup, Subgroup.closure_le]
    rintro x ⟨i, j, hij, a, rfl⟩
    exact ⟨elementaryRoot i j hij a, cornerEmbedding_elementaryRoot i j hij a⟩

/-- The corner embedding, corestricted to the corner. -/
def cornerEmbeddingToCorner (A : Type*) [Ring A] :
    elementaryGroup (Fin 3) A →* cornerSubgroup A :=
  (cornerEmbedding A).codRestrict (cornerSubgroup A) fun g ↦ by
    rw [← cornerEmbedding_range]
    exact ⟨g, rfl⟩

theorem cornerEmbeddingToCorner_surjective (A : Type*) [Ring A] :
    Function.Surjective (cornerEmbeddingToCorner A) := by
  intro x
  have hx : (x : elementaryGroup Idx A) ∈ (cornerEmbedding A).range := by
    rw [cornerEmbedding_range]
    exact x.property
  obtain ⟨g, hg⟩ := hx
  exact ⟨g, Subtype.ext hg⟩

theorem cornerEmbeddingToCorner_injective (A : Type*) [Ring A] :
    Function.Injective (cornerEmbeddingToCorner A) := by
  intro x y h
  have h' : cornerEmbedding A x = cornerEmbedding A y := congrArg Subtype.val h
  exact cornerEmbedding_injective A h'

/-- **The Kazhdan corner is a copy of `EL₃(A)`.** -/
noncomputable def cornerEquiv (A : Type*) [Ring A] :
    elementaryGroup (Fin 3) A ≃* cornerSubgroup A :=
  MulEquiv.ofBijective (cornerEmbeddingToCorner A)
    ⟨cornerEmbeddingToCorner_injective A, cornerEmbeddingToCorner_surjective A⟩

/-! ### The corner is nontrivial -/

theorem cornerRoot_ne_one [Nontrivial A] (i j : Fin 3) (hij : i ≠ j) :
    elementaryRoot (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) (1 : A) ≠ 1 := by
  intro h
  have hval : elementaryUnit (cornerIndex i) (cornerIndex j)
      (cornerIndex_injective.ne hij) (1 : A) = 1 := congrArg Subtype.val h
  rw [← elementaryUnit_zero (R := A) (cornerIndex i) (cornerIndex j)
    (cornerIndex_injective.ne hij)] at hval
  exact one_ne_zero (elementaryUnit_injective _ _ _ hval)

theorem cornerSubgroup_ne_bot (A : Type*) [Ring A] [Nontrivial A] :
    cornerSubgroup A ≠ ⊥ := by
  intro h
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hmem := cornerRoot_mem (A := A) 0 1 h01 1
  rw [h, Subgroup.mem_bot] at hmem
  exact cornerRoot_ne_one 0 1 h01 hmem

/-! ## `eq:corner-conjugation` and `eq:compresses-L` in the group -/

/-- **`eq:corner-conjugation` on units.** -/
theorem tauUnit_conj_fullCornerUnits (L : LeavittFamily A) (u : (Cell A)ˣ) :
    tauUnit L * fullCornerUnits A u * (tauUnit L)⁻¹ =
      fullCornerUnits A (L.matrixCompressionHom u) :=
  Units.ext (tau_fullCorner_tauInv L (u : Cell A))

/-- Conjugating a flat corner transvection by `τ` compresses its
coefficient, `Ψ(e_{ij}(a)) = e_{ij}(s₀ a t₀)`. -/
theorem tauTwelveUnit_conj_elementaryUnit (L : LeavittFamily A)
    (i j : Fin 3) (hij : i ≠ j) (a : A) :
    tauTwelveUnit L * elementaryUnit (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a * (tauTwelveUnit L)⁻¹ =
      elementaryUnit (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) (L.s0 * a * L.t0) := by
  have hraw := tauUnit_conj_fullCornerUnits L (elementaryUnit i j hij a)
  rw [LeavittFamily.matrixCompression_elementaryUnit] at hraw
  have hmapped := congrArg (flattenUnit A) hraw
  rw [map_mul, map_mul, map_inv,
    flattenUnit_fullCornerUnits_elementaryUnit,
    flattenUnit_fullCornerUnits_elementaryUnit] at hmapped
  exact hmapped

/-- **`eq:corner-conjugation` on the generators of the corner.** -/
theorem tauTwelve_conj_cornerRoot (L : LeavittFamily A)
    (i j : Fin 3) (hij : i ≠ j) (a : A) :
    tauTwelve L * elementaryRoot (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) a * (tauTwelve L)⁻¹ =
      elementaryRoot (cornerIndex i) (cornerIndex j)
        (cornerIndex_injective.ne hij) (L.s0 * a * L.t0) :=
  Subtype.ext (tauTwelveUnit_conj_elementaryUnit L i j hij a)

/-- **`eq:compresses-L`.**  Conjugation by the flattened compressor `τ` maps
the whole Kazhdan corner into itself. -/
theorem tauTwelve_compresses_corner (L : LeavittFamily A) :
    ∀ g ∈ cornerSubgroup A,
      tauTwelve L * g * (tauTwelve L)⁻¹ ∈ cornerSubgroup A := by
  intro g hg
  rw [cornerSubgroup] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, j, hij, a, rfl⟩ := hx
      rw [tauTwelve_conj_cornerRoot L i j hij a]
      exact cornerRoot_mem i j hij (L.s0 * a * L.t0)
  | one => simp
  | mul x y _ _ hx hy =>
      rw [show tauTwelve L * (x * y) * (tauTwelve L)⁻¹ =
          (tauTwelve L * x * (tauTwelve L)⁻¹) *
            (tauTwelve L * y * (tauTwelve L)⁻¹) by group]
      exact (cornerSubgroup A).mul_mem hx hy
  | inv x _ hx =>
      rw [show tauTwelve L * x⁻¹ * (tauTwelve L)⁻¹ =
          (tauTwelve L * x * (tauTwelve L)⁻¹)⁻¹ by group]
      exact (cornerSubgroup A).inv_mem hx

end RankTwelve
end GroupApproximation
