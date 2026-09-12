import GroupApproximation.KOne.AlgebraicKOne

/-!
# Morita invariance of `K₁`: `K_1(M_n(R)) ≅ K_1(R)` for every ring and every `n ≥ 1`

`non_mf_groups_exist.tex`, line 1182--1184, the first sentence of the proof of
`thm:mf-quotient-units`:

> The ring `M_n(R)` is again countable, purely infinite, and
> simple~\cite[Corollary~1.7]{AGP}, and `K_1(M_n(R)) ≅ K_1(R)` by
> Morita invariance, so it suffices to treat `n=1`.

`Manuscript/OneSidedMFRadical/MFQuotientUnitsKOne.lean` states the second clause
as the hypothesis `MoritaKOne` and does not prove it; `KOne/AlgebraicKOneFunctor.lean`
closes only the self-similar case `R ≅ M_n(R)`, which is functoriality of `K₁`
for a ring isomorphism and says nothing about a general ring.  This module
proves the general statement.

## The proof

`K₁(S) = GL(S)/E_∞(S)` with `GL(S) = colim_m GL_m(S)` along `A ↦ diag(A,1)`, so
Morita invariance is a statement about the two colimits.  Three ingredients:

* **Flattening.**  `blockFlatUnitEquiv R n m : GL_m(M_n(R)) ≅ GL_{mn}(R)` is the
  block composition `M_m(M_n(R)) ≅ M_{m×n}(R)` of `Leavitt/ElementaryGroup.lean`
  followed by the reindexing along `finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)`,
  `(i,a) ↦ a + n*i`.  Both halves already carry elementary subgroups.
* **Compatibility with the transitions.**  `blockFlatten_stabMatrix`: flattening
  the padding is the padding of the flattening.  This is the one genuine
  computation, and it is where the *order* of `finProdFinEquiv` matters: with
  `(i,a) ↦ a + n*i` the first `m*n` indices of `Fin (m'*n)` are exactly the
  flattened `m × m` corner, so `padEntry`'s `< m` test on block indices and its
  `< m*n` test on flat indices agree (`blockIndex_lt_iff`).
* **Cofinality.**  `m ↦ m*n` is monotone and, for `n ≥ 1`, cofinal in `ℕ`; the
  two induced maps of colimits (`moritaGLHom`, built from the flattenings, and
  `moritaGLInvFun`, built from the inverse flattenings after padding `p` to
  `p*n`) are mutually inverse by the same compatibility, so
  `moritaGLEquiv : GL(M_n(R)) ≅ GL(R)`.

The elementary subgroups then correspond on the nose
(`moritaGLEquiv_elementaryColim`): `E_m(M_n(R))` maps *onto* `E_{mn}(R)` for
`m ≥ 2` by `elementaryBlockGroup_map`, whose reverse inclusion is the Whitehead
two-step identity `x_{ik}(a) = ⁅x_{ij}(a), x_{jk}(1)⁆` applied inside a fixed
diagonal block, and every elementary matrix at a rank `p` is elementary at rank
`m*n ≥ p` after padding (`glStab_elementaryGroup_le`).  Quotienting gives the
printed isomorphism.

## Naturality

`moritaKOneEquiv_kappa` records the direction the manuscript uses: composed with
the printed `κ : (M_n(R))^× → K_1(M_n(R))` -- that is, with the canonical map
out of `GL_n(R)`, since `(M_n(R))^× = GL_n(R)` -- the equivalence is the
canonical stabilization map `GL_n(R) → K_1(R)`.  So the reduction to `n = 1` in
the printed proof identifies the two comparison maps, not merely the two groups.

## What is not needed

No countability, no simplicity, no purely infinite hypothesis: Morita invariance
of `K₁` holds over an arbitrary unital ring.

## Note on overlap

`KOne/LeavittKOneStabElementary.lean`, written concurrently and in a different
namespace (`KOneDescent`), proves the same padding facts --- its
`stabMatrix_elementaryUnit` and `glStab_mem_elementaryGroup` are
`stabMatrix_one_add_single` and `glStab_elementaryGroup_le` here.  Neither module
imports the other, and each records the duplication rather than resolving it
silently; once both are on the tree either copy can be deleted in favour of the
other.
-/

namespace GroupApproximation
namespace AlgebraicK

/-! ### Rank arithmetic -/

theorem rank_mul_le_mul {m m' : ℕ} (h : m ≤ m') (n : ℕ) : m * n ≤ m' * n :=
  Nat.mul_le_mul h le_rfl

theorem rank_le_mul (m : ℕ) {n : ℕ} (hn : 1 ≤ n) : m ≤ m * n :=
  le_trans (le_of_eq (Nat.mul_one m).symm) (Nat.mul_le_mul le_rfl hn)

/-! ### The block index `Fin m × Fin n ≃ Fin (m * n)` -/

/-- The flat index of the block index pair `(i, a)` is `a + n * i`: the blocks
are consecutive runs of `n` indices, in order. -/
theorem val_finProdFinEquiv {p q : ℕ} (i : Fin p) (a : Fin q) :
    ((finProdFinEquiv (i, a) : Fin (p * q)) : ℕ) = (a : ℕ) + q * (i : ℕ) := rfl

/-- **The corner test transfers**: a flat index lies below `m * q` exactly when
its block index lies below `m`.  This is what makes the flattening commute with
the padding. -/
theorem blockIndex_lt_iff {p q : ℕ} (m : ℕ) (i : Fin p) (a : Fin q) :
    (a : ℕ) + q * (i : ℕ) < m * q ↔ (i : ℕ) < m := by
  constructor
  · intro hlt
    by_contra hge
    have hmi : m ≤ (i : ℕ) := Nat.le_of_not_lt hge
    have h1 : q * m ≤ q * (i : ℕ) := Nat.mul_le_mul le_rfl hmi
    have h2 : q * (i : ℕ) < m * q := lt_of_le_of_lt (Nat.le_add_left _ _) hlt
    rw [Nat.mul_comm m q] at h2
    exact absurd (lt_of_lt_of_le h2 h1) (lt_irrefl _)
  · intro hlt
    have h1 : (i : ℕ) + 1 ≤ m := hlt
    calc (a : ℕ) + q * (i : ℕ) < q + q * (i : ℕ) := Nat.add_lt_add_right a.isLt _
      _ = q * ((i : ℕ) + 1) := by ring
      _ ≤ q * m := Nat.mul_le_mul le_rfl h1
      _ = m * q := Nat.mul_comm q m

noncomputable section

/-! ### The flattening `M_m(M_n(R)) → M_{mn}(R)` -/

section Flatten

variable {R : Type*} [Ring R]

/-- The block flattening of an `m × m` matrix of `n × n` blocks, as an
`mn × mn` matrix: block composition followed by the reindexing
`(i, a) ↦ a + n * i`. -/
def blockFlatten (n : ℕ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R)) :
    Matrix (Fin (m * n)) (Fin (m * n)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.comp (Fin m) (Fin m) (Fin n) (Fin n) R A)

omit [Ring R] in
theorem blockFlatten_apply {n m : ℕ}
    (A : Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R)) (i j : Fin m)
    (a b : Fin n) :
    blockFlatten n A (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b))
      = A i j a b := by
  show Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.comp (Fin m) (Fin m) (Fin n) (Fin n) R A)
      (finProdFinEquiv (i, a)) (finProdFinEquiv (j, b)) = A i j a b
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Matrix.comp_apply]

/-- **The flattening commutes with the padding.**  Padding an `m × m` block
matrix to `m' × m'` blocks and flattening is flattening and padding from rank
`m * n` to rank `m' * n`: the block picture at index pairs and the `padEntry`
picture at natural numbers describe the same matrix.

No inequality between `m` and `m'` is needed: for `m' < m` both sides truncate
the same corner. -/
theorem blockFlatten_stabMatrix {n m m' : ℕ}
    (A : Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R)) :
    blockFlatten n (stabMatrix m' A) = stabMatrix (m' * n) (blockFlatten n A) := by
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective y
  rw [blockFlatten_apply, stabMatrix_apply, stabMatrix_apply, val_finProdFinEquiv,
    val_finProdFinEquiv]
  by_cases hi : (i : ℕ) < m
  · have hx : (a : ℕ) + n * (i : ℕ) < m * n := (blockIndex_lt_iff m i a).mpr hi
    by_cases hj : (j : ℕ) < m
    · have hy : (b : ℕ) + n * (j : ℕ) < m * n := (blockIndex_lt_iff m j b).mpr hj
      have hxe : (⟨(a : ℕ) + n * (i : ℕ), hx⟩ : Fin (m * n))
          = finProdFinEquiv ((⟨(i : ℕ), hi⟩ : Fin m), a) :=
        Fin.ext (by rw [val_finProdFinEquiv])
      have hye : (⟨(b : ℕ) + n * (j : ℕ), hy⟩ : Fin (m * n))
          = finProdFinEquiv ((⟨(j : ℕ), hj⟩ : Fin m), b) :=
        Fin.ext (by rw [val_finProdFinEquiv])
      rw [padEntry_of_lt_lt A hi hj, padEntry_of_lt_lt (blockFlatten n A) hx hy,
        hxe, hye, blockFlatten_apply]
    · have hy : ¬ ((b : ℕ) + n * (j : ℕ) < m * n) := fun hc =>
        hj ((blockIndex_lt_iff m j b).mp hc)
      rw [padEntry_of_lt_ge A hi hj, padEntry_of_lt_ge (blockFlatten n A) hx hy,
        Matrix.zero_apply]
  · have hx : ¬ ((a : ℕ) + n * (i : ℕ) < m * n) := fun hc =>
      hi ((blockIndex_lt_iff m i a).mp hc)
    rw [padEntry_of_ge A hi, padEntry_of_ge (blockFlatten n A) hx]
    by_cases hij : (i : ℕ) = (j : ℕ)
    · rw [if_pos hij, Matrix.one_apply]
      by_cases hab : a = b
      · have heq : (a : ℕ) + n * (i : ℕ) = (b : ℕ) + n * (j : ℕ) := by
          rw [hij, hab]
        rw [if_pos hab, if_pos heq]
      · have hne : ¬ ((a : ℕ) + n * (i : ℕ) = (b : ℕ) + n * (j : ℕ)) := by
          intro hc
          rw [hij] at hc
          exact hab (Fin.ext (Nat.add_right_cancel hc))
        rw [if_neg hab, if_neg hne]
    · have hne : ¬ ((a : ℕ) + n * (i : ℕ) = (b : ℕ) + n * (j : ℕ)) := by
        intro hc
        have he : (finProdFinEquiv (i, a) : Fin (m' * n)) = finProdFinEquiv (j, b) :=
          Fin.ext (by rw [val_finProdFinEquiv, val_finProdFinEquiv]; exact hc)
        exact hij (congrArg (fun p : Fin m' × Fin n => ((p.1 : Fin m') : ℕ))
          (finProdFinEquiv.injective he))
      rw [if_neg hij, if_neg hne, Matrix.zero_apply]

end Flatten

/-! ### The flattening of general linear groups -/

/-- **The flattening `GL_m(M_n(R)) ≅ GL_{mn}(R)`.**  The `m = 2` case is
`StableWhitehead.twoBlockUnitEquiv`, assembled there at rank `n + n`; this is the
same construction at every rank, at `m * n`. -/
def blockFlatUnitEquiv (R : Type*) [Ring R] (n m : ℕ) :
    (Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R))ˣ ≃*
      (Matrix (Fin (m * n)) (Fin (m * n)) R)ˣ :=
  (elementaryBlockUnitEquiv (ι := Fin m) (κ := Fin n) (R := R)).trans
    (elementaryReindexUnitEquiv (R := R)
      (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)))

theorem blockFlatUnitEquiv_val {R : Type*} [Ring R] (n m : ℕ)
    (z : (Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R))ˣ) :
    ((blockFlatUnitEquiv R n m z : (Matrix (Fin (m * n)) (Fin (m * n)) R)ˣ) :
        Matrix (Fin (m * n)) (Fin (m * n)) R)
      = blockFlatten n
          (z : Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R)) := rfl

/-- **The flattening is a map of direct systems**: it carries the transition
`GL_m(M_n(R)) → GL_{m'}(M_n(R))` to the transition `GL_{mn}(R) → GL_{m'n}(R)`. -/
theorem blockFlatUnitEquiv_glStab (R : Type*) [Ring R] (n : ℕ) {m m' : ℕ}
    (h : m ≤ m') (h' : m * n ≤ m' * n)
    (z : (Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R))ˣ) :
    blockFlatUnitEquiv R n m' (glStab (Matrix (Fin n) (Fin n) R) m m' h z)
      = glStab R (m * n) (m' * n) h' (blockFlatUnitEquiv R n m z) := by
  apply Units.ext
  simp only [blockFlatUnitEquiv_val, glStab_val]
  exact blockFlatten_stabMatrix _

/-- The flattening carries elementary matrices to elementary matrices, at every
rank. -/
theorem blockFlatUnitEquiv_elementary_le (R : Type*) [Ring R] (n m : ℕ) :
    (elementaryGroup (Fin m) (Matrix (Fin n) (Fin n) R)).map
        (blockFlatUnitEquiv R n m).toMonoidHom
      ≤ elementaryGroup (Fin (m * n)) R := by
  have hblock : (elementaryGroup (Fin m) (Matrix (Fin n) (Fin n) R)).map
      (elementaryBlockUnitEquiv (ι := Fin m) (κ := Fin n) (R := R)).toMonoidHom
      ≤ elementaryGroup (Fin m × Fin n) R := by
    apply Subgroup.map_le_iff_le_comap.mpr
    change Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, M, rfl⟩
    exact elementaryBlockUnitEquiv_mem i j hij M
  have hcomp : (blockFlatUnitEquiv R n m).toMonoidHom
      = (elementaryReindexUnitEquiv (R := R)
            (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))).toMonoidHom.comp
          (elementaryBlockUnitEquiv (ι := Fin m) (κ := Fin n) (R := R)).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [hcomp, ← Subgroup.map_map]
  exact le_trans (Subgroup.map_mono hblock)
    (le_of_eq (elementaryReindexGroup_map (R := R) _))

/-- **The flattening carries `EL_m(M_n(R))` onto `EL_{mn}(R)`**, for `m ≥ 2`.

The reverse inclusion is the content: an elementary matrix of `M_{mn}(R)` whose
row and column lie in the *same* diagonal block is not the flattening of a
block-elementary matrix, and is reached instead by the Whitehead two-step
identity `x_{ik}(a) = ⁅x_{ij}(a), x_{jk}(1)⁆` through a second block -- which is
where `m ≥ 2` enters.  Both halves are `elementaryBlockGroup_map` of
`Leavitt/ElementaryGroup.lean`. -/
theorem blockFlatUnitEquiv_elementary_map (R : Type*) [Ring R] (n : ℕ) {m : ℕ}
    (hm : 2 ≤ m) :
    (elementaryGroup (Fin m) (Matrix (Fin n) (Fin n) R)).map
        (blockFlatUnitEquiv R n m).toMonoidHom
      = elementaryGroup (Fin (m * n)) R := by
  haveI : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have hcomp : (blockFlatUnitEquiv R n m).toMonoidHom
      = (elementaryReindexUnitEquiv (R := R)
            (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))).toMonoidHom.comp
          (elementaryBlockUnitEquiv (ι := Fin m) (κ := Fin n) (R := R)).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [hcomp, ← Subgroup.map_map, elementaryBlockGroup_map,
    elementaryReindexGroup_map]

/-! ### Padding preserves elementary matrices

`KOne/ClassicalKOne.lean` records that the elementary groups form a direct
subsystem and leaves it unproved, having no use for it; the cofinality argument
below needs it. -/

section Padding

variable {R : Type*} [Ring R]

theorem single_apply_ite {q : ℕ} (u v x y : Fin q) (c : R) :
    Matrix.single u v c x y = if u = x ∧ v = y then c else 0 := by
  by_cases huv : u = x ∧ v = y
  · rw [if_pos huv, huv.1, huv.2, Matrix.single_apply_same]
  · rw [if_neg huv, Matrix.single_apply_of_ne _ _ _ _ _ huv]

/-- Padding an elementary matrix is the elementary matrix at the padded index
pair. -/
theorem stabMatrix_one_add_single {p q : ℕ} (h : p ≤ q) (i j : Fin p) (a : R) :
    stabMatrix q ((1 : Matrix (Fin p) (Fin p) R) + Matrix.single i j a)
      = (1 : Matrix (Fin q) (Fin q) R)
        + Matrix.single (Fin.castLE h i) (Fin.castLE h j) a := by
  ext x y
  rw [stabMatrix_apply, Matrix.add_apply, Matrix.one_apply, single_apply_ite]
  by_cases hx : (x : ℕ) < p
  · by_cases hy : (y : ℕ) < p
    · rw [padEntry_of_lt_lt _ hx hy, Matrix.add_apply, Matrix.one_apply,
        single_apply_ite]
      congr 1
      · by_cases hxy : (x : ℕ) = (y : ℕ)
        · rw [if_pos (Fin.ext hxy : (⟨(x : ℕ), hx⟩ : Fin p) = ⟨(y : ℕ), hy⟩),
            if_pos (Fin.ext hxy : x = y)]
        · have hne1 : ¬ ((⟨(x : ℕ), hx⟩ : Fin p) = ⟨(y : ℕ), hy⟩) := by
            intro hc
            have hv := congrArg Fin.val hc
            exact hxy hv
          have hne2 : ¬ (x = y) := by
            intro hc
            have hv := congrArg Fin.val hc
            exact hxy hv
          rw [if_neg hne1, if_neg hne2]
      · by_cases hij : (i : ℕ) = (x : ℕ) ∧ (j : ℕ) = (y : ℕ)
        · rw [if_pos (⟨Fin.ext hij.1, Fin.ext hij.2⟩ :
              i = (⟨(x : ℕ), hx⟩ : Fin p) ∧ j = ⟨(y : ℕ), hy⟩),
            if_pos (⟨Fin.ext hij.1, Fin.ext hij.2⟩ :
              Fin.castLE h i = x ∧ Fin.castLE h j = y)]
        · rw [if_neg (fun hc : i = (⟨(x : ℕ), hx⟩ : Fin p) ∧ j = ⟨(y : ℕ), hy⟩ =>
              hij ⟨congrArg Fin.val hc.1, congrArg Fin.val hc.2⟩),
            if_neg (fun hc : Fin.castLE h i = x ∧ Fin.castLE h j = y =>
              hij ⟨congrArg Fin.val hc.1, congrArg Fin.val hc.2⟩)]
    · have hne : ¬ (x = y) := by
        intro hc
        exact hy (by rw [← hc]; exact hx)
      have hns : ¬ (Fin.castLE h i = x ∧ Fin.castLE h j = y) := by
        rintro ⟨-, hc⟩
        exact hy (by rw [← hc]; exact j.isLt)
      rw [padEntry_of_lt_ge _ hx hy, if_neg hne, if_neg hns, add_zero]
  · have hns : ¬ (Fin.castLE h i = x ∧ Fin.castLE h j = y) := by
      rintro ⟨hc, -⟩
      exact hx (by rw [← hc]; exact i.isLt)
    rw [padEntry_of_ge _ hx, if_neg hns, add_zero]
    by_cases hxy : (x : ℕ) = (y : ℕ)
    · rw [if_pos hxy, if_pos (Fin.ext hxy : x = y)]
    · rw [if_neg hxy, if_neg (fun hc : x = y => hxy (congrArg Fin.val hc))]

theorem castLE_ne {p q : ℕ} (h : p ≤ q) {i j : Fin p} (hij : i ≠ j) :
    Fin.castLE h i ≠ Fin.castLE h j := by
  intro hc
  apply hij
  have hv := congrArg Fin.val hc
  exact Fin.ext hv

theorem glStab_elementaryUnit {p q : ℕ} (h : p ≤ q) (i j : Fin p) (hij : i ≠ j)
    (a : R) :
    glStab R p q h (elementaryUnit i j hij a)
      = elementaryUnit (Fin.castLE h i) (Fin.castLE h j) (castLE_ne h hij) a := by
  apply Units.ext
  rw [glStab_val]
  exact stabMatrix_one_add_single h i j a

/-- **The elementary groups form a direct subsystem**: padding carries
`EL_p(R)` into `EL_q(R)`. -/
theorem glStab_elementaryGroup_le {p q : ℕ} (h : p ≤ q) :
    (elementaryGroup (Fin p) R).map (glStab R p q h)
      ≤ elementaryGroup (Fin q) R := by
  rw [elementaryGroup, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  change glStab R p q h (elementaryUnit i j hij a) ∈ elementaryGroup (Fin q) R
  rw [glStab_elementaryUnit]
  exact elementaryUnit_mem _ _ _ a

theorem glStab_glStab (R : Type*) [Ring R] {p q r : ℕ} (h₁ : p ≤ q) (h₂ : q ≤ r)
    (h₃ : p ≤ r) (u : (Matrix (Fin p) (Fin p) R)ˣ) :
    glStab R q r h₂ (glStab R p q h₁ u) = glStab R p r h₃ u := by
  apply Units.ext
  simp only [glStab_val]
  exact stabMatrix_stabMatrix h₁ r _

end Padding

/-! ### The isomorphism of stable general linear groups -/

section Colimit

variable (R : Type*) [Ring R]

/-- The rank-`m` piece of the forward map: flatten, then take the class at rank
`m * n`. -/
def moritaFwd (n m : ℕ)
    (u : (Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R))ˣ) :
    ClassicalGLColim R :=
  glColimOf R (m * n) (blockFlatUnitEquiv R n m u)

theorem moritaFwd_compat (n : ℕ) {m m' : ℕ} (h : m ≤ m')
    (u : (Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R))ˣ) :
    moritaFwd R n m u
      = moritaFwd R n m' (glStab (Matrix (Fin n) (Fin n) R) m m' h u) := by
  simp only [moritaFwd]
  rw [blockFlatUnitEquiv_glStab R n h (rank_mul_le_mul h n) u,
    glColimOf_glStab (R := R) (rank_mul_le_mul h n)]

/-- **The map `GL(M_n(R)) → GL(R)` induced by the flattenings.** -/
def moritaGLFun (n : ℕ) :
    ClassicalGLColim (Matrix (Fin n) (Fin n) R) → ClassicalGLColim R :=
  DirectLimit.lift (glStab (Matrix (Fin n) (Fin n) R)) (moritaFwd R n)
    (fun _ _ h u => moritaFwd_compat R n h u)

theorem moritaGLFun_glColimOf (n m : ℕ)
    (u : (Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R))ˣ) :
    moritaGLFun R n (glColimOf (Matrix (Fin n) (Fin n) R) m u)
      = glColimOf R (m * n) (blockFlatUnitEquiv R n m u) := rfl

/-- The forward map is a group homomorphism. -/
def moritaGLHom (n : ℕ) :
    ClassicalGLColim (Matrix (Fin n) (Fin n) R) →* ClassicalGLColim R :=
  MonoidHom.mk' (moritaGLFun R n) (by
    intro x y
    obtain ⟨m, u, v, rfl, rfl⟩ :=
      DirectLimit.exists_eq_mk₂ (f := glStab (Matrix (Fin n) (Fin n) R)) x y
    have hu : (⟦⟨m, u⟩⟧ : ClassicalGLColim (Matrix (Fin n) (Fin n) R))
        = glColimOf (Matrix (Fin n) (Fin n) R) m u := rfl
    have hv : (⟦⟨m, v⟩⟧ : ClassicalGLColim (Matrix (Fin n) (Fin n) R))
        = glColimOf (Matrix (Fin n) (Fin n) R) m v := rfl
    rw [hu, hv, ← map_mul (glColimOf (Matrix (Fin n) (Fin n) R) m),
      moritaGLFun_glColimOf, moritaGLFun_glColimOf, moritaGLFun_glColimOf,
      map_mul, map_mul])

theorem moritaGLHom_glColimOf (n m : ℕ)
    (u : (Matrix (Fin m) (Fin m) (Matrix (Fin n) (Fin n) R))ˣ) :
    moritaGLHom R n (glColimOf (Matrix (Fin n) (Fin n) R) m u)
      = glColimOf R (m * n) (blockFlatUnitEquiv R n m u) := rfl

/-- The rank-`p` piece of the backward map: pad from rank `p` to rank `p * n`,
unflatten, and take the class at rank `p`.  The padding is where `n ≥ 1` is
used: it is what makes `m ↦ m * n` cofinal. -/
def moritaBack (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (u : (Matrix (Fin p) (Fin p) R)ˣ) :
    ClassicalGLColim (Matrix (Fin n) (Fin n) R) :=
  glColimOf (Matrix (Fin n) (Fin n) R) p
    ((blockFlatUnitEquiv R n p).symm (glStab R p (p * n) (rank_le_mul p hn) u))

theorem moritaBack_compat (n : ℕ) (hn : 1 ≤ n) {p q : ℕ} (h : p ≤ q)
    (u : (Matrix (Fin p) (Fin p) R)ˣ) :
    moritaBack R n hn p u = moritaBack R n hn q (glStab R p q h u) := by
  have hflat : blockFlatUnitEquiv R n p
        ((blockFlatUnitEquiv R n p).symm
          (glStab R p (p * n) (rank_le_mul p hn) u))
      = glStab R p (p * n) (rank_le_mul p hn) u :=
    (blockFlatUnitEquiv R n p).apply_symm_apply _
  have hstep : glStab R q (q * n) (rank_le_mul q hn) (glStab R p q h u)
      = blockFlatUnitEquiv R n q
          (glStab (Matrix (Fin n) (Fin n) R) p q h
            ((blockFlatUnitEquiv R n p).symm
              (glStab R p (p * n) (rank_le_mul p hn) u))) := by
    rw [blockFlatUnitEquiv_glStab R n h (rank_mul_le_mul h n), hflat,
      glStab_glStab R h (rank_le_mul q hn) (le_trans h (rank_le_mul q hn)),
      glStab_glStab R (rank_le_mul p hn) (rank_mul_le_mul h n)
        (le_trans h (rank_le_mul q hn))]
  simp only [moritaBack]
  rw [hstep, MulEquiv.symm_apply_apply,
    glColimOf_glStab (R := Matrix (Fin n) (Fin n) R) h]

/-- **The map `GL(R) → GL(M_n(R))` inverse to `moritaGLHom`.** -/
def moritaGLInvFun (n : ℕ) (hn : 1 ≤ n) :
    ClassicalGLColim R → ClassicalGLColim (Matrix (Fin n) (Fin n) R) :=
  DirectLimit.lift (glStab R) (moritaBack R n hn)
    (fun _ _ h u => moritaBack_compat R n hn h u)

theorem moritaGLInvFun_glColimOf (n : ℕ) (hn : 1 ≤ n) (p : ℕ)
    (u : (Matrix (Fin p) (Fin p) R)ˣ) :
    moritaGLInvFun R n hn (glColimOf R p u)
      = glColimOf (Matrix (Fin n) (Fin n) R) p
          ((blockFlatUnitEquiv R n p).symm
            (glStab R p (p * n) (rank_le_mul p hn) u)) := rfl

/-- **The stable general linear groups agree**: `GL(M_n(R)) ≅ GL(R)` for every
ring and every `n ≥ 1`, because `m ↦ m * n` is a cofinal subsystem. -/
def moritaGLEquiv (n : ℕ) (hn : 1 ≤ n) :
    ClassicalGLColim (Matrix (Fin n) (Fin n) R) ≃* ClassicalGLColim R where
  toFun := moritaGLHom R n
  invFun := moritaGLInvFun R n hn
  left_inv := by
    intro z
    induction z using DirectLimit.induction with
    | ih m u =>
        have hz : (⟦⟨m, u⟩⟧ : ClassicalGLColim (Matrix (Fin n) (Fin n) R))
            = glColimOf (Matrix (Fin n) (Fin n) R) m u := rfl
        have key : blockFlatUnitEquiv R n (m * n)
              (glStab (Matrix (Fin n) (Fin n) R) m (m * n) (rank_le_mul m hn) u)
            = glStab R (m * n) (m * n * n) (rank_le_mul (m * n) hn)
                (blockFlatUnitEquiv R n m u) :=
          blockFlatUnitEquiv_glStab R n (rank_le_mul m hn)
            (rank_le_mul (m * n) hn) u
        rw [hz, moritaGLHom_glColimOf, moritaGLInvFun_glColimOf, ← key,
          MulEquiv.symm_apply_apply,
          glColimOf_glStab (R := Matrix (Fin n) (Fin n) R) (rank_le_mul m hn)]
  right_inv := by
    intro z
    induction z using DirectLimit.induction with
    | ih p u =>
        have hz : (⟦⟨p, u⟩⟧ : ClassicalGLColim R) = glColimOf R p u := rfl
        rw [hz, moritaGLInvFun_glColimOf, moritaGLHom_glColimOf,
          MulEquiv.apply_symm_apply,
          glColimOf_glStab (R := R) (rank_le_mul p hn)]
  map_mul' := (moritaGLHom R n).map_mul

theorem moritaGLEquiv_apply (n : ℕ) (hn : 1 ≤ n)
    (z : ClassicalGLColim (Matrix (Fin n) (Fin n) R)) :
    moritaGLEquiv R n hn z = moritaGLHom R n z := rfl

/-- **The elementary subgroups correspond.**

Forwards: the flattening carries `EL_m(M_n(R))` into `EL_{mn}(R)`.  Backwards:
an elementary matrix at rank `p` is elementary at rank `m * n` for any `m ≥ 2`
with `p ≤ m * n`, and there `EL_{mn}(R)` is exactly the image of
`EL_m(M_n(R))`. -/
theorem moritaGLEquiv_elementaryColim (n : ℕ) (hn : 1 ≤ n) :
    (elementaryColim (Matrix (Fin n) (Fin n) R)).map
        (moritaGLEquiv R n hn).toMonoidHom
      = elementaryColim R := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    show (⨆ m : ℕ, (elementaryGroup (Fin m) (Matrix (Fin n) (Fin n) R)).map
        (glColimOf (Matrix (Fin n) (Fin n) R) m)) ≤ _
    refine iSup_le fun m => ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, moritaGLEquiv_apply,
      moritaGLHom_glColimOf]
    exact glColimOf_mem_elementaryColim R
      (blockFlatUnitEquiv_elementary_le R n m (Subgroup.mem_map_of_mem _ hu))
  · show (⨆ p : ℕ, (elementaryGroup (Fin p) R).map (glColimOf R p)) ≤ _
    refine iSup_le fun p => ?_
    rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    simp only [Subgroup.mem_comap]
    obtain ⟨m, hpm, hm2⟩ : ∃ m : ℕ, p ≤ m ∧ 2 ≤ m :=
      ⟨max p 2, le_max_left p 2, le_max_right p 2⟩
    have hpmn : p ≤ m * n := le_trans hpm (rank_le_mul m hn)
    have hw : glStab R p (m * n) hpmn u ∈ elementaryGroup (Fin (m * n)) R :=
      glStab_elementaryGroup_le hpmn (Subgroup.mem_map_of_mem _ hu)
    rw [← blockFlatUnitEquiv_elementary_map R n hm2] at hw
    obtain ⟨v, hv, hvval⟩ := hw
    have hvv : blockFlatUnitEquiv R n m v = glStab R p (m * n) hpmn u := hvval
    refine ⟨glColimOf (Matrix (Fin n) (Fin n) R) m v,
      glColimOf_mem_elementaryColim _ hv, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, moritaGLEquiv_apply, moritaGLHom_glColimOf,
      hvv, glColimOf_glStab (R := R) hpmn]

/-! ### Morita invariance of `K₁` -/

/-- **`K_1(M_n(R)) ≅ K_1(R)`**, the printed Morita step, for an arbitrary unital
ring and every `n ≥ 1`. -/
def moritaKOneEquiv (n : ℕ) (hn : 1 ≤ n) :
    AlgebraicKOne (Matrix (Fin n) (Fin n) R) ≃* AlgebraicKOne R :=
  QuotientGroup.congr (elementaryColim (Matrix (Fin n) (Fin n) R))
    (elementaryColim R) (moritaGLEquiv R n hn)
    (moritaGLEquiv_elementaryColim R n hn)

/-- **The printed sentence**: `K_1(M_n(R)) ≅ K_1(R)` by Morita invariance. -/
theorem morita_algebraicKOne (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (AlgebraicKOne (Matrix (Fin n) (Fin n) R) ≃* AlgebraicKOne R) :=
  ⟨moritaKOneEquiv R n hn⟩

/-! ### Naturality: the reduction to `n = 1` respects the comparison maps -/

/-- At rank one the flattening is the padding: the `1 × 1` matrix over `M_n(R)`
with entry `u` flattens to `diag(u, 1)` at rank `1 * n`. -/
theorem blockFlatUnitEquiv_one_unitsToGLOne (n : ℕ) (h : n ≤ 1 * n)
    (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    blockFlatUnitEquiv R n 1 (unitsToGLOne (Matrix (Fin n) (Fin n) R) u)
      = glStab R n (1 * n) h u := by
  apply Units.ext
  rw [blockFlatUnitEquiv_val, glStab_val]
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := finProdFinEquiv.surjective y
  have hij : i = j := Fin.ext (by
    rw [Nat.lt_one_iff.mp i.isLt, Nat.lt_one_iff.mp j.isLt])
  subst hij
  have hi : (i : ℕ) = 0 := Nat.lt_one_iff.mp i.isLt
  have hval : ((unitsToGLOne (Matrix (Fin n) (Fin n) R) u :
        (Matrix (Fin 1) (Fin 1) (Matrix (Fin n) (Fin n) R))ˣ) :
        Matrix (Fin 1) (Fin 1) (Matrix (Fin n) (Fin n) R))
      = Matrix.scalar (Fin 1) (u : Matrix (Fin n) (Fin n) R) := rfl
  rw [blockFlatten_apply, stabMatrix_apply, val_finProdFinEquiv,
    val_finProdFinEquiv, hval, Matrix.scalar_apply, Matrix.diagonal_apply_eq,
    hi, Nat.mul_zero, Nat.add_zero, Nat.add_zero,
    padEntry_of_lt_lt _ a.isLt b.isLt]

/-- **The Morita isomorphism carries the printed `κ` to the canonical
stabilization map.**

`(M_n(R))^× = GL_n(R)`, and `κ : (M_n(R))^× → K_1(M_n(R))` is the printed
comparison map of `thm:mf-quotient-units` at the matrix ring.  Composed with
`K_1(M_n(R)) ≅ K_1(R)` it is the canonical map `GL_n(R) → K_1(R)`, so the
printed reduction to `n = 1` identifies the comparison maps and not merely the
groups. -/
theorem moritaKOneEquiv_kappa (n : ℕ) (hn : 1 ≤ n)
    (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    moritaKOneEquiv R n hn (kappa (Matrix (Fin n) (Fin n) R) u)
      = QuotientGroup.mk (glColimOf R n u) := by
  have h1 : moritaKOneEquiv R n hn (kappa (Matrix (Fin n) (Fin n) R) u)
      = QuotientGroup.mk (moritaGLEquiv R n hn
          (glColimOf (Matrix (Fin n) (Fin n) R) 1
            (unitsToGLOne (Matrix (Fin n) (Fin n) R) u))) := rfl
  rw [h1, moritaGLEquiv_apply, moritaGLHom_glColimOf,
    blockFlatUnitEquiv_one_unitsToGLOne R n (le_of_eq (Nat.one_mul n).symm) u,
    glColimOf_glStab (R := R) (le_of_eq (Nat.one_mul n).symm)]

end Colimit

end

end AlgebraicK
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AlgebraicK.blockIndex_lt_iff
#audit_axioms GroupApproximation.AlgebraicK.blockFlatten_stabMatrix
#audit_axioms GroupApproximation.AlgebraicK.blockFlatUnitEquiv_glStab
#audit_axioms GroupApproximation.AlgebraicK.blockFlatUnitEquiv_elementary_map
#audit_axioms GroupApproximation.AlgebraicK.glStab_elementaryGroup_le
#audit_axioms GroupApproximation.AlgebraicK.moritaGLEquiv
#audit_axioms GroupApproximation.AlgebraicK.moritaGLEquiv_elementaryColim
#audit_axioms GroupApproximation.AlgebraicK.moritaKOneEquiv
#audit_axioms GroupApproximation.AlgebraicK.morita_algebraicKOne
#audit_axioms GroupApproximation.AlgebraicK.moritaKOneEquiv_kappa
