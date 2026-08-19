import GroupApproximation.Analysis.MaximalCStarKazhdanAverage

/-!
# The quasi-regular representation and the strictness witness

The unitary representation of a group on `ℓ²` of a coset space, packaged
as a coordinate of the universal representation family, together with the
witness vector for strict compression: the point mass at the base coset
is fixed by the subgroup and moved by every element outside it.

This is brick (b3) of the strict-Kazhdan-compression program of
`notes/FORMALIZATION_DIRECTIVES_2026-08-15.md` §1: at this coordinate the
fixed subspace of a subgroup `K` strictly contains the fixed subspace of
any subgroup with an element outside `K`, which is what separates the
Kazhdan projection from its conjugate once the spectral-gap brick lands.
The construction mirrors the left regular representation of
`ReducedGroupCStarTrace`.
-/

namespace GroupApproximation
namespace QuasiRegularWitness

open ReducedGroupCStarTrace

noncomputable section

universe u

variable (G : Type u) [Group G] (K : Subgroup G)

/-- The Hilbert space `ℓ²(G/K)` of the quasi-regular representation. -/
abbrev CosetHilbert := lp (fun _ : G ⧸ K ↦ ℂ) 2

/-- The quasi-regular unitary on `ℓ²(G/K)`, by reindexing along the left
coset action. -/
def quasiRegular (g : G) : CosetHilbert G K ≃ₗᵢ[ℂ] CosetHilbert G K :=
  lpCongrLeft (MulAction.toPermHom G (G ⧸ K) g)

/-- The quasi-regular unitary as a bounded operator. -/
def quasiRegularOperator (g : G) :
    CosetHilbert G K →L[ℂ] CosetHilbert G K :=
  (quasiRegular G K g).toLinearIsometry.toContinuousLinearMap

@[simp] theorem quasiRegularOperator_apply (g : G) (f : CosetHilbert G K)
    (x : G ⧸ K) :
    quasiRegularOperator G K g f x = f (g⁻¹ • x) :=
  rfl

theorem quasiRegularOperator_one : quasiRegularOperator G K 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  rw [quasiRegularOperator_apply]
  rw [inv_one, one_smul]
  rfl

theorem quasiRegularOperator_mul (g h : G) :
    quasiRegularOperator G K g * quasiRegularOperator G K h
      = quasiRegularOperator G K (g * h) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  show f (h⁻¹ • (g⁻¹ • x)) = f ((g * h)⁻¹ • x)
  rw [mul_inv_rev, mul_smul]

theorem star_quasiRegularOperator (g : G) :
    star (quasiRegularOperator G K g) = quasiRegularOperator G K g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  change ContinuousLinearMap.adjoint
    (quasiRegular G K g : CosetHilbert G K →L[ℂ] CosetHilbert G K) = _
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  show f (g • x) = f ((g⁻¹)⁻¹ • x)
  rw [inv_inv]

/-- The quasi-regular unitary inside the full operator algebra. -/
def quasiRegularUnitary (g : G) :
    unitary (CosetHilbert G K →L[ℂ] CosetHilbert G K) :=
  ⟨quasiRegularOperator G K g, by
    constructor
    · rw [star_quasiRegularOperator, quasiRegularOperator_mul,
        inv_mul_cancel, quasiRegularOperator_one]
    · rw [star_quasiRegularOperator, quasiRegularOperator_mul,
        mul_inv_cancel, quasiRegularOperator_one]⟩

/-- The quasi-regular unitary representation. -/
def quasiRegularUnitaryHom :
    G →* unitary (CosetHilbert G K →L[ℂ] CosetHilbert G K) where
  toFun := quasiRegularUnitary G K
  map_one' := Subtype.ext (quasiRegularOperator_one G K)
  map_mul' g h := Subtype.ext (quasiRegularOperator_mul G K g h).symm

theorem smul_base_eq_base_iff (g : G) :
    g • ((1 : G) : G ⧸ K) = ((1 : G) : G ⧸ K) ↔ g ∈ K := by
  have h1 : g • ((1 : G) : G ⧸ K) = ((g * 1 : G) : G ⧸ K) :=
    MulAction.Quotient.smul_mk K g 1
  rw [h1, mul_one, QuotientGroup.eq, mul_one]
  exact inv_mem_iff

section BaseVector

variable [DecidableEq (G ⧸ K)]

/-- The point mass at the base coset. -/
def baseVector : CosetHilbert G K := lp.single 2 ((1 : G) : G ⧸ K) 1

/-- **The witness is a point mass.**  The base coordinate of the base vector
is `1`.

This is the coordinate computation the separation statement is assembled
from; the statement the manuscript prints is `baseVector_apply_base`, at the
end of this section. -/
theorem baseVector_self_coeff :
    ∀ (G : Type u) [Group G] (K : Subgroup G) [DecidableEq (G ⧸ K)],
      baseVector G K ((1 : G) : G ⧸ K) = 1 := by
  intro G _ K _
  unfold baseVector
  exact lp.single_apply_self 2 _ _

theorem baseVector_apply_ne {x : G ⧸ K} (hx : x ≠ ((1 : G) : G ⧸ K)) :
    baseVector G K x = 0 := by
  unfold baseVector
  exact lp.single_apply_ne 2 _ _ hx

theorem baseVector_ne_zero : baseVector G K ≠ 0 := by
  intro h
  have h1 := congrArg (fun f : CosetHilbert G K => f ((1 : G) : G ⧸ K)) h
  simp only at h1
  rw [baseVector_self_coeff G K] at h1
  have h2 : ((0 : CosetHilbert G K) : (G ⧸ K) → ℂ) ((1 : G) : G ⧸ K) = 0 :=
    rfl
  exact one_ne_zero (h1.trans h2)

theorem quasiRegularOperator_baseVector_of_mem {k : G} (hk : k ∈ K) :
    quasiRegularOperator G K k (baseVector G K) = baseVector G K := by
  apply lp.ext
  funext x
  rw [quasiRegularOperator_apply]
  show baseVector G K (k⁻¹ • x) = baseVector G K x
  by_cases hx : x = ((1 : G) : G ⧸ K)
  · subst hx
    rw [(smul_base_eq_base_iff G K k⁻¹).mpr (inv_mem hk)]
  · have hne : k⁻¹ • x ≠ ((1 : G) : G ⧸ K) := by
      intro hc
      apply hx
      have := congrArg (fun y => k • y) hc
      simp only [smul_smul, mul_inv_cancel, one_smul] at this
      rw [this, (smul_base_eq_base_iff G K k).mpr hk]
    rw [baseVector_apply_ne G K hne, baseVector_apply_ne G K hx]

theorem quasiRegularOperator_baseVector_of_notMem {a : G} (ha : a ∉ K) :
    quasiRegularOperator G K a (baseVector G K) ≠ baseVector G K := by
  intro h
  have happ := congrArg
    (fun f : CosetHilbert G K => f ((1 : G) : G ⧸ K)) h
  simp only at happ
  rw [quasiRegularOperator_apply] at happ
  have hne : a⁻¹ • ((1 : G) : G ⧸ K) ≠ ((1 : G) : G ⧸ K) := by
    intro hc
    exact ha (inv_mem_iff.mp ((smul_base_eq_base_iff G K a⁻¹).mp hc))
  have h0 : baseVector G K (a⁻¹ • ((1 : G) : G ⧸ K)) = 0 :=
    baseVector_apply_ne G K hne
  have h1 : baseVector G K ((1 : G) : G ⧸ K) = 1 := baseVector_self_coeff G K
  exact zero_ne_one (h0.symm.trans (happ.trans h1))

/-- **The quasi-regular coordinate separates a subgroup from anything outside
it.**  This is the sentence the manuscript prints in the remark *the maximal
algebra under proper one-sided conjugation*: at the quasi-regular coordinate
`ℓ²(G/K)` the point mass at the base coset is fixed by `K` and moved by every
element outside `K` — which is what makes the two projections differ there.

All four printed clauses are stated: the witness really is the point mass at
the base coset (its base coordinate is `1`), it is a nonzero vector, the whole
subgroup fixes it, and *every* element outside the subgroup moves it.  Only
the first of these is a coordinate computation; the separation is the last
two, and a badge on the coordinate computation alone would certify a true
statement that is not the printed one.

One deliberate strengthening.  The manuscript, taking `K = tΓt⁻¹`, says the
point mass is "moved by every element of `Γ` outside it"; the last clause here
quantifies over every element of the ambient group outside `K`, which implies
the printed claim and needs no `Γ`.  Nothing about the compression is used —
only that `K` is a subgroup and the coordinate is `ℓ²(G/K)`.

The group, the subgroup and the decidability of the coset space are quantified
inside the proposition.  They are the section variables of this file, and a
cited endpoint that inherits them silently has a leading input its printed
header does not show. -/
theorem baseVector_apply_base :
    ∀ (G : Type u) [Group G] (K : Subgroup G) [DecidableEq (G ⧸ K)],
      baseVector G K ((1 : G) : G ⧸ K) = 1 ∧
        baseVector G K ≠ 0 ∧
        (∀ k ∈ K, quasiRegularOperator G K k (baseVector G K) = baseVector G K) ∧
        (∀ a ∉ K,
          quasiRegularOperator G K a (baseVector G K) ≠ baseVector G K) := by
  intro G _ K _
  exact ⟨baseVector_self_coeff G K, baseVector_ne_zero G K,
    fun _ hk => quasiRegularOperator_baseVector_of_mem G K hk,
    fun _ ha => quasiRegularOperator_baseVector_of_notMem G K ha⟩

/-- **The strictness witness**: for any element outside the subgroup, the
point mass at the base coset is a nonzero vector fixed by the whole
subgroup and moved by that element. -/
theorem exists_baseVector_witness {a : G} (ha : a ∉ K) :
    ∃ v : CosetHilbert G K, v ≠ 0 ∧
      (∀ k ∈ K, quasiRegularOperator G K k v = v) ∧
      quasiRegularOperator G K a v ≠ v :=
  ⟨baseVector G K, baseVector_ne_zero G K,
    fun _ hk => quasiRegularOperator_baseVector_of_mem G K hk,
    quasiRegularOperator_baseVector_of_notMem G K ha⟩

end BaseVector

instance : Nontrivial (CosetHilbert G K →L[ℂ] CosetHilbert G K) := by
  letI := Classical.decEq (G ⧸ K)
  refine ⟨1, 0, fun h => ?_⟩
  have h1 : (1 : CosetHilbert G K →L[ℂ] CosetHilbert G K) (baseVector G K)
      = (0 : CosetHilbert G K →L[ℂ] CosetHilbert G K) (baseVector G K) := by
    rw [h]
  exact baseVector_ne_zero G K h1

/-- The quasi-regular representation, as a coordinate of the universal
representation family of the maximal group C-star algebra. -/
def quasiRegularRepresentation : CStarUnitaryRepresentation G :=
  CStarUnitaryRepresentation.ofHom G (quasiRegularUnitaryHom G K)

end

end QuasiRegularWitness
end GroupApproximation
