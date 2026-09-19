import GroupApproximation.Sofic.FiniteDimensionalResidual

/-!
# Section 49 for finite-dimensional unitary representations

Induction from a finite-index subgroup, in the form Section 49.1 uses: a
representation of `H` on `Y` induces one of `G` on `(G/H) × Y` by block-monomial
matrices, and the block of the induced representation at the base coset returns
the original representation.

Everything is carried by one *coefficient function*

`coeff π a b = π (a⁻¹ b)` when `a⁻¹ b ∈ H`, and `0` otherwise,

which is a total function of two group elements: the block-monomial pattern, the
cocycle identity, and unitarity are three of its algebraic properties, and no
dependent case distinction ever enters a matrix index.

The consequence is **Theorem 49.2** for the finite-dimensional residual: it is
exactly inherited by finite-index subgroups.
-/

namespace GroupApproximation

namespace InducedFdRep

open MatricialStabilityRadical Matrix

universe u

variable {G : Type u} [Group G] {H : Subgroup G} {Y : FiniteModel}

open scoped Classical in
/-- The matrix coefficient attached to a pair of group elements. -/
noncomputable def coeff (π : H →* Matrix.unitaryGroup Y ℂ) (a b : G) :
    Matrix Y Y ℂ :=
  if h : a⁻¹ * b ∈ H then
    ((π ⟨a⁻¹ * b, h⟩ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) else 0

variable (π : H →* Matrix.unitaryGroup Y ℂ)

theorem coeff_of_mem {a b : G} (h : a⁻¹ * b ∈ H) :
    coeff π a b = ((π ⟨a⁻¹ * b, h⟩ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) := by
  rw [coeff, dif_pos h]

theorem coeff_of_not_mem {a b : G} (h : a⁻¹ * b ∉ H) : coeff π a b = 0 := by
  rw [coeff, dif_neg h]

/-- Left translation invariance. -/
theorem coeff_translate (g a b : G) : coeff π (g * a) (g * b) = coeff π a b := by
  have hsame : (g * a)⁻¹ * (g * b) = a⁻¹ * b := by group
  by_cases hmem : a⁻¹ * b ∈ H
  · have hmem' : (g * a)⁻¹ * (g * b) ∈ H := by rw [hsame]; exact hmem
    rw [coeff_of_mem π hmem', coeff_of_mem π hmem]
    congr 2
    exact Subtype.ext hsame
  · have hmem' : (g * a)⁻¹ * (g * b) ∉ H := by rw [hsame]; exact hmem
    rw [coeff_of_not_mem π hmem', coeff_of_not_mem π hmem]

theorem coeff_self (a : G) : coeff π a a = 1 := by
  have hmem : a⁻¹ * a ∈ H := by
    rw [inv_mul_cancel]
    exact H.one_mem
  rw [coeff_of_mem π hmem]
  have hone : (⟨a⁻¹ * a, hmem⟩ : H) = 1 := by
    refine Subtype.ext ?_
    simp
  rw [hone, map_one]
  rfl

/-- **The cocycle identity.**  Composing coefficients across a point of the
same coset multiplies the representation values. -/
theorem coeff_mul_coeff {a b d : G} (h : b⁻¹ * d ∈ H) :
    coeff π a b * coeff π b d = coeff π a d := by
  by_cases hab : a⁻¹ * b ∈ H
  · have had : a⁻¹ * d ∈ H := by
      have : a⁻¹ * d = (a⁻¹ * b) * (b⁻¹ * d) := by group
      rw [this]
      exact H.mul_mem hab h
    rw [coeff_of_mem π hab, coeff_of_mem π h, coeff_of_mem π had]
    have hmul : (⟨a⁻¹ * b, hab⟩ : H) * ⟨b⁻¹ * d, h⟩ = ⟨a⁻¹ * d, had⟩ := by
      refine Subtype.ext ?_
      show (a⁻¹ * b) * (b⁻¹ * d) = a⁻¹ * d
      group
    rw [← hmul, map_mul]
    rfl
  · have hnad : a⁻¹ * d ∉ H := by
      intro hcon
      apply hab
      have hb : a⁻¹ * b = (a⁻¹ * d) * (b⁻¹ * d)⁻¹ := by group
      rw [hb]
      exact H.mul_mem hcon (H.inv_mem h)
    rw [coeff_of_not_mem π hab, coeff_of_not_mem π hnad, zero_mul]

/-- Conjugate transposition exchanges the two arguments. -/
theorem coeff_conjTranspose (a b : G) : (coeff π a b)ᴴ = coeff π b a := by
  by_cases hab : a⁻¹ * b ∈ H
  · have hba : b⁻¹ * a ∈ H := by
      have : b⁻¹ * a = (a⁻¹ * b)⁻¹ := by group
      rw [this]
      exact H.inv_mem hab
    rw [coeff_of_mem π hab, coeff_of_mem π hba]
    have hstar : ((π ⟨a⁻¹ * b, hab⟩ : Matrix.unitaryGroup Y ℂ) :
        Matrix Y Y ℂ)ᴴ = ((π ⟨a⁻¹ * b, hab⟩ : Matrix.unitaryGroup Y ℂ)⁻¹ :
        Matrix.unitaryGroup Y ℂ) := by
      rfl
    rw [hstar]
    have hinv : (⟨a⁻¹ * b, hab⟩ : H)⁻¹ = ⟨b⁻¹ * a, hba⟩ := by
      refine Subtype.ext ?_
      show (a⁻¹ * b)⁻¹ = b⁻¹ * a
      group
    rw [← map_inv, hinv]
  · have hnba : b⁻¹ * a ∉ H := by
      intro hcon
      apply hab
      have : a⁻¹ * b = (b⁻¹ * a)⁻¹ := by group
      rw [this]
      exact H.inv_mem hcon
    rw [coeff_of_not_mem π hab, coeff_of_not_mem π hnba]
    simp

/-! ## The induced representation -/

section Induced

variable {n : ℕ} (r : Fin n → G) (idx : G → Fin n)

/-- The coordinate model of the induced representation. -/
@[reducible] def indModel (n : ℕ) (Y : FiniteModel) : FiniteModel where
  carrier := Fin n × Y.carrier
  fintype := inferInstance
  decidableEq := inferInstance

/-- The induced matrix: block-monomial, with the coefficient function
supplying each block. -/
noncomputable def indMatrix (g : G) :
    Matrix (indModel n Y) (indModel n Y) ℂ :=
  Matrix.of fun p q => coeff π (r p.1) (g * r q.1) p.2 q.2

@[simp] theorem indMatrix_apply (g : G) (p q : indModel n Y) :
    indMatrix π r g p q = coeff π (r p.1) (g * r q.1) p.2 q.2 := rfl

variable (hidx : ∀ (i : Fin n) (b : G), idx b = i ↔ (r i)⁻¹ * b ∈ H)

include hidx

/-- **The transversal sum.**  Exactly one summand survives, and the cocycle
identity collapses it. -/
theorem sum_coeff (a g b : G) :
    ∑ j : Fin n, coeff π a (g * r j) * coeff π (r j) b = coeff π a (g * b) := by
  classical
  rw [Finset.sum_eq_single (idx b)]
  · have hmem : (r (idx b))⁻¹ * b ∈ H := (hidx (idx b) b).mp rfl
    have hshift : coeff π (r (idx b)) b
        = coeff π (g * r (idx b)) (g * b) := (coeff_translate π g _ _).symm
    rw [hshift]
    refine coeff_mul_coeff π ?_
    have : (g * r (idx b))⁻¹ * (g * b) = (r (idx b))⁻¹ * b := by group
    rw [this]
    exact hmem
  · intro j _ hj
    have hnot : (r j)⁻¹ * b ∉ H := by
      intro hcon
      exact hj ((hidx j b).mpr hcon).symm
    rw [coeff_of_not_mem π hnot, mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ (idx b)) hcon

theorem indMatrix_mul (g₁ g₂ : G) :
    indMatrix π r g₁ * indMatrix π r g₂ = indMatrix π r (g₁ * g₂) := by
  classical
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [indMatrix_apply]
  have hinner : ∀ j : Fin n,
      (∑ w : Y, coeff π (r p.1) (g₁ * r j) p.2 w
          * coeff π (r j) (g₂ * r q.1) w q.2)
        = (coeff π (r p.1) (g₁ * r j) * coeff π (r j) (g₂ * r q.1)) p.2 q.2 :=
    fun j => (Matrix.mul_apply).symm
  rw [Finset.sum_congr rfl fun j _ => hinner j, ← Matrix.sum_apply,
    sum_coeff π r idx hidx, mul_assoc]

theorem indMatrix_one : indMatrix π r (1 : G) = 1 := by
  classical
  ext p q
  rw [indMatrix_apply, one_mul, Matrix.one_apply]
  by_cases hpq : p.1 = q.1
  · have hmem : (r p.1)⁻¹ * r q.1 ∈ H := by
      rw [hpq, inv_mul_cancel]
      exact H.one_mem
    have hone : (⟨(r p.1)⁻¹ * r q.1, hmem⟩ : H) = 1 := by
      refine Subtype.ext ?_
      show (r p.1)⁻¹ * r q.1 = 1
      rw [hpq, inv_mul_cancel]
    rw [coeff_of_mem π hmem, hone, map_one]
    show (1 : Matrix Y Y ℂ) p.2 q.2 = _
    rw [Matrix.one_apply]
    by_cases hy : p.2 = q.2
    · rw [if_pos hy, if_pos (Prod.ext hpq hy)]
    · rw [if_neg hy, if_neg (fun hcon => hy (congrArg Prod.snd hcon))]
  · have hnot : (r p.1)⁻¹ * r q.1 ∉ H := by
      intro hcon
      have h1 : idx (r q.1) = p.1 := (hidx p.1 (r q.1)).mpr hcon
      have h2 : idx (r q.1) = q.1 := (hidx q.1 (r q.1)).mpr (by
        rw [inv_mul_cancel]
        exact H.one_mem)
      exact hpq (h1.symm.trans h2)
    rw [coeff_of_not_mem π hnot, Matrix.zero_apply,
      if_neg (fun hcon => hpq (congrArg Prod.fst hcon))]

omit hidx in
theorem indMatrix_conjTranspose (g : G) :
    (indMatrix π r g)ᴴ = indMatrix π r g⁻¹ := by
  ext p q
  rw [Matrix.conjTranspose_apply, indMatrix_apply, indMatrix_apply]
  have hstar := coeff_conjTranspose π (r q.1) (g * r p.1)
  have hentry : (coeff π (r q.1) (g * r p.1))ᴴ p.2 q.2
      = coeff π (g * r p.1) (r q.1) p.2 q.2 := by rw [hstar]
  rw [Matrix.conjTranspose_apply] at hentry
  rw [hentry, ← coeff_translate π g⁻¹ (g * r p.1) (r q.1)]
  congr 2
  group

/-- The induced representation, as a homomorphism into a unitary group. -/
noncomputable def indHom : G →* Matrix.unitaryGroup (indModel n Y) ℂ where
  toFun g := ⟨indMatrix π r g, by
    rw [Matrix.mem_unitaryGroup_iff']
    rw [Matrix.star_eq_conjTranspose, indMatrix_conjTranspose,
      indMatrix_mul π r idx hidx, inv_mul_cancel,
      indMatrix_one π r idx hidx]⟩
  map_one' := Subtype.ext (indMatrix_one π r idx hidx)
  map_mul' g₁ g₂ := Subtype.ext (indMatrix_mul π r idx hidx g₁ g₂).symm

omit hidx in
/-- **The base block.**  At a transversal index whose representative is the
identity, the induced representation returns the original one. -/
theorem indMatrix_base_block {i₀ : Fin n} (hr₀ : r i₀ = 1) (h : G) (hh : h ∈ H)
    (y z : Y) :
    indMatrix π r h (i₀, y) (i₀, z)
      = ((π ⟨h, hh⟩ : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) y z := by
  rw [indMatrix_apply, hr₀]
  have hmem : (1 : G)⁻¹ * (h * 1) ∈ H := by simpa using hh
  rw [coeff_of_mem π hmem]
  have harg : (⟨(1 : G)⁻¹ * (h * 1), hmem⟩ : H) = ⟨h, hh⟩ := by
    refine Subtype.ext ?_
    simp
  rw [harg]

end Induced

/-! ## Theorem 49.2 for the finite-dimensional residual -/

/-- **Theorem 49.2, finite-dimensional case.**  The finite-dimensional unitary
residual is exactly inherited by finite-index subgroups. -/
theorem fdUnitaryResidual_subgroupOf (H : Subgroup G) [H.FiniteIndex] :
    fdUnitaryResidual H = (fdUnitaryResidual G).subgroupOf H := by
  classical
  refine le_antisymm ?_ ?_
  · -- restriction of a representation of the ambient group
    intro x hx
    rw [Subgroup.mem_subgroupOf, mem_fdUnitaryResidual_iff]
    intro Y phi
    have := (mem_fdUnitaryResidual_iff).mp hx Y (phi.comp H.subtype)
    simpa using this
  · -- induction of a representation of the subgroup
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [mem_fdUnitaryResidual_iff]
    intro Y π
    haveI : Finite (G ⧸ H) := H.finite_quotient_of_finiteIndex
    haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
    set n : ℕ := Fintype.card (G ⧸ H) with hn
    set e : (G ⧸ H) ≃ Fin n := Fintype.equivFin _ with he
    set i₀ : Fin n := e (QuotientGroup.mk 1) with hi₀
    set r : Fin n → G := fun i => if i = i₀ then 1 else (e.symm i).out with hr
    have hrmk : ∀ i : Fin n, (QuotientGroup.mk (r i) : G ⧸ H) = e.symm i := by
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
    set idx : G → Fin n := fun b => e (QuotientGroup.mk b) with hidxdef
    have hidx : ∀ (i : Fin n) (b : G), idx b = i ↔ (r i)⁻¹ * b ∈ H := by
      intro i b
      show e (QuotientGroup.mk b) = i ↔ (r i)⁻¹ * b ∈ H
      constructor
      · intro hb
        refine (QuotientGroup.eq (s := H)).mp ?_
        rw [hrmk i, ← hb, Equiv.symm_apply_apply]
      · intro hb
        have heq := (QuotientGroup.eq (s := H)).mpr hb
        rw [hrmk i] at heq
        rw [← heq, Equiv.apply_symm_apply]
    have hr₀ : r i₀ = 1 := by rw [hr]; simp
    -- the induced representation kills `x`
    have hind := (mem_fdUnitaryResidual_iff).mp hx (indModel n Y)
      (indHom π r idx hidx)
    have hmat : indMatrix π r (x : G) = 1 := congrArg Subtype.val hind
    refine Subtype.ext ?_
    ext y z
    have hblock := indMatrix_base_block π r hr₀ (x : G) x.2 y z
    rw [hmat] at hblock
    rw [← hblock]
    have hone : ((1 : Matrix.unitaryGroup Y ℂ) : Matrix Y Y ℂ) = 1 := rfl
    rw [hone, Matrix.one_apply, Matrix.one_apply]
    simp [Prod.ext_iff]

/-- A group with no finite-dimensional residual passes that to its
finite-index subgroups. -/
theorem fdUnitaryResidual_eq_bot_of_finiteIndex (H : Subgroup G) [H.FiniteIndex]
    (h : fdUnitaryResidual G = ⊥) : fdUnitaryResidual H = ⊥ := by
  rw [fdUnitaryResidual_subgroupOf H, h]
  exact Subgroup.bot_subgroupOf H

end InducedFdRep

end GroupApproximation
