import GroupApproximation.PropertyT.ClassTwoApproximation
import GroupApproximation.PropertyT.FiniteClassTwoOrthogonality

/-!
# Exponent-free class-two fixed-space orthogonality

`ClassTwoOrthogonality.epsilonOrthogonal` obtains the `1 / sqrt 2` angle
bound between the two fixed subspaces of a class-two pair by making every
finite stage a *finite* group and averaging over it.  That step spends a
bounded exponent, and over a torsion-free coefficient ring no such exponent
exists.

This file removes the exponent.  The two devices that replace the finite
average are:

* **a two-term convex combination.**  If a single `x` in the left subgroup
  makes the correlation `⟪rho x v, v⟫` nonpositive, then already
  `‖(v + rho x⁻¹ v) / 2‖ ^ 2 ≤ ‖v‖ ^ 2 / 2`, and the angle bound follows with
  no averaging, no finiteness and no exponent
  (`abs_inner_le_of_correlation_nonpos`);
* **a cyclic-subspace mean-ergodic argument.**  If a vector `a` has the same
  correlation with `v` after translation by every element of a subgroup `D`,
  and `v` is orthogonal to the whole `D`-fixed subspace, then that
  correlation vanishes (`inner_eq_zero_of_translation_invariant`).  The proof
  compares the closed span of the `D`-orbit of `v` with the closed span of
  its displacements, using orthogonal complements only; it replaces the
  finite geometric sum
  `FiniteClassTwoOrthogonality.geomSum_apply_eq_zero_of_fixedSubmodule_bot`.

Splitting off one central commutator at a time then runs as an induction over
a finite list of commutators generating `⁅Y, X⁆`, and the directed-limit
machinery of `ClassTwoApproximation` supplies such a list at every finite
stage.  The resulting statement `epsilonOrthogonality` needs neither a
bounded exponent nor commutativity of the two subgroups.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u v

namespace ExponentFreeClassTwoOrthogonality

variable {G : Type u} [Group G]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Elementary rewriting helpers -/

/-- Composition of two represented elements. -/
theorem apply_mul (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g h : G) (z : E) :
    rho (g * h) z = rho g (rho h z) := by
  rw [map_mul]
  rfl

/-- Cancelling an inverse inside a representation. -/
theorem apply_inv_apply (rho : G →* (E ≃ₗᵢ[ℝ] E)) (g : G) (z : E) :
    rho g (rho g⁻¹ z) = z := by
  simp

/-- Orthogonality to the span of a set is orthogonality to the set. -/
theorem mem_span_orthogonal_iff {s : Set E} {z : E} :
    z ∈ (Submodule.span ℝ s)ᗮ ↔ ∀ y ∈ s, inner ℝ y z = 0 := by
  constructor
  · intro hz y hy
    exact (Submodule.mem_orthogonal _ _).mp hz y (Submodule.subset_span hy)
  · intro h
    rw [Submodule.mem_orthogonal]
    intro y hy
    induction hy using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simp
    | add w w' _ _ hw hw' => rw [inner_add_left, hw, hw']; ring
    | smul r w _ hw => rw [real_inner_smul_left, hw]; ring

/-! ### Invariant subspaces and their orthogonal projections -/

/-- If `rho g⁻¹` preserves a subspace, `rho g` preserves its orthogonal
complement. -/
theorem map_mem_orthogonal (rho : G →* (E ≃ₗᵢ[ℝ] E)) {F : Submodule ℝ E}
    {g : G} (hg : ∀ z ∈ F, rho g⁻¹ z ∈ F) {z : E} (hz : z ∈ Fᗮ) :
    rho g z ∈ Fᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  calc
    inner ℝ y (rho g z) = inner ℝ (rho g (rho g⁻¹ y)) (rho g z) := by
      rw [apply_inv_apply rho g y]
    _ = inner ℝ (rho g⁻¹ y) z := (rho g).inner_map_map _ _
    _ = 0 := (Submodule.mem_orthogonal _ _).mp hz _ (hg y hy)

/-- Orthogonal projection onto an invariant subspace is equivariant. -/
theorem starProjection_equivariant (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (F : Submodule ℝ E) [F.HasOrthogonalProjection] {g : G}
    (hg : ∀ z ∈ F, rho g z ∈ F) (hg' : ∀ z ∈ F, rho g⁻¹ z ∈ F) (z : E) :
    F.starProjection (rho g z) = rho g (F.starProjection z) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hg _ (F.starProjection_apply_mem z)
  · have hsub : rho g z - rho g (F.starProjection z)
        = rho g (z - F.starProjection z) := by rw [map_sub]
    rw [hsub]
    exact map_mem_orthogonal rho hg' (F.sub_starProjection_mem_orthogonal z)

/-- Orthogonal projections are self-adjoint. -/
theorem inner_starProjection_left (F : Submodule ℝ E)
    [F.HasOrthogonalProjection] (z w : E) :
    inner ℝ (F.starProjection z) w = inner ℝ z (F.starProjection w) := by
  have h1 : inner ℝ (F.starProjection z) (w - F.starProjection w) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (F.starProjection_apply_mem z)
      (F.sub_starProjection_mem_orthogonal w)
  have h2 : inner ℝ (F.starProjection w) (z - F.starProjection z) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (F.starProjection_apply_mem w)
      (F.sub_starProjection_mem_orthogonal z)
  rw [inner_sub_right] at h1 h2
  have h3 : inner ℝ (F.starProjection w) (F.starProjection z)
      = inner ℝ (F.starProjection z) (F.starProjection w) := real_inner_comm _ _
  have h4 : inner ℝ z (F.starProjection w)
      = inner ℝ (F.starProjection w) z := real_inner_comm _ _
  rw [h4]
  linarith

/-- A subgroup of the centre has a globally invariant fixed subspace. -/
theorem central_fixedSubspace_invariant (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (D : Subgroup G) (hD : D ≤ Subgroup.center G) (g : G) {z : E}
    (hz : z ∈ KazhdanFixedSpace.fixedSubspace rho D) :
    rho g z ∈ KazhdanFixedSpace.fixedSubspace rho D := by
  rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
  intro d hd
  have hdc : g * d = d * g := Subgroup.mem_center_iff.mp (hD hd) g
  have hzd : rho d z = z :=
    (KazhdanFixedSpace.mem_fixedSubspace_iff rho D z).mp hz d hd
  calc
    rho d (rho g z) = rho (d * g) z := (apply_mul rho d g z).symm
    _ = rho (g * d) z := by rw [hdc]
    _ = rho g (rho d z) := apply_mul rho g d z
    _ = rho g z := by rw [hzd]

/-! ### The two-term convex combination -/

/-- **Single-element angle bound.**  One element of `X` with nonpositive
correlation already produces the `1 / sqrt 2` bound.

This is the exponent-free replacement for the finite orbit average of
`FiniteClassTwoOrthogonality.norm_orbitAverage_sq_le_half_of_vanishing`:
instead of averaging over a finite group and counting the index of the
radical, the two-term average `(v + rho x⁻¹ v) / 2` is used. -/
theorem abs_inner_le_of_correlation_nonpos (rho : G →* (E ≃ₗᵢ[ℝ] E))
    (X : Subgroup G) {u v : E}
    (hu : u ∈ KazhdanFixedSpace.fixedSubspace rho X)
    {x : G} (hx : x ∈ X) (hcorr : inner ℝ (rho x v) v ≤ 0) :
    |inner ℝ u v| ≤ (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by
  have hux : rho x u = u :=
    (KazhdanFixedSpace.mem_fixedSubspace_iff rho X u).mp hu x hx
  have hcancel : rho x (rho x⁻¹ v) = v := apply_inv_apply rho x v
  have hshift : inner ℝ u (rho x⁻¹ v) = inner ℝ u v := by
    calc
      inner ℝ u (rho x⁻¹ v)
          = inner ℝ (rho x u) (rho x (rho x⁻¹ v)) :=
            ((rho x).inner_map_map u (rho x⁻¹ v)).symm
      _ = inner ℝ u v := by rw [hux, hcancel]
  have hcorr' : inner ℝ v (rho x⁻¹ v) = inner ℝ (rho x v) v := by
    calc
      inner ℝ v (rho x⁻¹ v)
          = inner ℝ (rho x v) (rho x (rho x⁻¹ v)) :=
            ((rho x).inner_map_map v (rho x⁻¹ v)).symm
      _ = inner ℝ (rho x v) v := by rw [hcancel]
  have hinner_w : inner ℝ u (v + rho x⁻¹ v) = 2 * inner ℝ u v := by
    rw [inner_add_right, hshift]
    ring
  have hnormw : ‖v + rho x⁻¹ v‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, hcorr', (rho x⁻¹).norm_map v]
    linarith
  have hcs : |inner ℝ u (v + rho x⁻¹ v)| ≤ ‖u‖ * ‖v + rho x⁻¹ v‖ :=
    abs_real_inner_le_norm u (v + rho x⁻¹ v)
  have h2 : 2 * |inner ℝ u v| ≤ ‖u‖ * ‖v + rho x⁻¹ v‖ := by
    have habs : |inner ℝ u (v + rho x⁻¹ v)| = 2 * |inner ℝ u v| := by
      rw [hinner_w, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← habs]
    exact hcs
  have hsq : |inner ℝ u v| ^ 2 ≤ (1 / 2 : ℝ) * (‖u‖ * ‖v‖) ^ 2 := by
    nlinarith [h2, hnormw, abs_nonneg (inner ℝ u v), norm_nonneg u,
      norm_nonneg v, norm_nonneg (v + rho x⁻¹ v),
      mul_nonneg (norm_nonneg u) (norm_nonneg (v + rho x⁻¹ v)),
      mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 * |inner ℝ u v|) h2,
      mul_le_mul_of_nonneg_left hnormw (sq_nonneg ‖u‖)]
  have hfinal := FiniteClassTwoOrthogonality.le_inv_sqrt_two_mul_of_sq_le_half
    (abs_nonneg (inner ℝ u v))
    (mul_nonneg (norm_nonneg u) (norm_nonneg v)) hsq
  rw [← mul_assoc] at hfinal
  exact hfinal

/-! ### Recombination across an orthogonal splitting -/

/-- An angle bound holding separately on a subspace and on its orthogonal
complement holds on the whole space. -/
theorem abs_inner_le_of_split (F : Submodule ℝ E) [F.HasOrthogonalProjection]
    {eps : ℝ} (heps : 0 ≤ eps) (u v : E)
    (h1 : |inner ℝ (F.starProjection u) (F.starProjection v)| ≤
      eps * ‖F.starProjection u‖ * ‖F.starProjection v‖)
    (h2 : |inner ℝ (u - F.starProjection u) (v - F.starProjection v)| ≤
      eps * ‖u - F.starProjection u‖ * ‖v - F.starProjection v‖) :
    |inner ℝ u v| ≤ eps * ‖u‖ * ‖v‖ := by
  have hcross1 : inner ℝ (F.starProjection u) (v - F.starProjection v) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (F.starProjection_apply_mem u)
      (F.sub_starProjection_mem_orthogonal v)
  have hcross2 : inner ℝ (F.starProjection v) (u - F.starProjection u) = 0 :=
    Submodule.inner_right_of_mem_orthogonal (F.starProjection_apply_mem v)
      (F.sub_starProjection_mem_orthogonal u)
  have hcross2' : inner ℝ (u - F.starProjection u) (F.starProjection v) = 0 := by
    rw [real_inner_comm]
    exact hcross2
  have hexpand : inner ℝ u v
      = inner ℝ (F.starProjection u) (F.starProjection v)
        + inner ℝ (u - F.starProjection u) (v - F.starProjection v) := by
    have e1 := hcross1
    have e2 := hcross2'
    simp only [inner_sub_left, inner_sub_right] at e1 e2 ⊢
    linarith
  have hpu : ‖u‖ ^ 2 = ‖F.starProjection u‖ ^ 2 + ‖u - F.starProjection u‖ ^ 2 := by
    have o1 : inner ℝ (u - F.starProjection u) (F.starProjection u) = 0 :=
      Submodule.inner_left_of_mem_orthogonal (F.starProjection_apply_mem u)
        (F.sub_starProjection_mem_orthogonal u)
    have o2 : inner ℝ (F.starProjection u) (u - F.starProjection u) = 0 :=
      Submodule.inner_right_of_mem_orthogonal (F.starProjection_apply_mem u)
        (F.sub_starProjection_mem_orthogonal u)
    have s1 : inner ℝ (u - F.starProjection u) (u - F.starProjection u)
        = ‖u - F.starProjection u‖ ^ 2 := real_inner_self_eq_norm_sq _
    have s2 : inner ℝ (F.starProjection u) (F.starProjection u)
        = ‖F.starProjection u‖ ^ 2 := real_inner_self_eq_norm_sq _
    have s3 : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
    simp only [inner_sub_left, inner_sub_right] at o1 o2 s1
    linarith
  have hpv : ‖v‖ ^ 2 = ‖F.starProjection v‖ ^ 2 + ‖v - F.starProjection v‖ ^ 2 := by
    have o1 : inner ℝ (v - F.starProjection v) (F.starProjection v) = 0 :=
      Submodule.inner_left_of_mem_orthogonal (F.starProjection_apply_mem v)
        (F.sub_starProjection_mem_orthogonal v)
    have o2 : inner ℝ (F.starProjection v) (v - F.starProjection v) = 0 :=
      Submodule.inner_right_of_mem_orthogonal (F.starProjection_apply_mem v)
        (F.sub_starProjection_mem_orthogonal v)
    have s1 : inner ℝ (v - F.starProjection v) (v - F.starProjection v)
        = ‖v - F.starProjection v‖ ^ 2 := real_inner_self_eq_norm_sq _
    have s2 : inner ℝ (F.starProjection v) (F.starProjection v)
        = ‖F.starProjection v‖ ^ 2 := real_inner_self_eq_norm_sq _
    have s3 : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    simp only [inner_sub_left, inner_sub_right] at o1 o2 s1
    linarith
  have hX : (0 : ℝ) ≤ ‖F.starProjection u‖ * ‖F.starProjection v‖
      + ‖u - F.starProjection u‖ * ‖v - F.starProjection v‖ := by positivity
  have hY : (0 : ℝ) ≤ ‖u‖ * ‖v‖ := by positivity
  have hsq : (‖F.starProjection u‖ * ‖F.starProjection v‖
      + ‖u - F.starProjection u‖ * ‖v - F.starProjection v‖) ^ 2
      ≤ (‖u‖ * ‖v‖) ^ 2 := by
    rw [mul_pow, hpu, hpv]
    nlinarith [sq_nonneg (‖F.starProjection u‖ * ‖v - F.starProjection v‖
      - ‖u - F.starProjection u‖ * ‖F.starProjection v‖)]
  have hcs : ‖F.starProjection u‖ * ‖F.starProjection v‖
      + ‖u - F.starProjection u‖ * ‖v - F.starProjection v‖ ≤ ‖u‖ * ‖v‖ :=
    (sq_le_sq₀ hX hY).mp hsq
  calc
    |inner ℝ u v| ≤ |inner ℝ (F.starProjection u) (F.starProjection v)|
        + |inner ℝ (u - F.starProjection u) (v - F.starProjection v)| := by
      rw [hexpand]
      exact abs_add_le _ _
    _ ≤ eps * ‖F.starProjection u‖ * ‖F.starProjection v‖
        + eps * ‖u - F.starProjection u‖ * ‖v - F.starProjection v‖ :=
      add_le_add h1 h2
    _ ≤ eps * ‖u‖ * ‖v‖ := by nlinarith [hcs, heps, hX, hY]

/-! ### The case of trivially represented commutators -/

/-- **Exactly orthogonal fixed spaces when the commutators act trivially.**
No finiteness, no exponent, and no commutativity of `X` or `Y` is used; the
hypothesis on `u` is the exponent-free substitute for "no invariant
vectors". -/
theorem inner_eq_zero_of_commutators_trivial [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G)
    (htriv : ∀ y ∈ Y, ∀ x ∈ X, rho ⁅y, x⁆ = 1) {u v : E}
    (hu : u ∈ KazhdanFixedSpace.fixedSubspace rho X)
    (hv : v ∈ KazhdanFixedSpace.fixedSubspace rho Y)
    (hu0 : u ∈ (KazhdanFixedSpace.fixedSubspace rho (X ⊔ Y))ᗮ) :
    inner ℝ u v = 0 := by
  haveI : CompleteSpace (KazhdanFixedSpace.fixedSubspace rho X) :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho X).completeSpace_coe
  have hcomm : ∀ y ∈ Y, ∀ x ∈ X, rho y * rho x = rho x * rho y := by
    intro y hy x hx
    have h1 : ⁅rho y, rho x⁆ = (1 : E ≃ₗᵢ[ℝ] E) := by
      rw [← map_commutatorElement]
      exact htriv y hy x hx
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hYinv : ∀ y ∈ Y, ∀ z ∈ KazhdanFixedSpace.fixedSubspace rho X,
      rho y z ∈ KazhdanFixedSpace.fixedSubspace rho X := by
    intro y hy z hz
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro x hx
    have hzx : rho x z = z :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho X z).mp hz x hx
    calc
      rho x (rho y z) = (rho x * rho y) z := rfl
      _ = (rho y * rho x) z := by rw [← hcomm y hy x hx]
      _ = rho y (rho x z) := rfl
      _ = rho y z := by rw [hzx]
  have hYinv' : ∀ y ∈ Y, ∀ z ∈ KazhdanFixedSpace.fixedSubspace rho X,
      rho y⁻¹ z ∈ KazhdanFixedSpace.fixedSubspace rho X := fun y hy ↦
    hYinv y⁻¹ (Y.inv_mem hy)
  have hPv_X : (KazhdanFixedSpace.fixedSubspace rho X).starProjection v
      ∈ KazhdanFixedSpace.fixedSubspace rho X :=
    Submodule.starProjection_apply_mem _ v
  have hPv_Y : (KazhdanFixedSpace.fixedSubspace rho X).starProjection v
      ∈ KazhdanFixedSpace.fixedSubspace rho Y := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro y hy
    have hvy : rho y v = v :=
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hv y hy
    rw [← starProjection_equivariant rho _ (hYinv y hy) (hYinv' y hy) v, hvy]
  have hPv_Z : (KazhdanFixedSpace.fixedSubspace rho X).starProjection v
      ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Y) := by
    rw [KazhdanFixedSpace.fixedSubspace_sup]
    exact ⟨hPv_X, hPv_Y⟩
  have h2 : inner ℝ u ((KazhdanFixedSpace.fixedSubspace rho X).starProjection v) = 0 :=
    Submodule.inner_left_of_mem_orthogonal hPv_Z hu0
  have h1 : inner ℝ u
      (v - (KazhdanFixedSpace.fixedSubspace rho X).starProjection v) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hu
      (Submodule.sub_starProjection_mem_orthogonal v)
  rw [inner_sub_right, h2, sub_zero] at h1
  exact h1

/-! ### The mean-ergodic core -/

/-- **Exponent-free vanishing of an invariant correlation.**

If translating `a` by any element of `D` leaves its correlation with `v`
unchanged, and `v` is orthogonal to every `D`-fixed vector, then that
correlation is zero.

For finite `D` this is the statement proved in
`FiniteClassTwoOrthogonality.inner_translate_eq_zero_of_not_mem_radical_of_irreducible`
by summing the finite cyclic orbit.  The argument here compares the closed
span `W` of the `D`-orbit of `v` with the closed span `Z` of its
displacements: any vector of `W` orthogonal to `Z` is `D`-fixed, so the
`Z`-residue of `v` is `D`-fixed, hence zero, hence `v` lies in `Z`, which is
orthogonal to `a`.  Only orthogonal complements are used, so no finiteness,
no compactness and no direct integral is needed. -/
theorem inner_eq_zero_of_translation_invariant [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (D : Subgroup G) {a v : E}
    (hconst : ∀ d ∈ D, inner ℝ (rho d a) v = inner ℝ a v)
    (hperp : v ∈ (KazhdanFixedSpace.fixedSubspace rho D)ᗮ) :
    inner ℝ a v = 0 := by
  classical
  set orbSet : Set E := {z : E | ∃ d ∈ D, rho d v = z}
  set difSet : Set E := {z : E | ∃ d ∈ D, rho d v - v = z}
  -- translation invariance in the second slot
  have hconst' : ∀ d ∈ D, inner ℝ a (rho d v) = inner ℝ a v := by
    intro d hd
    calc
      inner ℝ a (rho d v)
          = inner ℝ (rho d⁻¹ a) (rho d⁻¹ (rho d v)) :=
            ((rho d⁻¹).inner_map_map a (rho d v)).symm
      _ = inner ℝ (rho d⁻¹ a) v := by
            rw [show rho d⁻¹ (rho d v) = v by
              rw [← apply_mul, inv_mul_cancel, map_one]; rfl]
      _ = inner ℝ a v := hconst d⁻¹ (D.inv_mem hd)
  -- `a` is orthogonal to the displacements
  have ha_perp : a ∈ (Submodule.span ℝ difSet)ᗮ := by
    rw [mem_span_orthogonal_iff]
    rintro y ⟨d, hd, rfl⟩
    rw [real_inner_comm, inner_sub_right, hconst' d hd, sub_self]
  have hv_orb : v ∈ Submodule.span ℝ orbSet := by
    refine Submodule.subset_span ⟨1, D.one_mem, ?_⟩
    simp
  -- the displacement span sits inside the orbit span
  have hdif_le : Submodule.span ℝ difSet ≤ Submodule.span ℝ orbSet := by
    rw [Submodule.span_le]
    rintro z ⟨d, hd, rfl⟩
    exact (Submodule.span ℝ orbSet).sub_mem
      (Submodule.subset_span ⟨d, hd, rfl⟩) hv_orb
  have hMN : (Submodule.span ℝ orbSet)ᗮ ≤ (Submodule.span ℝ difSet)ᗮ :=
    Submodule.orthogonal_le hdif_le
  -- split `v` along the displacement complement
  haveI : CompleteSpace ((Submodule.span ℝ difSet)ᗮ) :=
    (Submodule.isClosed_orthogonal (Submodule.span ℝ difSet)).completeSpace_coe
  obtain ⟨r, hrN, hvr⟩ :=
    Submodule.HasOrthogonalProjection.exists_orthogonal
      (K := (Submodule.span ℝ difSet)ᗮ) v
  have hv_mem : v ∈ ((Submodule.span ℝ orbSet)ᗮ)ᗮ :=
    Submodule.le_orthogonal_orthogonal (Submodule.span ℝ orbSet) hv_orb
  have hr_mem : r ∈ ((Submodule.span ℝ orbSet)ᗮ)ᗮ := by
    have h1 : v - r ∈ ((Submodule.span ℝ orbSet)ᗮ)ᗮ :=
      Submodule.orthogonal_le hMN hvr
    have h2 : r = v - (v - r) := by abel
    rw [h2]
    exact Submodule.sub_mem _ hv_mem h1
  -- correlations of `r` against the orbit are constant
  have hr_orb : ∀ d ∈ D, inner ℝ (rho d v) r = inner ℝ v r := by
    intro d hd
    have h : inner ℝ (rho d v - v) r = 0 :=
      (Submodule.mem_orthogonal _ _).mp hrN _
        (Submodule.subset_span ⟨d, hd, rfl⟩)
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have hshift : ∀ (d e : G), rho e v = rho d (rho (d⁻¹ * e) v) := by
    intro d e
    rw [← apply_mul, ← mul_assoc, mul_inv_cancel, one_mul]
  -- `D` preserves the orbit complement and its double complement
  have hM_inv : ∀ d ∈ D, ∀ z ∈ (Submodule.span ℝ orbSet)ᗮ,
      rho d z ∈ (Submodule.span ℝ orbSet)ᗮ := by
    intro d hd z hz
    rw [mem_span_orthogonal_iff]
    rintro y ⟨e, he, rfl⟩
    rw [hshift d e, (rho d).inner_map_map]
    exact (Submodule.mem_orthogonal _ _).mp hz _
      (Submodule.subset_span ⟨d⁻¹ * e, D.mul_mem (D.inv_mem hd) he, rfl⟩)
  have hMperp_inv : ∀ d ∈ D, ∀ z ∈ ((Submodule.span ℝ orbSet)ᗮ)ᗮ,
      rho d z ∈ ((Submodule.span ℝ orbSet)ᗮ)ᗮ := by
    intro d hd z hz
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hy' : rho d⁻¹ y ∈ (Submodule.span ℝ orbSet)ᗮ :=
      hM_inv d⁻¹ (D.inv_mem hd) y hy
    calc
      inner ℝ y (rho d z) = inner ℝ (rho d (rho d⁻¹ y)) (rho d z) := by
        rw [apply_inv_apply rho d y]
      _ = inner ℝ (rho d⁻¹ y) z := (rho d).inner_map_map _ _
      _ = 0 := (Submodule.mem_orthogonal _ _).mp hz _ hy'
  -- the residue is `D`-fixed
  have hr_fixed : r ∈ KazhdanFixedSpace.fixedSubspace rho D := by
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro d hd
    have hdiff_M : rho d r - r ∈ (Submodule.span ℝ orbSet)ᗮ := by
      rw [mem_span_orthogonal_iff]
      rintro y ⟨e, he, rfl⟩
      have hde : d⁻¹ * e ∈ D := D.mul_mem (D.inv_mem hd) he
      have hA : inner ℝ (rho e v) (rho d r) = inner ℝ v r := by
        calc
          inner ℝ (rho e v) (rho d r)
              = inner ℝ (rho d (rho (d⁻¹ * e) v)) (rho d r) := by
                rw [hshift d e]
          _ = inner ℝ (rho (d⁻¹ * e) v) r := (rho d).inner_map_map _ _
          _ = inner ℝ v r := hr_orb (d⁻¹ * e) hde
      rw [inner_sub_right, hA, hr_orb e he, sub_self]
    have hdiff_Mperp : rho d r - r ∈ ((Submodule.span ℝ orbSet)ᗮ)ᗮ :=
      Submodule.sub_mem _ (hMperp_inv d hd r hr_mem) hr_mem
    have hzero : inner ℝ (rho d r - r) (rho d r - r) = 0 :=
      Submodule.inner_right_of_mem_orthogonal hdiff_M hdiff_Mperp
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  -- hence the residue vanishes and `v` lies in the displacement closure
  have hrv : inner ℝ r v = 0 :=
    Submodule.inner_right_of_mem_orthogonal hr_fixed hperp
  have hrr : inner ℝ r (v - r) = 0 :=
    Submodule.inner_right_of_mem_orthogonal hrN hvr
  have hr0 : r = 0 := by
    rw [inner_sub_right, hrv, zero_sub, neg_eq_zero] at hrr
    exact inner_self_eq_zero.mp hrr
  have hvN : v ∈ ((Submodule.span ℝ difSet)ᗮ)ᗮ := by
    rw [show v = v - r by rw [hr0, sub_zero]]
    exact hvr
  exact Submodule.inner_right_of_mem_orthogonal ha_perp hvN

/-! ### Bimultiplicativity of central commutators -/

/-- With `⁅b, c⁆` central the commutator is multiplicative in its left
argument. -/
theorem commutatorElement_mul_left_of_central {a b c : G}
    (h : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  congr 1
  rw [Subgroup.mem_center_iff.mp h a]
  group

/-- With `⁅a, c⁆` central the commutator is multiplicative in its right
argument. -/
theorem commutatorElement_mul_right_of_central {a b c : G}
    (h : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj,
    show ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆) * b⁻¹ by group,
    Subgroup.mem_center_iff.mp h b]
  group

/-- With `⁅a, b⁆` central, inverting the left argument inverts the
commutator. -/
theorem commutatorElement_inv_left_of_central {a b : G}
    (h : ⁅a, b⁆ ∈ Subgroup.center G) : ⁅a⁻¹, b⁆ = ⁅a, b⁆⁻¹ := by
  have h' : ⁅b, a⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center G).inv_mem h
  rw [commutatorElement_inv_left, Subgroup.mem_center_iff.mp h' a⁻¹]
  simp [mul_assoc]

/-- With `⁅a, b⁆` central, inverting the right argument inverts the
commutator. -/
theorem commutatorElement_inv_right_of_central {a b : G}
    (h : ⁅a, b⁆ ∈ Subgroup.center G) : ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  have h' : ⁅b, a⁆ ∈ Subgroup.center G := by
    rw [← commutatorElement_inv]
    exact (Subgroup.center G).inv_mem h
  rw [commutatorElement_inv_right, Subgroup.mem_center_iff.mp h' b⁻¹]
  simp [mul_assoc]

/-- Every element of the subgroup generated by a single central commutator
`⁅y, x⁆` is itself a commutator `⁅w, x⁆` with `w ∈ Y`. -/
theorem exists_commutator_of_mem_closure (Y : Subgroup G) {y x : G}
    (hy : y ∈ Y) (hcent : ∀ w ∈ Y, ⁅w, x⁆ ∈ Subgroup.center G) :
    ∀ d ∈ Subgroup.closure ({⁅y, x⁆} : Set G), ∃ w ∈ Y, ⁅w, x⁆ = d := by
  intro d hd
  induction hd using Subgroup.closure_induction with
  | mem a ha =>
      rw [Set.mem_singleton_iff] at ha
      exact ⟨y, hy, ha.symm⟩
  | one => exact ⟨1, Y.one_mem, commutatorElement_one_left x⟩
  | mul a b _ _ iha ihb =>
      obtain ⟨wa, hwa, hea⟩ := iha
      obtain ⟨wb, hwb, heb⟩ := ihb
      refine ⟨wb * wa, Y.mul_mem hwb hwa, ?_⟩
      rw [commutatorElement_mul_left_of_central (hcent wa hwa), hea, heb]
  | inv a _ iha =>
      obtain ⟨w, hw, he⟩ := iha
      refine ⟨w⁻¹, Y.inv_mem hw, ?_⟩
      rw [commutatorElement_inv_left_of_central (hcent w hw), he]

/-- **The correlation of a `Y`-fixed vector with its `x`-translate
vanishes** as soon as the vector is orthogonal to everything fixed by the
central commutator `⁅y, x⁆`. -/
theorem inner_translate_eq_zero [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (Y : Subgroup G) {y x : G} (hy : y ∈ Y)
    (hcent : ∀ w ∈ Y, ⁅w, x⁆ ∈ Subgroup.center G) {v : E}
    (hv : v ∈ KazhdanFixedSpace.fixedSubspace rho Y)
    (hperp : v ∈ (KazhdanFixedSpace.fixedSubspace rho
      (Subgroup.closure ({⁅y, x⁆} : Set G)))ᗮ) :
    inner ℝ (rho x v) v = 0 := by
  refine inner_eq_zero_of_translation_invariant rho
    (Subgroup.closure ({⁅y, x⁆} : Set G)) ?_ hperp
  intro d hd
  obtain ⟨w, hw, hwd⟩ := exists_commutator_of_mem_closure Y hy hcent d hd
  have hwv : rho w v = v :=
    (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hv w hw
  have hwinv : rho w⁻¹ v = v :=
    (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v).mp hv w⁻¹ (Y.inv_mem hw)
  have hconj : d * x = w * x * w⁻¹ := by
    rw [← hwd, ← conj_eq_commutatorElement_mul]
    rfl
  calc
    inner ℝ (rho d (rho x v)) v = inner ℝ (rho (d * x) v) v := by
      rw [apply_mul]
    _ = inner ℝ (rho (w * x * w⁻¹) v) v := by rw [hconj]
    _ = inner ℝ (rho w (rho x (rho w⁻¹ v))) v := by
      rw [apply_mul, apply_mul]
    _ = inner ℝ (rho w (rho x v)) (rho w v) := by rw [hwinv, hwv]
    _ = inner ℝ (rho x v) v := (rho w).inner_map_map _ _

/-! ### One splitting step -/

/-- **Splitting off one central subgroup.**  The bound on the `D`-fixed part
comes from the recursion hypothesis; the bound on its orthogonal complement
comes from the two-term convex combination, because there the correlation
with `rho x` vanishes. -/
theorem abs_inner_le_of_invariant_split [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y D : Subgroup G) {x : G} (hx : x ∈ X)
    (hD : D ≤ Subgroup.center G)
    (hzero : ∀ w ∈ KazhdanFixedSpace.fixedSubspace rho Y,
      w ∈ (KazhdanFixedSpace.fixedSubspace rho D)ᗮ →
      inner ℝ (rho x w) w = 0)
    {u v : E}
    (hu : u ∈ KazhdanFixedSpace.fixedSubspace rho X)
    (hv : v ∈ KazhdanFixedSpace.fixedSubspace rho Y)
    (hu0 : u ∈ (KazhdanFixedSpace.fixedSubspace rho (X ⊔ Y))ᗮ)
    (hrec : ∀ u' ∈ KazhdanFixedSpace.fixedSubspace rho D,
      ∀ v' ∈ KazhdanFixedSpace.fixedSubspace rho D,
      u' ∈ KazhdanFixedSpace.fixedSubspace rho X →
      v' ∈ KazhdanFixedSpace.fixedSubspace rho Y →
      u' ∈ (KazhdanFixedSpace.fixedSubspace rho (X ⊔ Y))ᗮ →
      |inner ℝ u' v'| ≤ (Real.sqrt 2)⁻¹ * ‖u'‖ * ‖v'‖) :
    |inner ℝ u v| ≤ (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by
  haveI : CompleteSpace (KazhdanFixedSpace.fixedSubspace rho D) :=
    (KazhdanFixedSpace.isClosed_fixedSubspace rho D).completeSpace_coe
  have hinv : ∀ g : G, ∀ z ∈ KazhdanFixedSpace.fixedSubspace rho D,
      rho g z ∈ KazhdanFixedSpace.fixedSubspace rho D := fun g z hz ↦
    central_fixedSubspace_invariant rho D hD g hz
  -- the projection preserves membership in each relevant subspace
  have hfix : ∀ (H : Subgroup G) (z : E),
      z ∈ KazhdanFixedSpace.fixedSubspace rho H →
      (KazhdanFixedSpace.fixedSubspace rho D).starProjection z
        ∈ KazhdanFixedSpace.fixedSubspace rho H := by
    intro H z hz
    rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
    intro g hg
    rw [← starProjection_equivariant rho _ (hinv g) (hinv g⁻¹) z,
      (KazhdanFixedSpace.mem_fixedSubspace_iff rho H z).mp hz g hg]
  have hu0' : (KazhdanFixedSpace.fixedSubspace rho D).starProjection u
      ∈ (KazhdanFixedSpace.fixedSubspace rho (X ⊔ Y))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [← inner_starProjection_left]
    exact Submodule.inner_right_of_mem_orthogonal (hfix (X ⊔ Y) z hz) hu0
  have huX : u - (KazhdanFixedSpace.fixedSubspace rho D).starProjection u
      ∈ KazhdanFixedSpace.fixedSubspace rho X :=
    Submodule.sub_mem _ hu (hfix X u hu)
  have hvY : v - (KazhdanFixedSpace.fixedSubspace rho D).starProjection v
      ∈ KazhdanFixedSpace.fixedSubspace rho Y :=
    Submodule.sub_mem _ hv (hfix Y v hv)
  have hcorr : inner ℝ
      (rho x (v - (KazhdanFixedSpace.fixedSubspace rho D).starProjection v))
      (v - (KazhdanFixedSpace.fixedSubspace rho D).starProjection v) = 0 :=
    hzero _ hvY (Submodule.sub_starProjection_mem_orthogonal v)
  refine abs_inner_le_of_split (KazhdanFixedSpace.fixedSubspace rho D)
    (by positivity) u v ?_ ?_
  · exact hrec _ (Submodule.starProjection_apply_mem _ u) _
      (Submodule.starProjection_apply_mem _ v) (hfix X u hu) (hfix Y v hv) hu0'
  · exact abs_inner_le_of_correlation_nonpos rho X huX hx (le_of_eq hcorr)

/-! ### The induction over a finite list of commutator generators -/

/-- **The exponent-free angle bound for a finitely commutator-generated
class-two pair.**

`L` lists finitely many pairs whose commutators, together with the kernel of
the representation, generate every commutator `⁅y, x⁆`.  The induction splits
off one list entry at a time: on the orthogonal complement of the fixed space
of that entry the two-term convex combination gives the bound outright, and
on the fixed space itself the entry joins the kernel and the list shortens.
When the list is empty every commutator acts trivially and the two fixed
spaces are exactly orthogonal.

Neither a bounded exponent nor finiteness nor commutativity of `X` and `Y`
appears anywhere. -/
theorem abs_inner_le_of_commutatorList (X Y : Subgroup G)
    (hcentral : ⁅Y, X⁆ ≤ Subgroup.center G) :
    ∀ (L : List (G × G)), (∀ p ∈ L, p.1 ∈ Y ∧ p.2 ∈ X) →
      ∀ (F : Type v) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
        [CompleteSpace F] (rho : G →* (F ≃ₗᵢ[ℝ] F)),
        (∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈
          Subgroup.closure {g : G | ∃ q ∈ L, ⁅q.1, q.2⁆ = g} ⊔ rho.ker) →
        ∀ u ∈ KazhdanFixedSpace.fixedSubspace rho X,
        ∀ v ∈ KazhdanFixedSpace.fixedSubspace rho Y,
          u ∈ (KazhdanFixedSpace.fixedSubspace rho (X ⊔ Y))ᗮ →
          |inner ℝ u v| ≤ (Real.sqrt 2)⁻¹ * ‖u‖ * ‖v‖ := by
  intro L
  induction L with
  | nil =>
      intro _hL F _iA _iB _iC rho hker u hu v hv hu0
      have hset : {g : G | ∃ q ∈ ([] : List (G × G)), ⁅q.1, q.2⁆ = g}
          = (∅ : Set G) := by
        ext g
        simp
      have htriv : ∀ y ∈ Y, ∀ x ∈ X, rho ⁅y, x⁆ = 1 := by
        intro y hy x hx
        have h := hker y hy x hx
        rw [hset, Subgroup.closure_empty, bot_sup_eq, MonoidHom.mem_ker] at h
        exact h
      rw [inner_eq_zero_of_commutators_trivial rho X Y htriv hu hv hu0]
      rw [abs_zero]
      positivity
  | cons p L ih =>
      intro hL F _iA _iB _iC rho hker u hu v hv hu0
      obtain ⟨hp1, hp2⟩ := hL p (List.mem_cons.mpr (Or.inl rfl))
      have hLtail : ∀ q ∈ L, q.1 ∈ Y ∧ q.2 ∈ X := fun q hq ↦
        hL q (List.mem_cons.mpr (Or.inr hq))
      have hcent : ∀ w ∈ Y, ⁅w, p.2⁆ ∈ Subgroup.center G := fun w hw ↦
        hcentral (Subgroup.commutator_mem_commutator hw hp2)
      have hDle : Subgroup.closure ({⁅p.1, p.2⁆} : Set G)
          ≤ Subgroup.center G := by
        rw [Subgroup.closure_le]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact hcent p.1 hp1
      refine abs_inner_le_of_invariant_split rho X Y
        (Subgroup.closure ({⁅p.1, p.2⁆} : Set G)) hp2 hDle
        (fun w hw hw' ↦ inner_translate_eq_zero rho Y hp1 hcent hw hw')
        hu hv hu0 ?_
      intro u' hu'D v' hv'D hu'X hv'Y hu'0
      -- restrict everything to the fixed space of the split-off commutator
      haveI : CompleteSpace (KazhdanFixedSpace.fixedSubspace rho
          (Subgroup.closure ({⁅p.1, p.2⁆} : Set G))) :=
        (KazhdanFixedSpace.isClosed_fixedSubspace rho _).completeSpace_coe
      have hinvFc : ∀ g : G, ∀ z ∈ KazhdanFixedSpace.fixedSubspace rho
          (Subgroup.closure ({⁅p.1, p.2⁆} : Set G)),
          rho g z ∈ KazhdanFixedSpace.fixedSubspace rho
            (Subgroup.closure ({⁅p.1, p.2⁆} : Set G)) := fun g z hz ↦
        central_fixedSubspace_invariant rho _ hDle g hz
      set rho' := KazhdanFixedSpace.restrictToInvariantSubspace rho
        (KazhdanFixedSpace.fixedSubspace rho
          (Subgroup.closure ({⁅p.1, p.2⁆} : Set G))) hinvFc
      have hcoe : ∀ (g : G) (z : KazhdanFixedSpace.fixedSubspace rho
          (Subgroup.closure ({⁅p.1, p.2⁆} : Set G))),
          ((rho' g z : KazhdanFixedSpace.fixedSubspace rho
            (Subgroup.closure ({⁅p.1, p.2⁆} : Set G))) : F) = rho g z.1 :=
        fun g z ↦ rfl
      have hkerle : rho.ker ≤ rho'.ker := by
        intro g hg
        rw [MonoidHom.mem_ker] at hg ⊢
        ext z
        rw [hcoe g z, hg]
        rfl
      have hcker : ⁅p.1, p.2⁆ ∈ rho'.ker := by
        rw [MonoidHom.mem_ker]
        ext z
        rw [hcoe ⁅p.1, p.2⁆ z]
        exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho _ (z : F)).mp z.2 _
          (Subgroup.subset_closure (Set.mem_singleton_iff.mpr rfl))
      have hle : Subgroup.closure {g : G | ∃ q ∈ p :: L, ⁅q.1, q.2⁆ = g}
            ⊔ rho.ker
          ≤ Subgroup.closure {g : G | ∃ q ∈ L, ⁅q.1, q.2⁆ = g} ⊔ rho'.ker := by
        apply sup_le
        · rw [Subgroup.closure_le]
          rintro g ⟨q, hq, rfl⟩
          rcases List.mem_cons.mp hq with hqp | hqL
          · subst hqp
            exact Subgroup.mem_sup_right hcker
          · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨q, hqL, rfl⟩)
        · exact hkerle.trans le_sup_right
      have hker' : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈
          Subgroup.closure {g : G | ∃ q ∈ L, ⁅q.1, q.2⁆ = g} ⊔ rho'.ker :=
        fun y hy x hx ↦ hle (hker y hy x hx)
      have hu'' : (⟨u', hu'D⟩ : KazhdanFixedSpace.fixedSubspace rho
          (Subgroup.closure ({⁅p.1, p.2⁆} : Set G)))
          ∈ KazhdanFixedSpace.fixedSubspace rho' X := by
        rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
        intro g hg
        apply Subtype.ext
        rw [hcoe g ⟨u', hu'D⟩]
        exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho X u').mp hu'X g hg
      have hv'' : (⟨v', hv'D⟩ : KazhdanFixedSpace.fixedSubspace rho
          (Subgroup.closure ({⁅p.1, p.2⁆} : Set G)))
          ∈ KazhdanFixedSpace.fixedSubspace rho' Y := by
        rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
        intro g hg
        apply Subtype.ext
        rw [hcoe g ⟨v', hv'D⟩]
        exact (KazhdanFixedSpace.mem_fixedSubspace_iff rho Y v').mp hv'Y g hg
      have hu''0 : (⟨u', hu'D⟩ : KazhdanFixedSpace.fixedSubspace rho
          (Subgroup.closure ({⁅p.1, p.2⁆} : Set G)))
          ∈ (KazhdanFixedSpace.fixedSubspace rho' (X ⊔ Y))ᗮ := by
        rw [Submodule.mem_orthogonal]
        intro z hz
        have hzE : (z : F) ∈ KazhdanFixedSpace.fixedSubspace rho (X ⊔ Y) := by
          rw [KazhdanFixedSpace.mem_fixedSubspace_iff]
          intro g hg
          have hgz := (KazhdanFixedSpace.mem_fixedSubspace_iff rho' (X ⊔ Y) z).mp
            hz g hg
          rw [← hcoe g z, hgz]
        -- the submodule carries the restricted inner product, so it is
        -- enough to know the ambient one vanishes
        have hzu : (inner ℝ (z : F) (u' : F) : ℝ) = 0 :=
          Submodule.inner_right_of_mem_orthogonal hzE hu'0
        simpa [Submodule.coe_inner] using hzu
      exact ih hLtail _ rho' hker' _ hu'' _ hv'' hu''0

/-! ### Central commutators are generated by generator commutators -/

/-- When all commutators `⁅Y, X⁆` are central the commutator map is
bimultiplicative, so every `⁅y, x⁆` lies in the subgroup generated by the
commutators of chosen generating sets.  This is what supplies the finite
list consumed by `abs_inner_le_of_commutatorList`. -/
theorem commutator_mem_closure_of_generators (X Y : Subgroup G) (S T : Set G)
    (hX : Subgroup.closure S = X) (hY : Subgroup.closure T = Y)
    (hcentral : ⁅Y, X⁆ ≤ Subgroup.center G) :
    ∀ y ∈ Y, ∀ x ∈ X,
      ⁅y, x⁆ ∈ Subgroup.closure {g : G | ∃ t ∈ T, ∃ s ∈ S, ⁅t, s⁆ = g} := by
  have hcen : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ Subgroup.center G :=
    fun y hy x hx ↦ hcentral (Subgroup.commutator_mem_commutator hy hx)
  have key : ∀ s ∈ S, ∀ y ∈ Y,
      ⁅y, s⁆ ∈ Subgroup.closure {g : G | ∃ t ∈ T, ∃ s ∈ S, ⁅t, s⁆ = g} := by
    intro s hs
    have hsX : s ∈ X := by rw [← hX]; exact Subgroup.subset_closure hs
    have hsub : ∀ y ∈ Subgroup.closure T, y ∈ Y ∧
        ⁅y, s⁆ ∈ Subgroup.closure {g : G | ∃ t ∈ T, ∃ s ∈ S, ⁅t, s⁆ = g} := by
      intro y hyc
      induction hyc using Subgroup.closure_induction with
      | mem t ht =>
          refine ⟨by rw [← hY]; exact Subgroup.subset_closure ht, ?_⟩
          exact Subgroup.subset_closure ⟨t, ht, s, hs, rfl⟩
      | one =>
          refine ⟨Y.one_mem, ?_⟩
          rw [commutatorElement_one_left]
          exact Subgroup.one_mem _
      | mul a b _ _ iha ihb =>
          refine ⟨Y.mul_mem iha.1 ihb.1, ?_⟩
          rw [commutatorElement_mul_left_of_central (hcen b ihb.1 s hsX)]
          exact Subgroup.mul_mem _ ihb.2 iha.2
      | inv a _ iha =>
          refine ⟨Y.inv_mem iha.1, ?_⟩
          rw [commutatorElement_inv_left_of_central (hcen a iha.1 s hsX)]
          exact Subgroup.inv_mem _ iha.2
    intro y hy
    exact (hsub y (by rw [hY]; exact hy)).2
  intro y hy x hx
  have hsub : ∀ z ∈ Subgroup.closure S, z ∈ X ∧
      ⁅y, z⁆ ∈ Subgroup.closure {g : G | ∃ t ∈ T, ∃ s ∈ S, ⁅t, s⁆ = g} := by
    intro z hzc
    induction hzc using Subgroup.closure_induction with
    | mem s hs =>
        exact ⟨by rw [← hX]; exact Subgroup.subset_closure hs, key s hs y hy⟩
    | one =>
        refine ⟨X.one_mem, ?_⟩
        rw [commutatorElement_one_right]
        exact Subgroup.one_mem _
    | mul a b _ _ iha ihb =>
        refine ⟨X.mul_mem iha.1 ihb.1, ?_⟩
        rw [commutatorElement_mul_right_of_central (hcen y hy b ihb.1)]
        exact Subgroup.mul_mem _ iha.2 ihb.2
    | inv a _ iha =>
        refine ⟨X.inv_mem iha.1, ?_⟩
        rw [commutatorElement_inv_right_of_central (hcen y hy a iha.1)]
        exact Subgroup.inv_mem _ iha.2
  exact (hsub x (by rw [hX]; exact hx)).2

/-! ### The exponent-free theorem -/

/-- **Exponent-free class-two fixed-space orthogonality.**

This is `ClassTwoOrthogonality.epsilonOrthogonal` with the exponent
hypotheses `hXexp`, `hYexp`, `hCexp` deleted — and with the commutativity
hypotheses `hXcomm`, `hYcomm` deleted as well, since they were only ever
used to make the finite stages finite.

The directed-limit reduction of `ClassTwoApproximation` replaces `X` and `Y`
by finitely generated stages, `commutator_mem_closure_of_generators` turns
their generators into a finite list of commutators, and
`abs_inner_le_of_commutatorList` runs the exponent-free induction over that
list. -/
theorem epsilonOrthogonality [CompleteSpace E]
    (rho : G →* (E ≃ₗᵢ[ℝ] E)) (X Y : Subgroup G)
    (hgen : X ⊔ Y = ⊤)
    (hcentral : ⁅Y, X⁆ ≤ Subgroup.center G)
    (hno : IsKazhdanPair.HasNoInvariantVectors G rho) :
    HilbertEpsilonOrthogonality.EpsilonOrthogonal
      (KazhdanFixedSpace.fixedSubspace rho X)
      (KazhdanFixedSpace.fixedSubspace rho Y)
      (Real.sqrt 2)⁻¹ := by
  apply ClassTwoApproximation.epsilonOrthogonal_of_stage_estimates
    rho X Y hgen hno
  intro a u hu v hv
  obtain ⟨S, hS⟩ := ClassTwoApproximation.leftStage_fg X Y a
  obtain ⟨T, hT⟩ := ClassTwoApproximation.rightStage_fg X Y a
  have hcent0 : ⁅ClassTwoApproximation.rightStage X Y a,
      ClassTwoApproximation.leftStage X Y a⁆ ≤ Subgroup.center G :=
    le_trans (Subgroup.commutator_mono
      (ClassTwoApproximation.rightStage_le X Y a)
      (ClassTwoApproximation.leftStage_le X Y a)) hcentral
  have hstage : ClassTwoApproximation.leftStage X Y a
      ⊔ ClassTwoApproximation.rightStage X Y a
      = ClassTwoApproximation.stageGroup X Y a := rfl
  -- the finite list of commutator pairs
  have hLmem : ∀ q ∈ (T ×ˢ S).toList,
      q.1 ∈ ClassTwoApproximation.rightStage X Y a ∧
      q.2 ∈ ClassTwoApproximation.leftStage X Y a := by
    intro q hq
    rw [Finset.mem_toList] at hq
    simp only [Finset.mem_product] at hq
    refine ⟨?_, ?_⟩
    · rw [← hT]
      exact Subgroup.subset_closure (Finset.mem_coe.mpr hq.1)
    · rw [← hS]
      exact Subgroup.subset_closure (Finset.mem_coe.mpr hq.2)
  have hsub : {g : G | ∃ t ∈ (T : Set G), ∃ s ∈ (S : Set G), ⁅t, s⁆ = g}
      ⊆ {g : G | ∃ q ∈ (T ×ˢ S).toList, ⁅q.1, q.2⁆ = g} := by
    rintro g ⟨t, ht, s, hs, rfl⟩
    refine ⟨(t, s), ?_, rfl⟩
    rw [Finset.mem_toList]
    simp only [Finset.mem_product]
    exact ⟨Finset.mem_coe.mp ht, Finset.mem_coe.mp hs⟩
  have hker : ∀ y ∈ ClassTwoApproximation.rightStage X Y a,
      ∀ x ∈ ClassTwoApproximation.leftStage X Y a,
      ⁅y, x⁆ ∈ Subgroup.closure
        {g : G | ∃ q ∈ (T ×ˢ S).toList, ⁅q.1, q.2⁆ = g} ⊔ rho.ker := by
    intro y hy x hx
    have hmem := Subgroup.closure_mono hsub
      (commutator_mem_closure_of_generators _ _ (S : Set G) (T : Set G)
        hS hT hcent0 y hy x hx)
    exact Subgroup.mem_sup_left hmem
  -- the projected vectors
  have hpuX : KazhdanFixedSpace.subgroupMovingProjection rho
      (ClassTwoApproximation.stageGroup X Y a) u
      ∈ KazhdanFixedSpace.fixedSubspace rho
        (ClassTwoApproximation.leftStage X Y a) :=
    KazhdanFixedSpace.subgroupMovingProjection_mem_fixedSubspace rho _ _
      le_sup_left
      (KazhdanFixedSpace.antitone rho
        (ClassTwoApproximation.leftStage_le X Y a) hu)
  have hpvY : KazhdanFixedSpace.subgroupMovingProjection rho
      (ClassTwoApproximation.stageGroup X Y a) v
      ∈ KazhdanFixedSpace.fixedSubspace rho
        (ClassTwoApproximation.rightStage X Y a) :=
    KazhdanFixedSpace.subgroupMovingProjection_mem_fixedSubspace rho _ _
      le_sup_right
      (KazhdanFixedSpace.antitone rho
        (ClassTwoApproximation.rightStage_le X Y a) hv)
  have hpu0 : KazhdanFixedSpace.subgroupMovingProjection rho
      (ClassTwoApproximation.stageGroup X Y a) u
      ∈ (KazhdanFixedSpace.fixedSubspace rho
        (ClassTwoApproximation.leftStage X Y a
          ⊔ ClassTwoApproximation.rightStage X Y a))ᗮ := by
    rw [hstage]
    simpa [KazhdanFixedSpace.subgroupMovingSubspace] using
      KazhdanFixedSpace.subgroupMovingProjection_mem rho
        (ClassTwoApproximation.stageGroup X Y a) u
  exact abs_inner_le_of_commutatorList
    (ClassTwoApproximation.leftStage X Y a)
    (ClassTwoApproximation.rightStage X Y a) hcent0 ((T ×ˢ S).toList) hLmem
    E rho hker _ hpuX _ hpvY hpu0

end ExponentFreeClassTwoOrthogonality
end GroupApproximation
