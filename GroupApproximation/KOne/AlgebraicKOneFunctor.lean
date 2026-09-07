import GroupApproximation.KOne.AlgebraicKOne

/-!
# `K₁` is functorial, and Morita invariance for a self-similar ring

`non_mf_groups_exist.tex`, inside the proof of `thm:mf-quotient-units`:

> The ring `M_n(R)` is again countable, purely infinite, and simple, and
> `K_1(M_n(R)) ≅ K_1(R)` by Morita invariance, so it suffices to treat `n = 1`.

`Manuscript/OneSidedMFRadical/MFQuotientUnitsKOne.lean` states that Morita step
as the hypothesis `MoritaKOne` and does not prove it: in general it is a
cofinality argument about direct limits, since `K₁(M_n(R))` is the colimit of
`GL_m(M_n(R)) ≅ GL_{mn}(R)`, a cofinal subsystem of the colimit defining
`K₁(R)`.

This module proves the case the manuscript actually consumes, by a different and
much shorter route.  Where `R ≅ M_n(R)` **as a ring** — which is exactly the
situation of `cor:leavitt-mf-quotient`, since `L_k(1,d)` satisfies
`R ≅ M_d(R)` — Morita invariance is not a cofinality statement at all: it is
functoriality of `K₁` applied to that ring isomorphism.  So the content needed
here is that a ring isomorphism induces an isomorphism of `K₁`, which is what
this module supplies.

## What it takes

Three compatibilities, each with its ingredient already in the tree:

* padding commutes with entrywise coefficient maps (`stabMatrix_map`), an entry
  check on `padEntry`;
* hence the coefficient maps assemble into a map of colimits (`glColimMap`),
  through Mathlib's `DirectLimit.map`;
* and they carry elementary subgroups into elementary subgroups
  (`elementaryColim_map_le`), from `elementaryGroup_map_le` of
  `Leavitt/ElementaryGroup.lean`.

For an isomorphism the two directions are mutually inverse, so the induced map
of colimits is an isomorphism carrying `E_∞` onto `E_∞`, and it descends.

## What is not proved

Morita invariance for a general ring: `MoritaKOne` remains open.  Only the
self-similar case is closed here, and `moritaKOne_of_selfSimilar` says exactly
that.
-/

namespace GroupApproximation
namespace AlgebraicK

section Functor

variable {R S : Type*} [Ring R] [Ring S]

/-! ### Padding commutes with coefficient maps -/

theorem padEntry_map (f : R →+* S) {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (x y : ℕ) : padEntry (A.map f) x y = f (padEntry A x y) := by
  by_cases hx : x < n
  · by_cases hy : y < n
    · rw [padEntry_of_lt_lt (A.map f) hx hy, padEntry_of_lt_lt A hx hy,
        Matrix.map_apply]
    · rw [padEntry_of_lt_ge (A.map f) hx hy, padEntry_of_lt_ge A hx hy,
        map_zero]
  · rw [padEntry_of_ge (A.map f) hx, padEntry_of_ge A hx]
    split_ifs
    · exact (map_one f).symm
    · exact (map_zero f).symm

theorem stabMatrix_map (f : R →+* S) {n : ℕ} (m : ℕ)
    (A : Matrix (Fin n) (Fin n) R) :
    stabMatrix m (A.map f) = (stabMatrix m A).map f := by
  ext x y
  rw [stabMatrix_apply, Matrix.map_apply, stabMatrix_apply]
  exact padEntry_map f A _ _

/-- The transition maps of the direct system commute with the coefficient
maps. -/
theorem glStab_elementaryMatrixUnitMap (f : R →+* S) {n m : ℕ} (h : n ≤ m)
    (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    glStab S n m h (elementaryMatrixUnitMap f u)
      = elementaryMatrixUnitMap f (glStab R n m h u) := by
  apply Units.ext
  exact stabMatrix_map f m (u : Matrix (Fin n) (Fin n) R)

/-! ### The induced map of stable general linear groups -/

/-- The underlying function of `glColimMap`. -/
noncomputable def glColimMapFun (f : R →+* S) :
    ClassicalGLColim R → ClassicalGLColim S :=
  DirectLimit.map (glStab R) (glStab S)
    (fun _ => ⇑(elementaryMatrixUnitMap f))
    (fun _ _ h x => glStab_elementaryMatrixUnitMap f h x)

theorem glColimMapFun_glColimOf (f : R →+* S) (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    glColimMapFun f (glColimOf R n u)
      = glColimOf S n (elementaryMatrixUnitMap f u) := rfl

/-- **The map of stable general linear groups induced by a ring
homomorphism.** -/
noncomputable def glColimMap (f : R →+* S) :
    ClassicalGLColim R →* ClassicalGLColim S where
  toFun := glColimMapFun f
  map_one' := by
    have h0 : (1 : ClassicalGLColim R) = glColimOf R 0 1 := (map_one _).symm
    rw [h0, glColimMapFun_glColimOf, map_one, map_one]
  map_mul' := by
    intro x y
    obtain ⟨n, u, v, rfl, rfl⟩ := DirectLimit.exists_eq_mk₂ (f := glStab R) x y
    have hu : (⟦⟨n, u⟩⟧ : ClassicalGLColim R) = glColimOf R n u := rfl
    have hv : (⟦⟨n, v⟩⟧ : ClassicalGLColim R) = glColimOf R n v := rfl
    rw [hu, hv, ← map_mul (glColimOf R n), glColimMapFun_glColimOf,
      glColimMapFun_glColimOf, glColimMapFun_glColimOf, map_mul, map_mul]

@[simp] theorem glColimMap_glColimOf (f : R →+* S) (n : ℕ)
    (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    glColimMap f (glColimOf R n u)
      = glColimOf S n (elementaryMatrixUnitMap f u) := rfl

/-- **Coefficient maps carry `E_∞` into `E_∞`**, with no surjectivity
assumption, exactly as `elementaryGroup_map_le` does at each fixed rank. -/
theorem elementaryColim_map_le (f : R →+* S) :
    (elementaryColim R).map (glColimMap f) ≤ elementaryColim S := by
  rw [Subgroup.map_le_iff_le_comap]
  show (⨆ n : ℕ, (elementaryGroup (Fin n) R).map (glColimOf R n)) ≤ _
  refine iSup_le fun n => ?_
  rw [Subgroup.map_le_iff_le_comap]
  intro u hu
  simp only [Subgroup.mem_comap, glColimMap_glColimOf]
  exact glColimOf_mem_elementaryColim S
    (elementaryGroup_map_le f (Subgroup.mem_map_of_mem _ hu))

/-! ### Ring isomorphisms -/

theorem elementaryMatrixUnitMap_symm_apply (e : R ≃+* S) {n : ℕ}
    (u : (Matrix (Fin n) (Fin n) R)ˣ) :
    elementaryMatrixUnitMap (e.symm : S →+* R)
        (elementaryMatrixUnitMap (e : R →+* S) u) = u := by
  apply Units.ext
  show ((u : Matrix (Fin n) (Fin n) R).map (e : R →+* S)).map (e.symm : S →+* R)
    = (u : Matrix (Fin n) (Fin n) R)
  ext i j
  simp

theorem elementaryMatrixUnitMap_apply_symm (e : R ≃+* S) {n : ℕ}
    (u : (Matrix (Fin n) (Fin n) S)ˣ) :
    elementaryMatrixUnitMap (e : R →+* S)
        (elementaryMatrixUnitMap (e.symm : S →+* R) u) = u := by
  apply Units.ext
  show ((u : Matrix (Fin n) (Fin n) S).map (e.symm : S →+* R)).map (e : R →+* S)
    = (u : Matrix (Fin n) (Fin n) S)
  ext i j
  simp

/-- **A ring isomorphism induces an isomorphism of stable general linear
groups.** -/
noncomputable def glColimEquiv (e : R ≃+* S) :
    ClassicalGLColim R ≃* ClassicalGLColim S where
  toFun := glColimMap (e : R →+* S)
  invFun := glColimMap (e.symm : S →+* R)
  left_inv := by
    intro z
    induction z using DirectLimit.induction with
    | ih n u =>
        have h : (⟦⟨n, u⟩⟧ : ClassicalGLColim R) = glColimOf R n u := rfl
        rw [h, glColimMap_glColimOf, glColimMap_glColimOf,
          elementaryMatrixUnitMap_symm_apply]
  right_inv := by
    intro z
    induction z using DirectLimit.induction with
    | ih n u =>
        have h : (⟦⟨n, u⟩⟧ : ClassicalGLColim S) = glColimOf S n u := rfl
        rw [h, glColimMap_glColimOf, glColimMap_glColimOf,
          elementaryMatrixUnitMap_apply_symm]
  map_mul' := (glColimMap (e : R →+* S)).map_mul

@[simp] theorem glColimEquiv_apply (e : R ≃+* S) (z : ClassicalGLColim R) :
    glColimEquiv e z = glColimMap (e : R →+* S) z := rfl

@[simp] theorem glColimEquiv_symm_apply (e : R ≃+* S) (z : ClassicalGLColim S) :
    (glColimEquiv e).symm z = glColimMap (e.symm : S →+* R) z := rfl

/-- A ring isomorphism carries `E_∞` **onto** `E_∞`. -/
theorem elementaryColim_map_equiv (e : R ≃+* S) :
    (elementaryColim R).map (glColimEquiv e).toMonoidHom = elementaryColim S := by
  refine le_antisymm (elementaryColim_map_le (e : R →+* S)) ?_
  intro z hz
  refine ⟨glColimMap (e.symm : S →+* R) z, ?_, ?_⟩
  · exact elementaryColim_map_le (e.symm : S →+* R) (Subgroup.mem_map_of_mem _ hz)
  · exact (glColimEquiv e).apply_symm_apply z

/-- **`K₁` is functorial for ring isomorphisms.** -/
noncomputable def algebraicKOneCongr (e : R ≃+* S) :
    AlgebraicKOne R ≃* AlgebraicKOne S :=
  QuotientGroup.congr (elementaryColim R) (elementaryColim S)
    (glColimEquiv e) (elementaryColim_map_equiv e)

end Functor

/-! ### Morita invariance for a self-similar ring -/

/-- **The printed Morita step, for a ring isomorphic to its own matrix ring.**

`MFQuotientUnitsKOne.MoritaKOne` asks for `K_1(M_n(R)) ≅ K_1(R)` for every ring;
in general that is a cofinality argument about direct limits.  When `R` is
already isomorphic to `M_n(R)` as a ring — the case of `cor:leavitt-mf-quotient`,
where `R = L_k(1,d)` satisfies `R ≅ M_d(R)` — it is functoriality applied to
that isomorphism, and nothing about colimits is needed beyond
`algebraicKOneCongr`. -/
theorem moritaKOne_of_selfSimilar {R : Type*} [Ring R] {n : ℕ}
    (e : R ≃+* Matrix (Fin n) (Fin n) R) :
    Nonempty (AlgebraicKOne (Matrix (Fin n) (Fin n) R) ≃* AlgebraicKOne R) :=
  ⟨algebraicKOneCongr e.symm⟩

end AlgebraicK
end GroupApproximation

/-! ### Axiom audit -/

#audit_axioms GroupApproximation.AlgebraicK.stabMatrix_map
#audit_axioms GroupApproximation.AlgebraicK.glColimMap
#audit_axioms GroupApproximation.AlgebraicK.elementaryColim_map_le
#audit_axioms GroupApproximation.AlgebraicK.glColimEquiv
#audit_axioms GroupApproximation.AlgebraicK.elementaryColim_map_equiv
#audit_axioms GroupApproximation.AlgebraicK.algebraicKOneCongr
#audit_axioms GroupApproximation.AlgebraicK.moritaKOne_of_selfSimilar
