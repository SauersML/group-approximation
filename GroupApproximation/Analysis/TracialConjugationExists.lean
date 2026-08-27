import GroupApproximation.Analysis.TracialStandardFormCommutation

/-!
# Existence of the modular conjugation, from the standard form alone

`Analysis/TracialStandardFormCommutation.lean` proves the commutation theorem
and the generation payoff for a von Neumann algebra with a unit cyclic
separating tracial vector, taking the modular conjugation `J` as *data*
(`TracialConjugation`).  This module discharges that datum: **every tracial
standard form admits a modular conjugation**, so the abstract commutation
theorem needs nothing beyond `IsTracialStandardForm`.

The construction is the classical one, with no modular theory.  On the orbit
`MΩ` the map is algebraic: a vector `TΩ` determines its representative
`T ∈ M` *uniquely*, because `Ω` is separating (`orbitRep_unique`), and
`J₀(TΩ) = T⋆Ω`.  Traciality of the vector state makes `J₀` an isometry of
the orbit — `⟪S⋆Ω, T⋆Ω⟫ = ⟪TΩ, SΩ⟫` (`inner_star_omega`) — so it extends
uniformly to the closure of the orbit, which is all of `H` by cyclicity
(`Dense.extend`).  Additivity, conjugate-linearity, the involution law, the
inner-product conjugation, and the defining action on the orbit all pass to
the extension by continuity off the dense orbit.

* `orbitRep`, `orbitRep_unique` — the unique representative of an orbit
  vector.
* `inner_star_omega` — the tracial pairing identity, the analytic heart.
* `modularConjugation` — the extension, with `modularConjugation_orbit`
  its defining action `J(TΩ) = T⋆Ω`.
* `tracialConjugation` — the bundled `TracialConjugation M Ω`.
* `exists_tracialConjugation` — the existence statement.
-/

namespace GroupApproximation
namespace TracialStandardForm

open scoped InnerProductSpace

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {Ω : H}

/-! ## The unique representative of an orbit vector -/

/-- The representative of an orbit vector is unique, because the vector is
separating. -/
theorem orbitRep_unique (hsf : IsTracialStandardForm M Ω)
    {T S : H →L[ℂ] H} (hT : T ∈ M) (hS : S ∈ M) (h : T Ω = S Ω) : T = S := by
  have hmem : T - S ∈ M := sub_mem hT hS
  have hzero : (T - S) Ω = 0 := by
    rw [sub_apply, h, sub_self]
  have := hsf.separating (T - S) hmem hzero
  exact sub_eq_zero.mp this

/-- A representative of an orbit vector, by choice. -/
def orbitRep (v : orbit (M : Set (H →L[ℂ] H)) Ω) : H →L[ℂ] H :=
  v.2.choose

theorem orbitRep_mem (v : orbit (M : Set (H →L[ℂ] H)) Ω) :
    orbitRep v ∈ M :=
  v.2.choose_spec.1

theorem orbitRep_apply (v : orbit (M : Set (H →L[ℂ] H)) Ω) :
    orbitRep v Ω = ↑v :=
  v.2.choose_spec.2

/-! ## The pairing identity, and the orbit-level conjugation -/

omit [CompleteSpace H] in
private theorem re_inner_self (v : H) : (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) v
  simpa [RCLike.re_to_complex] using h

/-- **The tracial pairing identity**: `⟪S⋆Ω, T⋆Ω⟫ = ⟪TΩ, SΩ⟫` for members of
`M`.  Everything about the conjugation reduces to this. -/
theorem inner_star_omega (hsf : IsTracialStandardForm M Ω)
    {A B : H →L[ℂ] H} (hA : A ∈ M) (hB : B ∈ M) :
    ⟪(star A) Ω, (star B) Ω⟫_ℂ = ⟪B Ω, A Ω⟫_ℂ := by
  calc ⟪(star A) Ω, (star B) Ω⟫_ℂ
      = ⟪Ω, A ((star B) Ω)⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_left]
    _ = ⟪Ω, (A * star B) Ω⟫_ℂ := rfl
    _ = ⟪Ω, (star B * A) Ω⟫_ℂ := hsf.tracial A hA (star B) (star_mem hB)
    _ = ⟪Ω, (star B) (A Ω)⟫_ℂ := rfl
    _ = ⟪B Ω, A Ω⟫_ℂ := by
        rw [ContinuousLinearMap.star_eq_adjoint,
          ContinuousLinearMap.adjoint_inner_right]

/-- The star map preserves the norm of orbit vectors. -/
theorem norm_star_omega (hsf : IsTracialStandardForm M Ω)
    {A : H →L[ℂ] H} (hA : A ∈ M) : ‖(star A) Ω‖ = ‖A Ω‖ := by
  have h := congrArg Complex.re (inner_star_omega hsf hA hA)
  rw [re_inner_self, re_inner_self] at h
  nlinarith [norm_nonneg ((star A) Ω), norm_nonneg (A Ω)]

/-- The conjugation on the orbit: `J₀(TΩ) = T⋆Ω` for the unique
representative. -/
def preJ (v : orbit (M : Set (H →L[ℂ] H)) Ω) : H :=
  (star (orbitRep v)) Ω

/-- `J₀` is an isometry of the orbit. -/
theorem isometry_preJ (hsf : IsTracialStandardForm M Ω) :
    Isometry (preJ (M := M) (Ω := Ω)) := by
  refine Isometry.of_dist_eq fun v w ↦ ?_
  rw [Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
  have hsub : preJ v - preJ w = (star (orbitRep v - orbitRep w)) Ω := by
    show (star (orbitRep v)) Ω - (star (orbitRep w)) Ω = _
    rw [star_sub, sub_apply]
  have hmem : orbitRep v - orbitRep w ∈ M :=
    sub_mem (orbitRep_mem v) (orbitRep_mem w)
  have happ : (orbitRep v - orbitRep w) Ω = ↑v - ↑w := by
    rw [sub_apply, orbitRep_apply, orbitRep_apply]
  rw [hsub, norm_star_omega hsf hmem, happ]

/-! ## The extension -/

/-- **The modular conjugation**, as the uniform extension of `J₀` off the
dense orbit. -/
def modularConjugation (hsf : IsTracialStandardForm M Ω) : H → H :=
  hsf.cyclic.extend (preJ (M := M) (Ω := Ω))

theorem continuous_modularConjugation (hsf : IsTracialStandardForm M Ω) :
    Continuous (modularConjugation hsf) :=
  (hsf.cyclic.uniformContinuous_extend
    (isometry_preJ hsf).uniformContinuous).continuous

/-- The defining action on the orbit: `J(TΩ) = T⋆Ω`. -/
theorem modularConjugation_orbit (hsf : IsTracialStandardForm M Ω)
    {T : H →L[ℂ] H} (hT : T ∈ M) :
    modularConjugation hsf (T Ω) = (star T) Ω := by
  have hmem : T Ω ∈ orbit (M : Set (H →L[ℂ] H)) Ω := ⟨T, hT, rfl⟩
  have h1 : modularConjugation hsf
      ((⟨T Ω, hmem⟩ : orbit (M : Set (H →L[ℂ] H)) Ω) : H)
      = preJ (⟨T Ω, hmem⟩ : orbit (M : Set (H →L[ℂ] H)) Ω) :=
    hsf.cyclic.extend_of_ind (isometry_preJ hsf).uniformContinuous _
  have h2 : orbitRep (⟨T Ω, hmem⟩ : orbit (M : Set (H →L[ℂ] H)) Ω) = T :=
    orbitRep_unique hsf (orbitRep_mem _) hT
      (by rw [orbitRep_apply])
  calc modularConjugation hsf (T Ω)
      = preJ (⟨T Ω, hmem⟩ : orbit (M : Set (H →L[ℂ] H)) Ω) := h1
    _ = (star T) Ω := by rw [preJ, h2]

/-! ## The identities, by density -/

/-- Additivity. -/
theorem modularConjugation_add (hsf : IsTracialStandardForm M Ω)
    (u v : H) :
    modularConjugation hsf (u + v)
      = modularConjugation hsf u + modularConjugation hsf v := by
  have hJ := continuous_modularConjugation hsf
  have hfun : (fun p : H × H ↦ modularConjugation hsf (p.1 + p.2))
      = fun p : H × H ↦ modularConjugation hsf p.1
          + modularConjugation hsf p.2 := by
    refine Continuous.ext_on ((hsf.cyclic.prod hsf.cyclic))
      (hJ.comp (continuous_fst.add continuous_snd))
      ((hJ.comp continuous_fst).add (hJ.comp continuous_snd)) ?_
    rintro ⟨u', v'⟩ ⟨⟨T₁, hT₁, rfl⟩, ⟨T₂, hT₂, rfl⟩⟩
    have hsum : T₁ Ω + T₂ Ω = (T₁ + T₂) Ω := by
      rw [add_apply]
    show modularConjugation hsf (T₁ Ω + T₂ Ω)
      = modularConjugation hsf (T₁ Ω) + modularConjugation hsf (T₂ Ω)
    rw [hsum, modularConjugation_orbit hsf (add_mem hT₁ hT₂),
      modularConjugation_orbit hsf hT₁, modularConjugation_orbit hsf hT₂,
      star_add, add_apply]
  exact congrFun hfun (u, v)

/-- Conjugate-linearity. -/
theorem modularConjugation_smul (hsf : IsTracialStandardForm M Ω)
    (z : ℂ) (v : H) :
    modularConjugation hsf (z • v)
      = (starRingEnd ℂ) z • modularConjugation hsf v := by
  have hJ := continuous_modularConjugation hsf
  have hfun : (fun w : H ↦ modularConjugation hsf (z • w))
      = fun w : H ↦ (starRingEnd ℂ) z • modularConjugation hsf w := by
    refine Continuous.ext_on hsf.cyclic
      (hJ.comp (continuous_const_smul z))
      ((hJ.comp continuous_id).const_smul _) ?_
    rintro u' ⟨T, hT, rfl⟩
    have hsmul : z • T Ω = (z • T) Ω := by
      rw [smul_apply]
    have hmem : z • T ∈ M := by
      rw [show z • T = algebraMap ℂ (H →L[ℂ] H) z * T from
        Algebra.smul_def z T]
      exact mul_mem (algebraMap_mem M.toStarSubalgebra z) hT
    show modularConjugation hsf (z • T Ω)
      = (starRingEnd ℂ) z • modularConjugation hsf (T Ω)
    rw [hsmul, modularConjugation_orbit hsf hmem,
      modularConjugation_orbit hsf hT, star_smul, smul_apply]
    rfl
  exact congrFun hfun v

/-- The involution law. -/
theorem modularConjugation_invol (hsf : IsTracialStandardForm M Ω)
    (v : H) :
    modularConjugation hsf (modularConjugation hsf v) = v := by
  have hJ := continuous_modularConjugation hsf
  have hfun : (fun w : H ↦
      modularConjugation hsf (modularConjugation hsf w)) = fun w : H ↦ w := by
    refine Continuous.ext_on hsf.cyclic (hJ.comp hJ) continuous_id ?_
    rintro u' ⟨T, hT, rfl⟩
    show modularConjugation hsf (modularConjugation hsf (T Ω)) = T Ω
    rw [modularConjugation_orbit hsf hT,
      modularConjugation_orbit hsf (star_mem hT), star_star]
  exact congrFun hfun v

/-- The inner-product conjugation. -/
theorem inner_modularConjugation (hsf : IsTracialStandardForm M Ω)
    (u v : H) :
    ⟪modularConjugation hsf u, modularConjugation hsf v⟫_ℂ = ⟪v, u⟫_ℂ := by
  have hJ := continuous_modularConjugation hsf
  have hfun : (fun p : H × H ↦
      ⟪modularConjugation hsf p.1, modularConjugation hsf p.2⟫_ℂ)
      = fun p : H × H ↦ ⟪p.2, p.1⟫_ℂ := by
    refine Continuous.ext_on ((hsf.cyclic.prod hsf.cyclic))
      (Continuous.inner (hJ.comp continuous_fst) (hJ.comp continuous_snd))
      (Continuous.inner continuous_snd continuous_fst) ?_
    rintro ⟨u', v'⟩ ⟨⟨T₁, hT₁, rfl⟩, ⟨T₂, hT₂, rfl⟩⟩
    show ⟪modularConjugation hsf (T₁ Ω),
        modularConjugation hsf (T₂ Ω)⟫_ℂ = ⟪T₂ Ω, T₁ Ω⟫_ℂ
    rw [modularConjugation_orbit hsf hT₁, modularConjugation_orbit hsf hT₂]
    exact inner_star_omega hsf hT₁ hT₂
  exact congrFun hfun (u, v)

/-! ## The bundled conjugation, and existence -/

/-- **Every tracial standard form admits a modular conjugation.**  The datum
the abstract commutation theorem consumes, constructed rather than assumed. -/
def tracialConjugation (hsf : IsTracialStandardForm M Ω) :
    TracialConjugation M Ω where
  J := modularConjugation hsf
  map_add := modularConjugation_add hsf
  map_smul := modularConjugation_smul hsf
  invol := modularConjugation_invol hsf
  inner_map := inner_modularConjugation hsf
  map_orbit := fun _ hT ↦ modularConjugation_orbit hsf hT

/-- Existence form. -/
theorem exists_tracialConjugation (hsf : IsTracialStandardForm M Ω) :
    Nonempty (TracialConjugation M Ω) :=
  ⟨tracialConjugation hsf⟩

end

end TracialStandardForm
end GroupApproximation
