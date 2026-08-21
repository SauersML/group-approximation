import GroupApproximation.Higman.OperationClosureRho

/-!
# The flip group: inverting the conjugators of `a`

`Higman.OperationClosureRho` reduces Higman's operation `ρ` to one statement,
that inverting the conjugators of a benign group of `a`-conjugates keeps it
benign, and packages what proves it as `Seq.FlipWitness`.  This file builds
the group and the automorphism, so that all that is left of the witness is its
last field, `transport`.

## The construction

The normal closure `N` of `a` in `F₃` is free on `{a ^ w : w ∈ K}`, and `K`
acts on that basis by right translation.  The map `a ^ w ↦ a ^ w⁻¹` permutes
the basis, so it is an automorphism of `N`, but it turns right translations
into left ones and therefore does not extend to `F₃`.  It does extend once a
second, left-acting copy of `K` is present, and that copy is added by two HNN
extensions:

* `ψ_b : a ↦ a ^ b, b ↦ b, c ↦ c` and `ψ_c : a ↦ a ^ c, b ↦ b, c ↦ c` are
  partial conjugations, hence automorphisms of `F₃`;
* `G₁ = F₃ ⋊_{ψ_b} ℤ` is the HNN extension along `ψ_b` on all of `F₃`;
* `G₂ = G₁ ⋊_{ψ_c} ℤ` is the HNN extension of `G₁` along `ψ_c` on the *copy
  of `F₃`* --- not on all of `G₁`, which is what keeps the second copy of `K`
  free rather than abelian, and so keeps it interchangeable with the first.

`G₂` is `F₃ ⋊_ψ K = N ⋊ (K × K)`, with presentation

    ⟨a, b, c, β, γ | [β, b], [β, c], [γ, b], [γ, c], [a, bβ], [a, cγ]⟩,

finitely presented and torsion-free because each stage is
(`isFinitelyPresented_hnnExtension`, `HNNBritton.isPowerTorsionFree_hnn`).

The flip is the automorphism `Θ` of `G₂` fixing `a` and exchanging the two
copies of `K`, `b ↔ β` and `c ↔ γ`.  It is built by lifting twice, and it is
an involution.  Because the two copies of `K` commute and `β` conjugates `a`
to `a ^ b`, one induction over `K` (`conj_left`) gives

    Θ (a ^ w) = a ^ (w⁻¹)      for every `w ∈ K`,

which is `flipWitness_flip_conj`, the field `Seq.FlipWitness.flip_conj`.

## What is still owed

`transportHypothesis` --- the torsion-free form of the image half of Higman's
Lemma 3.3 at this one embedding.  `Higman.BenignWitness.mapEmb` proves it
without the torsion clause.  See the header of
`Higman.OperationClosureRho` for the two routes to the clause; the tower here
was built with associated subgroups finitely generated inside `F₃` precisely
so that the amalgam-free route is available.
-/

namespace GroupApproximation
namespace Higman
namespace Flip

open GroupApproximation.Higman.Conj
open GroupApproximation.ProductFinitePresentation

/-! ## 1.  The two partial conjugations -/

/-- `ψ_b`: conjugate `a` by `b`, and fix `b` and `c`. -/
def psiB : F₃ →* F₃ :=
  FreeGroup.lift (fun i : Fin 3 => if i = 0 then b⁻¹ * a * b else if i = 1 then b else c)

/-- Its inverse. -/
def psiBinv : F₃ →* F₃ :=
  FreeGroup.lift (fun i : Fin 3 => if i = 0 then b * a * b⁻¹ else if i = 1 then b else c)

/-- `ψ_c`: conjugate `a` by `c`, and fix `b` and `c`. -/
def psiC : F₃ →* F₃ :=
  FreeGroup.lift (fun i : Fin 3 => if i = 0 then c⁻¹ * a * c else if i = 1 then b else c)

/-- Its inverse. -/
def psiCinv : F₃ →* F₃ :=
  FreeGroup.lift (fun i : Fin 3 => if i = 0 then c * a * c⁻¹ else if i = 1 then b else c)

@[simp] theorem psiB_a : psiB a = b⁻¹ * a * b := by
  unfold psiB a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiB_b : psiB b = b := by
  unfold psiB b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiB_c : psiB c = c := by
  unfold psiB c
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiBinv_a : psiBinv a = b * a * b⁻¹ := by
  unfold psiBinv a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiBinv_b : psiBinv b = b := by
  unfold psiBinv b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiBinv_c : psiBinv c = c := by
  unfold psiBinv c
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiC_a : psiC a = c⁻¹ * a * c := by
  unfold psiC a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiC_b : psiC b = b := by
  unfold psiC b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiC_c : psiC c = c := by
  unfold psiC c
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiCinv_a : psiCinv a = c * a * c⁻¹ := by
  unfold psiCinv a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiCinv_b : psiCinv b = b := by
  unfold psiCinv b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem psiCinv_c : psiCinv c = c := by
  unfold psiCinv c
  rw [FreeGroup.lift_apply_of]
  simp

theorem psiBinv_comp_psiB : psiBinv.comp psiB = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · show psiBinv (psiB a) = a
    rw [psiB_a, map_mul, map_mul, map_inv, psiBinv_a, psiBinv_b]
    group
  · show psiBinv (psiB b) = b
    rw [psiB_b, psiBinv_b]
  · show psiBinv (psiB c) = c
    rw [psiB_c, psiBinv_c]

theorem psiB_comp_psiBinv : psiB.comp psiBinv = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · show psiB (psiBinv a) = a
    rw [psiBinv_a, map_mul, map_mul, map_inv, psiB_a, psiB_b]
    group
  · show psiB (psiBinv b) = b
    rw [psiBinv_b, psiB_b]
  · show psiB (psiBinv c) = c
    rw [psiBinv_c, psiB_c]

theorem psiCinv_comp_psiC : psiCinv.comp psiC = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · show psiCinv (psiC a) = a
    rw [psiC_a, map_mul, map_mul, map_inv, psiCinv_a, psiCinv_c]
    group
  · show psiCinv (psiC b) = b
    rw [psiC_b, psiCinv_b]
  · show psiCinv (psiC c) = c
    rw [psiC_c, psiCinv_c]

theorem psiC_comp_psiCinv : psiC.comp psiCinv = MonoidHom.id F₃ := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · show psiC (psiCinv a) = a
    rw [psiCinv_a, map_mul, map_mul, map_inv, psiC_a, psiC_c]
    group
  · show psiC (psiCinv b) = b
    rw [psiCinv_b, psiC_b]
  · show psiC (psiCinv c) = c
    rw [psiCinv_c, psiC_c]

/-- `ψ_b`, as an automorphism. -/
def psiBEquiv : F₃ ≃* F₃ where
  toFun := psiB
  invFun := psiBinv
  left_inv x := congrArg (fun f : F₃ →* F₃ => f x) psiBinv_comp_psiB
  right_inv x := congrArg (fun f : F₃ →* F₃ => f x) psiB_comp_psiBinv
  map_mul' := map_mul _

/-- `ψ_c`, as an automorphism. -/
def psiCEquiv : F₃ ≃* F₃ where
  toFun := psiC
  invFun := psiCinv
  left_inv x := congrArg (fun f : F₃ →* F₃ => f x) psiCinv_comp_psiC
  right_inv x := congrArg (fun f : F₃ →* F₃ => f x) psiC_comp_psiCinv
  map_mul' := map_mul _

@[simp] theorem psiBEquiv_apply (x : F₃) : psiBEquiv x = psiB x := rfl

@[simp] theorem psiCEquiv_apply (x : F₃) : psiCEquiv x = psiC x := rfl

/-! ## 2.  The first extension -/

/-- `ψ_b`, transported to the top subgroup. -/
def psiBTop : ↥(⊤ : Subgroup F₃) ≃* ↥(⊤ : Subgroup F₃) :=
  (Subgroup.topEquiv).trans (psiBEquiv.trans (Subgroup.topEquiv).symm)

theorem coe_psiBTop (x : ↥(⊤ : Subgroup F₃)) :
    ((psiBTop x : ↥(⊤ : Subgroup F₃)) : F₃) = psiB (x : F₃) := rfl

/-- `F₃ ⋊_{ψ_b} ℤ`. -/
abbrev G₁ : Type := HNNExtension F₃ ⊤ ⊤ psiBTop

theorem conj_of_one (x : F₃) :
    (HNNExtension.t : G₁) * HNNExtension.of x * (HNNExtension.t : G₁)⁻¹
      = HNNExtension.of (psiB x) := by
  have h := HNNExtension.equiv_eq_conj (φ := psiBTop) ⟨x, Subgroup.mem_top x⟩
  rw [coe_psiBTop] at h
  exact h.symm

theorem of_one_injective : Function.Injective (HNNExtension.of : F₃ →* G₁) :=
  HNNExtension.of_injective psiBTop

theorem fg_top_F₃ : Group.FG ↥(⊤ : Subgroup F₃) := by
  letI : Group.FG F₃ := fg_of_isFinitelyPresented F₃
  exact Group.fg_of_surjective (f := (Subgroup.topEquiv (G := F₃)).symm.toMonoidHom)
    (Subgroup.topEquiv (G := F₃)).symm.surjective

theorem isFinitelyPresented_G₁ : Group.IsFinitelyPresented G₁ := by
  letI : Group.FG ↥(⊤ : Subgroup F₃) := fg_top_F₃
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension psiBTop

theorem torsionFree_G₁ : IsPowerTorsionFree G₁ :=
  HNNBritton.isPowerTorsionFree_hnn psiBTop IsPowerTorsionFree.of_isMulTorsionFree

/-! ## 3.  The second extension -/

/-- The copy of `F₃` inside `G₁`, which is where the second stable letter
acts. -/
def Acopy : Subgroup G₁ := MonoidHom.range (HNNExtension.of : F₃ →* G₁)

/-- `F₃` and its copy. -/
noncomputable def embA : F₃ ≃* ↥Acopy :=
  MonoidHom.ofInjective of_one_injective

@[simp] theorem coe_embA (x : F₃) : ((embA x : ↥Acopy) : G₁) = HNNExtension.of x :=
  MonoidHom.ofInjective_apply of_one_injective

/-- `ψ_c`, transported to the copy of `F₃`. -/
noncomputable def psiCA : ↥Acopy ≃* ↥Acopy :=
  (embA.symm).trans (psiCEquiv.trans embA)

theorem psiCA_embA (x : F₃) : psiCA (embA x) = embA (psiC x) := by
  unfold psiCA
  simp

/-- `G₁ ⋊_{ψ_c} ℤ` --- that is, `F₃ ⋊_ψ K`. -/
abbrev G₂ : Type := HNNExtension G₁ Acopy Acopy psiCA

theorem fg_Acopy : Group.FG ↥Acopy := by
  letI : Group.FG F₃ := fg_of_isFinitelyPresented F₃
  exact Group.fg_of_surjective (f := embA.toMonoidHom) embA.surjective

theorem isFinitelyPresented_G₂ : Group.IsFinitelyPresented G₂ := by
  letI : Group.IsFinitelyPresented G₁ := isFinitelyPresented_G₁
  letI : Group.FG ↥Acopy := fg_Acopy
  exact HNNFinitePresentation.isFinitelyPresented_hnnExtension psiCA

theorem torsionFree_G₂ : IsPowerTorsionFree G₂ :=
  HNNBritton.isPowerTorsionFree_hnn psiCA torsionFree_G₁

/-! ## 4.  The generators of `G₂` -/

/-- The copy of `F₃` inside `G₂`. -/
noncomputable def emb : F₃ →* G₂ :=
  (HNNExtension.of : G₁ →* G₂).comp (HNNExtension.of : F₃ →* G₁)

theorem emb_injective : Function.Injective emb :=
  (HNNExtension.of_injective psiCA).comp of_one_injective

/-- The first stable letter: the left-acting copy of `b`. -/
noncomputable def beta : G₂ := HNNExtension.of (HNNExtension.t : G₁)

/-- The second stable letter: the left-acting copy of `c`. -/
noncomputable def gamma : G₂ := HNNExtension.t

theorem conj_beta (x : F₃) : beta * emb x * beta⁻¹ = emb (psiB x) := by
  have h : (HNNExtension.of : G₁ →* G₂)
        ((HNNExtension.t : G₁) * (HNNExtension.of : F₃ →* G₁) x
          * (HNNExtension.t : G₁)⁻¹)
      = (HNNExtension.of : G₁ →* G₂) ((HNNExtension.of : F₃ →* G₁) (psiB x)) :=
    congrArg _ (conj_of_one x)
  rw [map_mul, map_mul, map_inv] at h
  exact h

theorem conj_gamma (x : F₃) : gamma * emb x * gamma⁻¹ = emb (psiC x) := by
  have h := HNNExtension.equiv_eq_conj (φ := psiCA) (embA x)
  rw [psiCA_embA, coe_embA, coe_embA] at h
  exact h.symm

/-! ## 5.  The relations, spelled out -/

theorem conj_beta_b : beta * emb b * beta⁻¹ = emb b := by
  have h := conj_beta b
  rwa [psiB_b] at h

theorem conj_beta_c : beta * emb c * beta⁻¹ = emb c := by
  have h := conj_beta c
  rwa [psiB_c] at h

theorem conj_gamma_b : gamma * emb b * gamma⁻¹ = emb b := by
  have h := conj_gamma b
  rwa [psiC_b] at h

theorem conj_gamma_c : gamma * emb c * gamma⁻¹ = emb c := by
  have h := conj_gamma c
  rwa [psiC_c] at h

theorem comm_beta_b : beta * emb b = emb b * beta := by
  calc beta * emb b = beta * emb b * beta⁻¹ * beta := by group
    _ = emb b * beta := by rw [conj_beta_b]

theorem comm_beta_c : beta * emb c = emb c * beta := by
  calc beta * emb c = beta * emb c * beta⁻¹ * beta := by group
    _ = emb c * beta := by rw [conj_beta_c]

theorem comm_gamma_b : gamma * emb b = emb b * gamma := by
  calc gamma * emb b = gamma * emb b * gamma⁻¹ * gamma := by group
    _ = emb b * gamma := by rw [conj_gamma_b]

theorem comm_gamma_c : gamma * emb c = emb c * gamma := by
  calc gamma * emb c = gamma * emb c * gamma⁻¹ * gamma := by group
    _ = emb c * gamma := by rw [conj_gamma_c]

/-- Conjugating the other way is `ψ_b⁻¹`. -/
theorem conj_beta_inv (x : F₃) : beta⁻¹ * emb x * beta = emb (psiBinv x) := by
  have h := conj_beta (psiBinv x)
  rw [show psiB (psiBinv x) = x from
    congrArg (fun f : F₃ →* F₃ => f x) psiB_comp_psiBinv] at h
  calc beta⁻¹ * emb x * beta
      = beta⁻¹ * (beta * emb (psiBinv x) * beta⁻¹) * beta := by rw [h]
    _ = emb (psiBinv x) := by group

/-- Conjugating the other way is `ψ_c⁻¹`. -/
theorem conj_gamma_inv (x : F₃) : gamma⁻¹ * emb x * gamma = emb (psiCinv x) := by
  have h := conj_gamma (psiCinv x)
  rw [show psiC (psiCinv x) = x from
    congrArg (fun f : F₃ →* F₃ => f x) psiC_comp_psiCinv] at h
  calc gamma⁻¹ * emb x * gamma
      = gamma⁻¹ * (gamma * emb (psiCinv x) * gamma⁻¹) * gamma := by rw [h]
    _ = emb (psiCinv x) := by group

/-! ## 6.  The flip -/

/-- The flip on the copy of `F₃`: fix `a`, send `b` and `c` to the left-acting
copies. -/
noncomputable def f0 : F₃ →* G₂ :=
  FreeGroup.lift (fun i : Fin 3 => if i = 0 then emb a else if i = 1 then beta else gamma)

@[simp] theorem f0_a : f0 a = emb a := by
  unfold f0 a
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem f0_b : f0 b = beta := by
  unfold f0 b
  rw [FreeGroup.lift_apply_of]
  simp

@[simp] theorem f0_c : f0 c = gamma := by
  unfold f0 c
  rw [FreeGroup.lift_apply_of]
  simp

/-- The lift condition at the first stable letter. -/
theorem f0_conj_b (x : F₃) : emb b * f0 x * (emb b)⁻¹ = f0 (psiB x) := by
  have key : (MulAut.conj (emb b)).toMonoidHom.comp f0 = f0.comp psiB := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    fin_cases i
    · show emb b * f0 a * (emb b)⁻¹ = f0 (psiB a)
      rw [f0_a, psiB_a, map_mul f0, map_mul f0, map_inv f0, f0_a, f0_b,
        conj_beta_inv a, psiBinv_a, map_mul emb, map_mul emb, map_inv emb]
    · show emb b * f0 b * (emb b)⁻¹ = f0 (psiB b)
      rw [f0_b, psiB_b, f0_b, ← comm_beta_b]
      group
    · show emb b * f0 c * (emb b)⁻¹ = f0 (psiB c)
      rw [f0_c, psiB_c, f0_c, ← comm_gamma_b]
      group
  exact congrArg (fun g : F₃ →* G₂ => g x) key

/-- The lift condition at the second stable letter. -/
theorem f0_conj_c (x : F₃) : emb c * f0 x * (emb c)⁻¹ = f0 (psiC x) := by
  have key : (MulAut.conj (emb c)).toMonoidHom.comp f0 = f0.comp psiC := by
    refine FreeGroup.ext_hom _ _ fun i => ?_
    fin_cases i
    · show emb c * f0 a * (emb c)⁻¹ = f0 (psiC a)
      rw [f0_a, psiC_a, map_mul f0, map_mul f0, map_inv f0, f0_a, f0_c,
        conj_gamma_inv a, psiCinv_a, map_mul emb, map_mul emb, map_inv emb]
    · show emb c * f0 b * (emb c)⁻¹ = f0 (psiC b)
      rw [f0_b, psiC_b, f0_b, ← comm_beta_c]
      group
    · show emb c * f0 c * (emb c)⁻¹ = f0 (psiC c)
      rw [f0_c, psiC_c, f0_c, ← comm_gamma_c]
      group
  exact congrArg (fun g : F₃ →* G₂ => g x) key

theorem f0_lift_one (x : ↥(⊤ : Subgroup F₃)) :
    emb b * f0 (x : F₃) = f0 ((psiBTop x : ↥(⊤ : Subgroup F₃)) : F₃) * emb b := by
  rw [coe_psiBTop, ← f0_conj_b (x : F₃)]
  group

/-- The flip on the first extension. -/
noncomputable def f1 : G₁ →* G₂ := HNNExtension.lift f0 (emb b) f0_lift_one

@[simp] theorem f1_of (x : F₃) : f1 (HNNExtension.of x) = f0 x :=
  HNNExtension.lift_of _ _ _ _

@[simp] theorem f1_t : f1 (HNNExtension.t : G₁) = emb b :=
  HNNExtension.lift_t _ _ _

theorem f1_lift_two (y : ↥Acopy) :
    emb c * f1 (y : G₁) = f1 ((psiCA y : ↥Acopy) : G₁) * emb c := by
  obtain ⟨z, hz⟩ := y.2
  have hy : (y : G₁) = HNNExtension.of z := hz.symm
  have hyz : y = embA z := Subtype.ext (by rw [hy, coe_embA])
  rw [hyz, psiCA_embA, coe_embA, coe_embA, f1_of, f1_of, ← f0_conj_c z]
  group

/-- **The flip.** -/
noncomputable def flipHom : G₂ →* G₂ := HNNExtension.lift f1 (emb c) f1_lift_two

@[simp] theorem flipHom_of (y : G₁) : flipHom (HNNExtension.of y) = f1 y :=
  HNNExtension.lift_of _ _ _ _

@[simp] theorem flipHom_t : flipHom (HNNExtension.t : G₂) = emb c :=
  HNNExtension.lift_t _ _ _

@[simp] theorem flipHom_emb (x : F₃) : flipHom (emb x) = f0 x := by
  unfold emb
  show flipHom (HNNExtension.of (HNNExtension.of x)) = f0 x
  rw [flipHom_of, f1_of]

@[simp] theorem flipHom_beta : flipHom beta = emb b := by
  unfold beta
  rw [flipHom_of, f1_t]

@[simp] theorem flipHom_gamma : flipHom gamma = emb c := by
  unfold gamma
  exact flipHom_t

theorem flipHom_comp_f0 : flipHom.comp f0 = emb := by
  refine FreeGroup.ext_hom _ _ fun i => ?_
  fin_cases i
  · show flipHom (f0 a) = emb a
    rw [f0_a, flipHom_emb, f0_a]
  · show flipHom (f0 b) = emb b
    rw [f0_b, flipHom_beta]
  · show flipHom (f0 c) = emb c
    rw [f0_c, flipHom_gamma]

theorem flipHom_f0 (x : F₃) : flipHom (f0 x) = emb x :=
  congrArg (fun g : F₃ →* G₂ => g x) flipHom_comp_f0

theorem flipHom_comp_flipHom : flipHom.comp flipHom = MonoidHom.id G₂ := by
  refine HNNExtension.hom_ext ?_ ?_
  · refine HNNExtension.hom_ext ?_ ?_
    · refine FreeGroup.ext_hom _ _ fun i => ?_
      fin_cases i
      · show flipHom (flipHom (emb a)) = emb a
        rw [flipHom_emb, f0_a, flipHom_emb, f0_a]
      · show flipHom (flipHom (emb b)) = emb b
        rw [flipHom_emb, f0_b, flipHom_beta]
      · show flipHom (flipHom (emb c)) = emb c
        rw [flipHom_emb, f0_c, flipHom_gamma]
    · show flipHom (flipHom beta) = beta
      rw [flipHom_beta, flipHom_emb, f0_b]
  · show flipHom (flipHom gamma) = gamma
    rw [flipHom_gamma, flipHom_emb, f0_c]

/-- **The flip, as an automorphism of `G₂`.** -/
noncomputable def flipEquiv : G₂ ≃* G₂ where
  toFun := flipHom
  invFun := flipHom
  left_inv x := congrArg (fun g : G₂ →* G₂ => g x) flipHom_comp_flipHom
  right_inv x := congrArg (fun g : G₂ →* G₂ => g x) flipHom_comp_flipHom
  map_mul' := map_mul _

@[simp] theorem flipEquiv_apply (x : G₂) : flipEquiv x = flipHom x := rfl

/-! ## 7.  The two copies of `K` commute, and the flip inverts the index -/

theorem comm_beta (v : F₃) (hv : v ∈ K) : Commute beta (emb v) := by
  refine Subgroup.closure_induction (p := fun z _ => Commute beta (emb z)) ?_ ?_ ?_ ?_ hv
  · rintro z hz
    rcases hz with rfl | hz
    · exact comm_beta_b
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact comm_beta_c
  · rw [map_one]
    exact Commute.one_right _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact hx.mul_right hy
  · intro x _ hx
    rw [map_inv]
    exact hx.inv_right

theorem comm_gamma (v : F₃) (hv : v ∈ K) : Commute gamma (emb v) := by
  refine Subgroup.closure_induction (p := fun z _ => Commute gamma (emb z)) ?_ ?_ ?_ ?_ hv
  · rintro z hz
    rcases hz with rfl | hz
    · exact comm_gamma_b
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact comm_gamma_c
  · rw [map_one]
    exact Commute.one_right _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact hx.mul_right hy
  · intro x _ hx
    rw [map_inv]
    exact hx.inv_right

/-- **The two copies of `K` commute.** -/
theorem comm_f0 (u : F₃) (hu : u ∈ K) (v : F₃) (hv : v ∈ K) :
    Commute (f0 u) (emb v) := by
  refine Subgroup.closure_induction (p := fun z _ => Commute (f0 z) (emb v)) ?_ ?_ ?_ ?_ hu
  · rintro z hz
    rcases hz with rfl | hz
    · rw [f0_b]
      exact comm_beta v hv
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [f0_c]
      exact comm_gamma v hv
  · rw [map_one]
    exact Commute.one_left _
  · intro x y _ _ hx hy
    rw [map_mul]
    exact hx.mul_left hy
  · intro x _ hx
    rw [map_inv]
    exact hx.inv_left

/-- A left-copy element conjugates a right-copy element of `K` trivially. -/
theorem conj_f0_emb (u : F₃) (hu : u ∈ K) (v : F₃) (hv : v ∈ K) :
    f0 u * emb v * (f0 u)⁻¹ = emb v := by
  rw [(comm_f0 u hu v hv).eq]
  group

/-- **The left copy conjugates `a` by the index.** -/
theorem conj_left (w : F₃) (hw : w ∈ K) :
    f0 w * emb a * (f0 w)⁻¹ = emb (w⁻¹ * a * w) := by
  refine Subgroup.closure_induction
    (p := fun z _ => f0 z * emb a * (f0 z)⁻¹ = emb (z⁻¹ * a * z)) ?_ ?_ ?_ ?_ hw
  · rintro z hz
    rcases hz with rfl | hz
    · rw [f0_b]
      have h := conj_beta a
      rw [psiB_a] at h
      exact h
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [f0_c]
      have h := conj_gamma a
      rw [psiC_a] at h
      exact h
  · simp
  · intro x y hx' hy' hx hy
    have hxK : x ∈ K := hx'
    have hyK : y ∈ K := hy'
    calc f0 (x * y) * emb a * (f0 (x * y))⁻¹
        = f0 x * (f0 y * emb a * (f0 y)⁻¹) * (f0 x)⁻¹ := by
          rw [map_mul]
          group
      _ = f0 x * emb (y⁻¹ * a * y) * (f0 x)⁻¹ := by rw [hy]
      _ = (f0 x * emb y⁻¹ * (f0 x)⁻¹) * (f0 x * emb a * (f0 x)⁻¹)
            * (f0 x * emb y * (f0 x)⁻¹) := by
          rw [map_mul emb, map_mul emb]
          group
      _ = emb y⁻¹ * emb (x⁻¹ * a * x) * emb y := by
          rw [conj_f0_emb x hxK y⁻¹ (Subgroup.inv_mem K hyK), hx,
            conj_f0_emb x hxK y hyK]
      _ = emb ((x * y)⁻¹ * a * (x * y)) := by
          rw [← map_mul emb, ← map_mul emb]
          congr 1
          group
  · intro x hx' hx
    have hxK : x ∈ K := hx'
    have hkey : f0 x * emb (x * a * x⁻¹) * (f0 x)⁻¹ = emb a := by
      calc f0 x * emb (x * a * x⁻¹) * (f0 x)⁻¹
          = (f0 x * emb x * (f0 x)⁻¹) * (f0 x * emb a * (f0 x)⁻¹)
              * (f0 x * emb x⁻¹ * (f0 x)⁻¹) := by
            rw [map_mul emb, map_mul emb]
            group
        _ = emb x * emb (x⁻¹ * a * x) * emb x⁻¹ := by
            rw [conj_f0_emb x hxK x hxK, hx,
              conj_f0_emb x hxK x⁻¹ (Subgroup.inv_mem K hxK)]
        _ = emb a := by
            rw [← map_mul emb, ← map_mul emb]
            congr 1
            group
    have hkey2 : emb (x * a * x⁻¹) = (f0 x)⁻¹ * emb a * f0 x := by
      rw [← hkey]
      group
    have hinvinv : x⁻¹⁻¹ = x := inv_inv x
    rw [map_inv f0, hinvinv, hkey2]
    group

/-- **The flip inverts the conjugators.**  This is the field
`Seq.FlipWitness.flip_conj`. -/
theorem flip_conj (h : F₃) (hh : h ∈ K) :
    flipEquiv (emb (h⁻¹ * a * h)) = emb (h * a * h⁻¹) := by
  have hinv : h⁻¹ ∈ K := Subgroup.inv_mem K hh
  have hkey := conj_left h⁻¹ hinv
  rw [inv_inv, map_inv f0, inv_inv] at hkey
  rw [flipEquiv_apply, flipHom_emb, map_mul f0, map_mul f0, map_inv f0, f0_a]
  exact hkey

/-! ## 8.  The witness, up to one classical input -/

/-- **The flip witness, given the one input that is left.**

Every field except `transport` is now proved.  `transport` is the torsion-free
form of the image half of Higman's Lemma 3.3 at this embedding;
`Higman.BenignWitness.mapEmb` proves it without the torsion clause. -/
noncomputable def flipWitness
    (transport : ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb)) :
    Seq.FlipWitness where
  G := G₂
  fp := isFinitelyPresented_G₂
  torsionFree := torsionFree_G₂
  emb := emb
  emb_injective := emb_injective
  flip := flipEquiv
  flip_conj := flip_conj
  transport := transport

/-- **Higman's operation `ρ`, from the flip group and the one classical
input.** -/
theorem benignTF_ASub_rhoOp_of_transport
    (transport : ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb))
    (B : Set Seq.E) (h : BenignTF (Seq.ASub B)) :
    BenignTF (Seq.ASub (Seq.rhoOp B)) :=
  Seq.benignTF_ASub_rhoOp_of_flip (flipWitness transport) B h

/-! ## 9.  The input in its general form

`transport` above is stated at one embedding, which is all `ρ` needs, but it is
an instance of a statement about the theory as a whole.  Recording that here
means whoever proves the general statement closes `ρ` with no further work ---
and the general statement is the one `τ` and any other operation that moves the
index set by something other than an endomorphism of `F₃` will need too. -/

theorem transport_of_imageClosure (himg : Seq.TorsionFreeImageClosure) :
    ∀ H : Subgroup F₃, BenignTF H → BenignTF (H.map emb) := by
  letI : Group.FG F₃ := fg_of_isFinitelyPresented F₃
  letI : Group.IsFinitelyPresented G₂ := isFinitelyPresented_G₂
  intro H hH
  exact himg F₃ G₂ torsionFree_G₂ H emb emb_injective hH

/-- **Higman's operation `ρ`, from one classical statement and nothing else.**

Every other ingredient --- the reflection identity, the automorphism `rhoAut`,
the flip group, the flip, and the transport calculus --- is proved. -/
theorem benignTF_ASub_rhoOp_of_imageClosure (himg : Seq.TorsionFreeImageClosure)
    (B : Set Seq.E) (h : BenignTF (Seq.ASub B)) :
    BenignTF (Seq.ASub (Seq.rhoOp B)) :=
  benignTF_ASub_rhoOp_of_transport (transport_of_imageClosure himg) B h

end Flip
end Higman
end GroupApproximation
