import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Group
import GroupApproximation.Meta.AxiomGuard

/-!
# The Kaloujnine–Krasner embedding into a regular wreath product

For groups `W` and `F`, the *regular wreath product* `W ≀ F` is the semidirect product
`(F → W) ⋊ F`, where `f` acts on a function `p : F → W` by left translation of the argument,
`(f · p) x = p (f⁻¹ * x)`.

The Kaloujnine–Krasner theorem: every group `G` with a normal subgroup `N` embeds in
`N ≀ (G ⧸ N)`.  Choosing a section `s` of the quotient map, the embedding is
`g ↦ (x ↦ (s x)⁻¹ * g * s (ḡ⁻¹ * x), ḡ)`.

Route.  `shiftHom` is the translation action, `kkHom` is the embedding for a given section,
and `exists_injective_regularWreath` chooses a section with `Function.surjInv`.  This is the
step "`V ↪ [V, V] ≀ (V / [V, V])`" of Zaremsky's envelope (arXiv:2405.09722, Section 3).
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

section Wreath

variable (W : Type*) [Group W] (F : Type*) [Group F]

/-- Left translation of the argument: `(shiftAut W F f p) x = p (f⁻¹ * x)`. -/
def shiftAut (f : F) : (F → W) ≃* (F → W) where
  toFun p x := p (f⁻¹ * x)
  invFun p x := p (f * x)
  left_inv p := by
    funext x
    show p (f⁻¹ * (f * x)) = p x
    rw [inv_mul_cancel_left]
  right_inv p := by
    funext x
    show p (f * (f⁻¹ * x)) = p x
    rw [mul_inv_cancel_left]
  map_mul' _ _ := rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.shiftAut

/-- The translation action of `F` on `F → W`. -/
def shiftHom : F →* MulAut (F → W) where
  toFun := shiftAut W F
  map_one' := by
    ext p x
    show p (1⁻¹ * x) = p x
    rw [inv_one, one_mul]
  map_mul' f g := by
    ext p x
    show p ((f * g)⁻¹ * x) = p (g⁻¹ * (f⁻¹ * x))
    rw [mul_inv_rev, mul_assoc]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.shiftHom

/-- The regular (unrestricted) wreath product `W ≀ F = (F → W) ⋊ F`. -/
abbrev RegularWreath : Type _ := (F → W) ⋊[shiftHom W F] F

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.RegularWreath

end Wreath

section KaloujnineKrasner

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal]

/-- The coordinate `(s x)⁻¹ * g * s (ḡ⁻¹ * x)` of the Kaloujnine–Krasner embedding; it lies
in `N` because its image in `G ⧸ N` is `x⁻¹ * ḡ * ḡ⁻¹ * x = 1`. -/
def kkCoord (s : G ⧸ N → G) (hs : ∀ q, (s q : G ⧸ N) = q) (g : G) (x : G ⧸ N) : ↥N :=
  ⟨(s x)⁻¹ * g * s ((g : G ⧸ N)⁻¹ * x), by
    refine (QuotientGroup.eq_one_iff _).1 ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hs, hs]
    group⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.kkCoord

/-- The Kaloujnine–Krasner homomorphism `G →* N ≀ (G ⧸ N)` for a section `s`. -/
def kkHom (s : G ⧸ N → G) (hs : ∀ q, (s q : G ⧸ N) = q) :
    G →* RegularWreath ↥N (G ⧸ N) where
  toFun g := ⟨kkCoord N s hs g, (g : G ⧸ N)⟩
  map_one' := by
    refine SemidirectProduct.ext ?_ ?_
    · funext x
      refine Subtype.ext ?_
      show (s x)⁻¹ * 1 * s (((1 : G) : G ⧸ N)⁻¹ * x) = 1
      rw [QuotientGroup.mk_one, inv_one, one_mul, mul_one, inv_mul_cancel]
    · show ((1 : G) : G ⧸ N) = 1
      rfl
  map_mul' g h := by
    refine SemidirectProduct.ext ?_ ?_
    · funext x
      refine Subtype.ext ?_
      show (s x)⁻¹ * (g * h) * s (((g * h : G) : G ⧸ N)⁻¹ * x) =
        (s x)⁻¹ * g * s ((g : G ⧸ N)⁻¹ * x) *
          ((s ((g : G ⧸ N)⁻¹ * x))⁻¹ * h * s ((h : G ⧸ N)⁻¹ * ((g : G ⧸ N)⁻¹ * x)))
      have e : ((g * h : G) : G ⧸ N)⁻¹ * x = (h : G ⧸ N)⁻¹ * ((g : G ⧸ N)⁻¹ * x) := by
        rw [QuotientGroup.mk_mul, mul_inv_rev, mul_assoc]
      rw [e]
      group
    · show ((g * h : G) : G ⧸ N) = (g : G ⧸ N) * (h : G ⧸ N)
      rfl

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.kkHom

theorem kkHom_injective (s : G ⧸ N → G) (hs : ∀ q, (s q : G ⧸ N) = q) :
    Function.Injective (kkHom N s hs) := by
  refine (injective_iff_map_eq_one _).2 fun g hg => ?_
  have hr : (g : G ⧸ N) = 1 := congrArg SemidirectProduct.right hg
  have hl : (s 1)⁻¹ * g * s ((g : G ⧸ N)⁻¹ * 1) = 1 :=
    congrArg (fun p : RegularWreath ↥N (G ⧸ N) => ((p.left 1 : ↥N) : G)) hg
  rw [hr, inv_one, one_mul] at hl
  calc g = s 1 * ((s 1)⁻¹ * g * s 1) * (s 1)⁻¹ := by group
    _ = 1 := by rw [hl]; group

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.kkHom_injective

/-- **Kaloujnine–Krasner.** A group embeds in the regular wreath product of any normal
subgroup by the corresponding quotient. -/
theorem exists_injective_regularWreath :
    ∃ φ : G →* RegularWreath ↥N (G ⧸ N), Function.Injective φ :=
  ⟨kkHom N (Function.surjInv QuotientGroup.mk_surjective)
      (Function.surjInv_eq QuotientGroup.mk_surjective),
    kkHom_injective N _ _⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_injective_regularWreath

end KaloujnineKrasner

end GroupApproximation.BooneHigman.Metabelian.Envelope
