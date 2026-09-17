import GroupApproximation.Algebra.WreathFunctor
import GroupApproximation.Algebra.VisibleQuotient
import GroupApproximation.Meta.AxiomGuard

/-!
# Height lamplighters with finite lamps are residually finite

**thm:notes-visible-quotient**, the step "`P_K` is residually finite".  The
target of the visible quotient map is `P_K = (K_ab)^{(ℤ)} ⋊ G_*`.  Here `G_*`
acts on the sites `ℤ` through its height character, and `K_ab` is finite.

We prove it in a general form.  Let `A` be a finite abelian group and `G` a
residually finite group.  Let `X` be a `G`-set with an injective height
`ℓ : X → ℤ` that is equivariant over a character `h : G → ℤ`.  Then `A^{(X)} ⋊ G`
is residually finite.

The proof follows the notes.  An element of the finite residual has trivial
`G`-coordinate, because `G` is residually finite.  For each `m > 0`, reducing
heights modulo `m` gives a homomorphism onto the finite group
`A^{(ℤ/m)} ⋊ ℤ/m`, so the lamp of such an element pushes to `1` modulo every
`m`.  A lamp that is nontrivial at `x₀` survives modulo any `m` larger than all
height gaps inside its support.  So the lamp is trivial.

* `heightMod` -- reduction `ℤ → ℤ/m`, multiplicatively.
* `wreath_finite` -- finite lamps, group and sites give a finite wreath product.
* `wreath_isResiduallyFinite_of_height` -- the general statement.
* `wreath_quotient_isResiduallyFinite` -- the sites `G ⧸ ker h`.
-/

namespace GroupApproximation.Full.NN04

open GroupApproximation.WreathLampPushforward

universe u v w

/-- Reduction of heights modulo `m`, as a multiplicative homomorphism. -/
def heightMod (m : ℕ) : Multiplicative ℤ →* Multiplicative (ZMod m) :=
  AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod m))

theorem toAdd_heightMod (m : ℕ) (n : Multiplicative ℤ) :
    Multiplicative.toAdd (heightMod m n)
      = ((Multiplicative.toAdd n : ℤ) : ZMod m) := rfl

/-- A wreath product with finite lamps, finite acting group and finitely many
sites is finite. -/
theorem wreath_finite {A : Type u} [Group A] [Finite A] {G : Type w} [Group G]
    [Finite G] {X : Type v} [Finite X] [MulAction G X] :
    Finite (Wreath A G X) := by
  haveI : Finite (Lamp A X) := Subtype.finite
  refine Finite.of_injective (fun w : Wreath A G X => (w.left, w.right)) ?_
  intro w₁ w₂ hw
  simp only [Prod.mk.injEq] at hw
  exact SemidirectProduct.ext hw.1 hw.2

/-- **thm:notes-visible-quotient, residual finiteness of `P_K`, general form.**
Finite abelian lamps over sites with an injective equivariant height, acted on
by a residually finite group, give a residually finite wreath product. -/
theorem wreath_isResiduallyFinite_of_height {A : Type u} [CommGroup A] [Finite A]
    {G : Type w} [Group G] {X : Type v} [MulAction G X]
    (hG : IsResiduallyFinite G) (h : G →* Multiplicative ℤ)
    (ℓ : X → Multiplicative ℤ) (hℓ : Function.Injective ℓ)
    (hequiv : ∀ (g : G) (y : X), ℓ (g • y) = h g * ℓ y) :
    IsResiduallyFinite (Wreath A G X) := by
  classical
  refine le_antisymm ?_ bot_le
  intro w hw
  rw [Subgroup.mem_bot]
  have hright : w.right = 1 :=
    MonoidHom.mem_ker.mp (VisibleQuotient.finiteResidual_le_ker_of_residuallyFinite hG
      (SemidirectProduct.rightHom : Wreath A G X →* G) hw)
  have hpush : ∀ m : ℕ, 0 < m →
      push (K := A) (fun y => heightMod m (ℓ y)) w.left = 1 := by
    intro m hm
    haveI : NeZero m := ⟨hm.ne'⟩
    have hq : ∀ (g : G) (y : X), heightMod m (ℓ (g • y))
        = ((heightMod m).comp h) g • heightMod m (ℓ y) := by
      intro g y
      rw [hequiv, map_mul, smul_eq_mul, MonoidHom.comp_apply]
    haveI : Finite (Wreath A (Multiplicative (ZMod m)) (Multiplicative (ZMod m))) :=
      wreath_finite
    have hker := VisibleQuotient.finiteResidual_le_ker_of_finite
      (wreathMap (K := A) ((heightMod m).comp h) (fun y => heightMod m (ℓ y)) hq) hw
    exact congrArg SemidirectProduct.left (MonoidHom.mem_ker.mp hker)
  have hleft : w.left = 1 := by
    by_contra hne
    have hex : ∃ x₀, w.left.toFun x₀ ≠ 1 := by
      by_contra hall
      exact hne (Lamp.ext fun x => by
        by_contra hx
        exact hall ⟨x, hx⟩)
    obtain ⟨x₀, hx₀⟩ := hex
    obtain ⟨m, hmdef⟩ : ∃ m : ℕ, m = (∑ y ∈ supp w.left,
        Int.natAbs (Multiplicative.toAdd (ℓ x₀) - Multiplicative.toAdd (ℓ y))) + 1 :=
      ⟨_, rfl⟩
    have hm : 0 < m := by
      rw [hmdef]
      exact Nat.succ_pos _
    have hval : pushFun (K := A) (fun y => heightMod m (ℓ y)) w.left
        (heightMod m (ℓ x₀)) = 1 := by
      have h1 := congrArg
        (fun f : Lamp A (Multiplicative (ZMod m)) => f.toFun (heightMod m (ℓ x₀)))
        (hpush m hm)
      exact h1
    rw [pushFun, Finset.prod_eq_single_of_mem x₀ ?_ ?_] at hval
    · exact hx₀ hval
    · exact Finset.mem_filter.mpr ⟨mem_supp.mpr hx₀, rfl⟩
    · intro y hy hyx
      exfalso
      obtain ⟨hys, hqy⟩ := Finset.mem_filter.mp hy
      have hadd : Multiplicative.toAdd (heightMod m (ℓ y))
          = Multiplicative.toAdd (heightMod m (ℓ x₀)) :=
        congrArg Multiplicative.toAdd hqy
      rw [toAdd_heightMod, toAdd_heightMod, ZMod.intCast_eq_intCast_iff_dvd_sub] at hadd
      have hzero := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hadd (by
        rw [Int.natAbs_natCast, hmdef]
        exact Nat.lt_succ_of_le (Finset.single_le_sum
          (f := fun z => Int.natAbs (Multiplicative.toAdd (ℓ x₀) - Multiplicative.toAdd (ℓ z)))
          (fun _ _ => Nat.zero_le _) hys))
      rw [sub_eq_zero] at hzero
      exact hyx (hℓ (Multiplicative.toAdd.injective hzero.symm))
  exact SemidirectProduct.ext hleft hright

/-- **thm:notes-visible-quotient, residual finiteness of `P_K`.**  Take the
sites to be `G ⧸ ker h`, which is a copy of the image of the character `h`.
If `A` is finite abelian and `G` is residually finite, then
`A^{(G ⧸ ker h)} ⋊ G` is residually finite. -/
theorem wreath_quotient_isResiduallyFinite {A : Type u} [CommGroup A] [Finite A]
    {G : Type w} [Group G] (hG : IsResiduallyFinite G) (h : G →* Multiplicative ℤ) :
    IsResiduallyFinite (Wreath A G (G ⧸ h.ker)) :=
  wreath_isResiduallyFinite_of_height hG h (QuotientGroup.kerLift h)
    (QuotientGroup.kerLift_injective h) (by
      intro g y
      induction y using QuotientGroup.induction_on with
      | H z =>
        show h (g * z) = h g * h z
        exact map_mul h g z)

#audit_axioms toAdd_heightMod
#audit_axioms wreath_finite
#audit_axioms wreath_isResiduallyFinite_of_height
#audit_axioms wreath_quotient_isResiduallyFinite

end GroupApproximation.Full.NN04
