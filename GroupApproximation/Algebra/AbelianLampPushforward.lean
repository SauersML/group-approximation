import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Pushforward of abelian lamps along a map of sites, on `Finsupp`

The `Finsupp` model of the pushforward of **Section 37** of the ascending-HNN
dossier.  `Algebra/LampPushforward` carries the same construction for the
repository's general (possibly nonabelian) `Lamp K X`; this file is the
abelian-only model on `X →₀ A`, kept because the limit-kernel arithmetic of
`Algebra/AbelianLampTelescopeKernel` runs entirely on `Finsupp.mapDomain` and
needs nothing about wreath products.  Past the first
telescope stage the lamp group is abelian, and the map that collapses a stage
onto the next one is exactly the pushforward of finitely supported
configurations along the map of site sets: the value at a target site is the
product of the values over its fibre.

Written additively that is `Finsupp.mapDomain`, so the group-theoretic layer
costs almost nothing:

* `push q` is the pushforward as a monoid homomorphism of multiplicative lamp
  groups;
* `push_comp` is functoriality, from which the telescope kernels increase
  (`ker_le_ker_comp`) — the monotonicity Theorem 37.5 needs before taking the
  union;
* `push_comm_of_equivariant` is the statement that a pushforward along an
  equivariant map of site sets commutes with the coordinate permutations, which
  is what lets the whole tower be a tower of maps of *wreath products* and not
  merely of lamp groups.

The identification of the limit kernel with the union of the stage kernels is
the separate arithmetic step and is not proved here.
-/

namespace GroupApproximation

universe u v w

/-- The abelian lamp group over a site set, written multiplicatively. -/
abbrev AbLamp (A : Type u) [AddCommGroup A] (X : Type v) : Type (max u v) :=
  Multiplicative (X →₀ A)

namespace AbLamp

variable {A : Type u} [AddCommGroup A] {X : Type v} {Y : Type w}

/-- The pushforward of lamps along a map of site sets: the value at a target
site is the sum of the values over its fibre. -/
noncomputable def push (q : X → Y) : AbLamp A X →* AbLamp A Y :=
  AddMonoidHom.toMultiplicative
    { toFun := Finsupp.mapDomain q
      map_zero' := Finsupp.mapDomain_zero
      map_add' := fun _ _ => Finsupp.mapDomain_add }

@[simp] theorem toAdd_push (q : X → Y) (f : AbLamp A X) :
    Multiplicative.toAdd (push q f)
      = Finsupp.mapDomain q (Multiplicative.toAdd f) := rfl

/-- Pushing forward along the identity does nothing. -/
@[simp] theorem push_id : push (A := A) (id : X → X) = MonoidHom.id _ := by
  refine MonoidHom.ext fun f => ?_
  exact congrArg Multiplicative.ofAdd Finsupp.mapDomain_id

/-- **Functoriality.**  Collapsing two stages at once is collapsing them one
after the other. -/
theorem push_comp {Z : Type*} (q : X → Y) (r : Y → Z) :
    push (A := A) (r ∘ q) = (push r).comp (push q) := by
  refine MonoidHom.ext fun f => ?_
  exact congrArg Multiplicative.ofAdd Finsupp.mapDomain_comp

/-- **The telescope kernels increase.**  A configuration invisible at one stage
is invisible at every later stage. -/
theorem ker_le_ker_comp {Z : Type*} (q : X → Y) (r : Y → Z) :
    (push (A := A) q).ker ≤ (push (A := A) (r ∘ q)).ker := by
  intro f hf
  rw [MonoidHom.mem_ker] at hf ⊢
  rw [push_comp, MonoidHom.comp_apply, hf, map_one]

/-- **Equivariance.**  A pushforward along an equivariant map of site sets
commutes with the coordinate permutations, so the tower of lamp maps extends to
a tower of maps of wreath products. -/
theorem push_comm_of_equivariant (q : X → Y) (σ : X → X) (τ : Y → Y)
    (h : q ∘ σ = τ ∘ q) :
    (push (A := A) q).comp (push σ) = (push τ).comp (push q) := by
  rw [← push_comp, ← push_comp, h]

/-- A one-site lamp pushes forward to a one-site lamp. -/
@[simp] theorem push_single (q : X → Y) (x : X) (a : A) :
    push (A := A) q (Multiplicative.ofAdd (Finsupp.single x a))
      = Multiplicative.ofAdd (Finsupp.single (q x) a) :=
  congrArg Multiplicative.ofAdd (Finsupp.mapDomain_single)

/-- Two sites in the same fibre have their difference killed: this is the
generator of the stage kernel. -/
theorem push_single_mul_single_inv (q : X → Y) {x y : X} (hxy : q x = q y)
    (a : A) :
    push (A := A) q (Multiplicative.ofAdd (Finsupp.single x a) *
        (Multiplicative.ofAdd (Finsupp.single y a))⁻¹) = 1 := by
  rw [map_mul, map_inv, push_single, push_single, hxy]
  exact mul_inv_cancel _

end AbLamp

end GroupApproximation
